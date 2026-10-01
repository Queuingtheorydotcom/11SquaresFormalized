/* Fixed-budget Actions cache slots. Used from a pinned github-script action.
 * Only this workflow's 16 leaf slots plus join may be replaced; unrelated caches/settings are
 * never changed. API uncertainty fails closed. No artifact uploads are used.
 */
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const PREFIX = 'wand125-replay-v1';
const SHARDS = 16;
const SLOT_LIMIT = 512 * 1024 ** 2;
const PAYLOAD_LIMIT = 480 * 1024 ** 2;
const LEAF_SLOT_LIMIT = 480 * 1024 ** 2;
const LEAF_PAYLOAD_LIMIT = 448 * 1024 ** 2;
const OTHER_LIMIT = 1 * 1024 ** 3;
const TOTAL_LIMIT = 10 * 1024 ** 3;
const ownedPattern = /^wand125-replay-v1-s(\d{2})-([0-9a-f]{64})-\d+-\d+$/;

function generation() {
  const hash = crypto.createHash('sha256');
  for (const file of ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json'])
    hash.update(fs.readFileSync(file));
  return hash.digest('hex');
}

function policy(caches, usage, ref) {
  if (!Number.isSafeInteger(usage) || usage < 0) throw new Error('Unknown cache usage');
  const slots = new Map();
  let owned = 0, other = 0;
  for (const entry of caches) {
    if (!Number.isSafeInteger(entry.size_in_bytes) || entry.size_in_bytes < 0)
      throw new Error('Unknown cache size');
    if (!entry.key.startsWith(PREFIX)) { other += entry.size_in_bytes; continue; }
    const match = ownedPattern.exec(entry.key);
    if (!match || Number(match[1]) > SHARDS || entry.ref !== ref)
      throw new Error('Owned cache namespace/ref differs; review before launching');
    const slot = Number(match[1]);
    if (slots.has(slot) || entry.size_in_bytes > (slot === SHARDS ? SLOT_LIMIT : LEAF_SLOT_LIMIT))
      throw new Error('Duplicate/oversized owned cache slot');
    slots.set(slot, entry); owned += entry.size_in_bytes;
  }
  // The usage endpoint may lag; use both it and the paginated cache inventory.
  if (other > OTHER_LIMIT || usage - owned > OTHER_LIMIT || usage > TOTAL_LIMIT)
    throw new Error('Cache headroom is insufficient or uncertain; do not launch/save');
  if (owned > SHARDS * LEAF_SLOT_LIMIT + SLOT_LIMIT) throw new Error('Owned caches exceed 8 GiB');
  return {slots, owned, other, usage};
}

async function inventory(github, context) {
  const params = {owner: context.repo.owner, repo: context.repo.repo};
  const repository = await github.request('GET /repos/{owner}/{repo}', params);
  if (repository.data.private !== false) throw new Error('Public repositories only');
  const caches = await github.paginate('GET /repos/{owner}/{repo}/actions/caches',
    {...params, per_page: 100}, response => response.data.actions_caches);
  const response = await github.request('GET /repos/{owner}/{repo}/actions/cache/usage', params);
  return policy(caches, response.data.active_caches_size_in_bytes, context.ref);
}

function payload(slot) { return `.verification/ci-cache/shard-${String(slot).padStart(2, '0')}.tar.gz`; }
function stateFile(slot) { return `.verification/ci-restored-${slot}.json`; }

async function restoreOne(api, slot, state) {
  const {cache, core} = api;
  const entry = state.slots.get(slot);
  fs.mkdirSync(path.dirname(payload(slot)), {recursive: true});
  if (!entry) { core.info(`No checkpoint for shard ${slot}`); return; }
  const hit = await cache.restoreCache([payload(slot)], entry.key, []);
  if (hit !== entry.key || !fs.existsSync(payload(slot)))
    throw new Error(`Checkpoint restore failed for shard ${slot}; retaining its previous cache`);
  if (fs.lstatSync(payload(slot)).isSymbolicLink() || fs.statSync(payload(slot)).size > PAYLOAD_LIMIT)
    throw new Error('Restored payload exceeds the accepted bound');
  fs.writeFileSync(stateFile(slot), JSON.stringify({id: entry.id, key: entry.key}));
  if (ownedPattern.exec(entry.key)[2] !== generation()) {
    fs.unlinkSync(payload(slot));
    core.info(`Shard ${slot} belongs to an older toolchain/configuration; rebuilding it safely`);
  }
}

async function main(api, mode, slot) {
  const {github, context, core, cache} = api;
  const state = await inventory(github, context);
  core.info(`Cache preflight: owned=${state.owned}, unrelated=${state.other}, reported=${state.usage} bytes`);
  if (mode === 'guard') return;
  if (mode === 'restore-all') {
    for (let i = 0; i <= SHARDS; i++) await restoreOne(api, i, state);
    return;
  }
  if (!Number.isInteger(slot) || slot < 0 || slot > SHARDS) throw new Error('Invalid shard');
  if (mode === 'restore') return restoreOne(api, slot, state);
  if (mode !== 'save') throw new Error('Invalid cache mode');
  const file = payload(slot);
  if (!fs.existsSync(file)) { core.warning('No bounded checkpoint to save; prior cache retained'); return; }
  if (fs.lstatSync(file).isSymbolicLink() || fs.statSync(file).size > (slot === SHARDS ? PAYLOAD_LIMIT : LEAF_PAYLOAD_LIMIT))
    throw new Error('Payload too large: never upload an oversized cache');
  const previous = state.slots.get(slot);
  if (previous) {
    if (!fs.existsSync(stateFile(slot))) throw new Error('Refusing to replace an unrestored cache');
    const restored = JSON.parse(fs.readFileSync(stateFile(slot), 'utf8'));
    if (restored.id !== previous.id || restored.key !== previous.key)
      throw new Error('Cache slot changed concurrently; refusing replacement');
    await github.request('DELETE /repos/{owner}/{repo}/actions/caches/{cache_id}',
      {...context.repo, cache_id: previous.id});
  }
  // One fixed slot per shard and workflow-wide concurrency bound aggregate new
  // storage even when all 16 leaf jobs save together. Unrelated usage was checked above.
  const key = `${PREFIX}-s${String(slot).padStart(2, '0')}-${generation()}-${context.runId}-${process.env.GITHUB_RUN_ATTEMPT}`;
  const id = await cache.saveCache([file], key);
  if (!Number.isInteger(id) || id < 0) throw new Error('Checkpoint upload failed; rerun to rebuild/resume');
  core.info(`Saved checkpoint ${slot} within its fixed cache slot`);
}

module.exports = {main, policy, generation, PAYLOAD_LIMIT, SLOT_LIMIT, LEAF_SLOT_LIMIT, OTHER_LIMIT};
