const assert = require('node:assert/strict');
const {policy, SLOT_LIMIT, LEAF_SLOT_LIMIT, OTHER_LIMIT} = require('./ci_cache.cjs');
const ref = 'refs/heads/integration';
const item = (slot, bytes = slot === 16 ? SLOT_LIMIT : LEAF_SLOT_LIMIT) => ({id: slot, key: `wand125-replay-v1-s${String(slot).padStart(2,'0')}-${'1'.repeat(64)}-123-1`, ref, size_in_bytes: bytes});
assert.equal(policy([], 0, ref).owned, 0);
const seventeen = Array.from({length: 17}, (_, i) => item(i));
assert.equal(policy(seventeen, 8*1024**3, ref).owned, 8*1024**3);
assert.throws(() => policy([item(0), item(0)], SLOT_LIMIT, ref), /Duplicate/);
assert.throws(() => policy([item(0, SLOT_LIMIT+1)], SLOT_LIMIT+1, ref), /oversized/);
assert.throws(() => policy([{...item(0), ref:'refs/heads/other'}], SLOT_LIMIT, ref), /namespace\/ref/);
assert.throws(() => policy([{key:'unrelated',size_in_bytes:OTHER_LIMIT+1}], 0, ref), /headroom/);
assert.throws(() => policy([], OTHER_LIMIT+1, ref), /headroom/);
assert.throws(() => policy([], undefined, ref), /Unknown/);
console.log('8 cache policy regressions passed');

const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const {main, generation} = require('./ci_cache.cjs');
(async () => {
  const previousCwd = process.cwd();
  const temporary = fs.mkdtempSync(path.join(os.tmpdir(), 'ci-cache-test-'));
  process.chdir(temporary);
  try {
    fs.mkdirSync('.verification/ci-cache', {recursive:true});
    for (const file of ['.verification/ci-plan.json', 'lean-toolchain', 'lakefile.lean', 'lake-manifest.json'])
      fs.writeFileSync(file, 'fixture');
    const entry = item(0, 100);
    entry.key = entry.key.replace('1'.repeat(64), generation());
    const events = [];
    let cachePages = [[]], reportedUsage = 0;
    const api = {
      context: {repo: {owner:'test',repo:'public'}, ref, runId:456},
      core: {info() {}, warning() {}},
      github: {
        // Match Octokit's normalized page shape, including its optional mapper.
        // The old actions_caches mapper produces undefined for these pages.
        async paginate(route, params, mapper) {
          return cachePages.flatMap(data => mapper ? mapper({data}) : data);
        },
        async request(route) {
          if (route.endsWith('/actions/cache/usage')) return {data:{active_caches_size_in_bytes:reportedUsage}};
          if (route.startsWith('DELETE ')) { events.push('delete'); return {}; }
          return {data:{private:false}};
        }
      },
      cache: {
        async restoreCache(paths, key) { fs.writeFileSync(paths[0], 'checkpoint'); return key; },
        async saveCache() { events.push('save'); return 99; }
      }
    };
    await main(api, 'guard'); // Empty normalized collection, as in the first CI run.
    cachePages = [[], [entry]]; reportedUsage = 100;
    await main(api, 'guard'); // Flatten all normalized pages, including empty ones.
    console.log('2 normalized pagination regressions passed');
    fs.writeFileSync('.verification/ci-cache/shard-00.tar.gz','checkpoint');
    await assert.rejects(() => main(api, 'save', 0), /unrestored/);
    assert.deepEqual(events, []);
    await main(api, 'restore', 0);
    process.env.GITHUB_RUN_ATTEMPT = '1';
    await main(api, 'save', 0);
    assert.deepEqual(events, ['delete','save']);
    events.length = 0;
    fs.truncateSync('.verification/ci-cache/shard-00.tar.gz', 449*1024**2);
    await assert.rejects(() => main(api, 'save', 0), /Payload too large/);
    assert.deepEqual(events, []);
    const compatible = generation();
    fs.writeFileSync('.verification/ci-plan.json', 'changed source/frontier plan');
    assert.equal(generation(), compatible);
    fs.writeFileSync('lean-toolchain', 'different compiler');
    await main(api, 'restore', 0);
    assert.equal(fs.existsSync('.verification/ci-cache/shard-00.tar.gz'), false);
    assert.deepEqual(events, []);
    console.log('5 cache replacement/generation regressions passed');
  } finally {
    process.chdir(previousCwd);
    fs.rmSync(temporary, {recursive:true,force:true});
  }
})().catch(error => { console.error(error); process.exitCode = 1; });
