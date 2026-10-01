# Accepted shared exclusion checker: standalone frozen source snapshot

The supplied original checker on Lean 4.10.0-rc2 accepted five exact targets:

| Actual targets | Audit seconds |
| --- | ---: |
| `SquarePacking.S11Opt.majority_capacity` | 27.72 |
| `SquarePacking.S11Opt.bridge`, `triGroupOk_mem`, `majority_capacity_idx` | 25.72 |
| `SquarePacking.S11Opt.Split.U2P.excluded_of_tris` | 28.08 |

Every target reports only `propext`, `Classical.choice` and `Quot.sound`. This
completes the ordinary shared exclusion-checker compatibility audit on the
original compiler. All 17 reachable Lean modules (444,539 source bytes), the
pinned Lake environment, supplied checker scripts and three exact task files
are frozen at their accepted source transport bytes. The reused core originated
in [wand125/n11-optimality-lean](https://github.com/wand125/n11-optimality-lean).
Every unchanged member and source-closure key is in `SOURCE_BINDINGS.json`.

The checker soundness theorem is generic: it does not prove a particular case's
finite tables or correspondence to the original case mask. Unaudited `Branch`
and individual case sources are excluded. No imported case is accepted; the
count stays 159/173. Actual finite case probes, complete imported case audits,
original public family targets and final return remain pending.

Keep this snapshot separate from stronger merged repository interfaces and later
canonical adaptations. All source/task/environment/checker bytes are unchanged.
Only private handoff metadata is omitted and the resource profile is neutralized.
No original handoff archive, compiler objects, receipts or caches are published.
Root independently source-bound the genuine objects/receipts; publication checked
every immutable transport member, source-closure key and exact recorded
audit/CHECK/wrapper/execution hash without running another compiler.

For a fresh standalone replay, install the pinned toolchain, prepare its pinned
mathlib dependencies/cache, and run sequentially from this snapshot directory:

```sh
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-majority-compatibility-retry02-task.json
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-field-bridge-compatibility-retry01-task.json
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-shared-checker-compatibility-retry16-task.json
```

No fresh standalone or merged repository Lean replay is claimed by publication.
