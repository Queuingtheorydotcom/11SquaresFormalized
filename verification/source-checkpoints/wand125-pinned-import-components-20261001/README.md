# Audited import components: deduplicated exact source snapshot

Upstream supplied 172 case-proof archives; case1465 is its sole missing case.
The legacy 159/173 count records full certificate audits into the original
project and is a separate metric from that supplied proof inventory.

This snapshot contains the exact accepted source closure of these original
Lean 4.10.0-rc2 checker audits:

| Component | Actual targets | Audit seconds |
| --- | --- | ---: |
| Branch | `SquarePacking.S11Opt.Split.U2P.not_in_of_excl`, `split_excl` | 30.81 |
| First tree2051 | `SquarePacking.S11Opt.Split.U2R.C2051.cov0` | 41.74 |
| First tree1849 | `SquarePacking.S11Opt.Split.U2R.C1849.cov0` | 34.65 |
| Correspondence2051 | `ElevenSquare.Pending.T03.Wand125.Case2051.bounds`, `mask_eq` | 38.01 |
| Correspondence1849 | `ElevenSquare.Pending.T03.Wand125.Case1849.bounds`, `mask_eq` | 38.55 |

Both bounds targets use no axioms; the other six use only `propext`,
`Classical.choice` and `Quot.sound`. These are component audits, not complete
imported case certificates. Original-project full audits remain159/173 at this
checkpoint, with zero new full imported case audits. Full-case integration,
original public family targets and final return are still pending.

All 663 reachable source modules (13,680,277 bytes) occur only once here. Each of
the five unchanged tasks has its entire exact dependency closure. Shared source
versions agree across the five immutable accepted transports. The original
initialization closures of the two correspondence audits have639 and656 modules.
Source/task/environment/checker bytes remain unchanged, isolated from stronger
merged repository interfaces and later canonical edits. Only private handoff
metadata is omitted and the resource profile is neutralized. No build objects,
receipts, caches or private paths are distributed.

The imported core originated in
[wand125/n11-optimality-lean](https://github.com/wand125/n11-optimality-lean).
Exact source, closure and original transport hashes are in `SOURCE_BINDINGS.json`.
Root independently checked source-bound genuine compiled objects/receipts;
publication verified every immutable member and actual audit/CHECK/wrapper/
execution hash without running Lean.

For fresh standalone replay, install the pinned toolchain, prepare its pinned
mathlib dependencies/cache, then run sequentially from this snapshot directory:

```sh
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-branch-compatibility-task.json
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-case2051-s0-compatibility-retry01-task.json
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-case1849-s0-compatibility-retry02-task.json
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-case2051-correspondence-compatibility-retry02-task.json
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-case1849-correspondence-compatibility-retry05-task.json
```

No fresh standalone or merged repository compiler replay is claimed by publication.
