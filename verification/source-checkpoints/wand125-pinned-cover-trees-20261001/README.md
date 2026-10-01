# Accepted cover and tree modules: standalone exact source snapshot

The supplied original checker on Lean 4.10.0-rc2 accepted four exact targets:

| Actual targets | Audit seconds |
| --- | ---: |
| `SquarePacking.PTree.nodup_of_chainB`, `SquarePacking.d4_reduction` | 34.46 |
| `SquarePacking.BoxTree.ptOk_mem` | 31.30 |
| `SquarePacking.S11Opt.FieldTree.soundDec` | 33.62 |

Each reports only `propext`, `Classical.choice` and `Quot.sound`. All nine
reachable Lean modules (184,928 source bytes), the pinned Lake environment,
unchanged supplied checker scripts and three exact task files are frozen here
from those accepted transports. The reused core originated in
[wand125/n11-optimality-lean](https://github.com/wand125/n11-optimality-lean).
Every exact source member and closure key is listed in `SOURCE_BINDINGS.json`.

Keep this standalone snapshot separate from the stronger merged repository
interfaces. Later canonical adaptations, unaccepted `Majority` and shared-checker
files are excluded. No imported case is accepted: the total stays 159/173.
Concrete case obligations, the complete exclusion checker, imported full case
audits, public family targets and final return remain pending.

Source, task, environment and checker bytes are unchanged. Only private handoff
metadata is omitted and the resource profile is replaced with a neutral serial
profile. No original handoff archive, compiler objects, receipts or caches are
distributed. Root independently source-bound the genuine compiled objects and
receipts; publication verified immutable transport member/source-closure keys
and the exact audit/CHECK/wrapper/execution bytes without running Lean.

For a fresh standalone replay, install the pinned toolchain, prepare the pinned
mathlib dependencies/cache, then run these commands sequentially from this
snapshot directory:

```sh
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-cover-compatibility-task.json
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-box-tree-compatibility-task.json
python project/scripts/check_handoff.py --task library-case1849-node993-wand125-field-tree-compatibility-task.json
```

Publication does not claim a fresh standalone or merged repository Lean replay.
