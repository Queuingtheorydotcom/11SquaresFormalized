# Generator for U2 (prior; also usable for generic and returned)

Excludes a canonical case by the owned-hull induction with box trees (`U2P/Rules.lean`:
`owned_all_of_tris`, `excluded_of_tris`).  Pure Python (standard library only); the sites are read
from `lean/Sqpack/S11Opt/Cells.lean`, no file of the author is needed.

```sh
python3 gen_u2p.py CASE OUTDIR [PREFIX]           # one case; CASE is the index of `maskAt`
U2P_PREFIX=U2P python3 batch.py JOBS OUTDIR CASES  # many cases in parallel, OUTDIR/summary.jsonl
```

Output `OUTDIR/C<case>/`: `Data.lean` (cells, owned hulls, triangle options), `S<k>.lean` (the box
tree of step `k`, chunks of at most 1,500 leaves), `Main.lean` (the chain of promotions and the
terminal step; `theorem excluded : CaseExcluded (maskAt CASE)`).  Modules are
`Sqpack.S11Opt.Split.<PREFIX>.C<case>.*`.

* Owner step: angle rows by U-splits (32), then X/Y splits; leaves wall / cell / dead (a lattice
  point of a fan triangle of another owner's hull, weights over `bm = 65536`, lies in every square
  of the box) / alive.  The new owned hull is the intersection of the ptOk regions (12 half-planes
  per leaf) of the alive leaves; the alive leaves that bind it are refined one level at a time.
* Round-robin over the owners until one owner has no alive leaf (terminal); only the steps the
  terminal step depends on are emitted.
* `check_case.sh`, `watch_check.sh`: the Lean check of generated cases on a build machine.
* `branch.py`: when the induction stops growing, split the centre of one owner by an axis-parallel
  grid half-plane and solve both halves (`U2P/Branch.lean`).
* `regen.py MANIFEST OUTDIR [JOBS]`: regenerate the cases of a MANIFEST and compare the sha256 of
  every file; the per-case settings are header lines of the MANIFEST.
* `make_tars.sh`: reproducible per-case archives `n11-u2p-C<4 digits>.tar.xz`.

Settings (environment variables, all default to the plain generator):

| variable | meaning | default |
|---|---|---|
| `U2P_KMAX` | at most this many targets per step (0: no limit) | 16 |
| `U2P_PROFILE` | step refinement: `default` or `fine` (finer boxes and angles, 200 refinements) | default |
| `U2P_CHUNK` | leaves per Lean theorem (smaller: less kernel memory) | 1500 |
| `U2P_PART` | branch.py: leaf theorems per file (0: one file per step) | 0 |
| `U2P_FIRST_SPLIT` | branch.py: forced first split `owner,A,B,C` | none |

PyPy (`pypy3`) runs the generator about 12 times faster than CPython, with byte-identical output.
Many targets (`U2P_KMAX=0`) make the kernel check heavy in memory (up to 30 GB per Lean process
with 1,500-leaf theorems); use `U2P_CHUNK=300 U2P_PART=40` for such cases.

## The 76 prior cases (`U2Prior.lean`)

The generated files are not committed.  `MANIFEST_U2P.sha256` holds the sha256 of every `.lean`
file of the 76 cases that the kernel checked (3,380 files) and, as header lines, the settings of
the cases that need non-default ones (`regen.py` reads them).  The per-case archives
`n11-u2p-C<4 digits>.tar.xz` (`make_tars.sh`, 475 MB in all) are release assets with
`SHA256SUMS_U2P` as their `SHA256SUMS`; `make_manifest.sh` wrote the MANIFEST on the build machine.

```sh
python3 scripts/fetch_wand125_data.py --unit U2P --manifest scripts/u2p/MANIFEST_U2P.sha256 --root lean
python3 scripts/u2p/regen.py scripts/u2p/MANIFEST_U2P.sha256 OUTDIR JOBS [CASE ...]   # or regenerate
```

`fetch_wand125_data.py` checks each archive against `SHA256SUMS`, extracts it to a temporary
directory, checks the files against the MANIFEST and only then puts the case in place.  Cases 655,
1839 (`branch.py`, depth 3), 761 (depth 5, `fine`) and 1383 (depth 5, `fine`, no target limit,
`U2P_CHUNK=300 U2P_PART=40`, 658 part files) take hours; the others minutes.  Kernel check of all
76 on a 16-vCPU machine: about 18 h wall in total (1383 alone 1.7 h at 10 parallel builds).
`prior_excluded` depends on the axioms `propext`, `Classical.choice`, `Quot.sound` only.
