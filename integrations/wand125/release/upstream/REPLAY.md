# Independent re-run of the author's verifier

*Summary of a run made on 2026-09-29 and reviewed by the person who ran it.*

**What was run.** The author's own verifier, `VERIFY.py` in
[Queuingtheorydotcom/11SquaresOptimal](https://github.com/Queuingtheorydotcom/11SquaresOptimal),
on commit `f9e0de713a0949d1bc6a0fa6b59d96edf6c3d65c`. It was run without
modifying the repository and without reusing saved geometry.

**Environment.**
- Machine: M1 Mac mini (macOS, arm64, 8 cores).
- Python 3.12.2, in a fresh virtual environment with the pinned versions:
  gmpy2 2.3.1, sympy 1.14.0, numpy 2.5.3, scipy 1.18.1.
- The repository was cloned with Git LFS (2,638 objects).

**Before running.**
- We read the code first. None of the 978 Python sources opens a network
  connection.
- `RUN_ALL.py` runs 23 stages in order, stops at the first failure, and writes
  only inside `work/`.

## Results

`VERIFY.py --check-package` passed in 211 s. It checks the integrity of the
package (2,646 objects, 2,524 files, 978 sources); it is not a check of the proof.

Full run (run-history `20260929T033336734131Z`), without
`--resume-after-stage4`. Stages 1–4 were also recomputed:

| stage | result | seconds | notes |
|---|---|---:|---|
| 1 original-package-check | PASS | 7 | |
| 2 baseline-full-geometry | PASS | 2,209 | 1,931 exclusions: 59 field and 34 generic certificates |
| 3 prior-76-full-geometry | **FAIL** | ≈ 69 | first case (mask 1000, `direct_v9`): `Fresh mathematical field differs: final_state_sha256`; see below |
| 4 returned-173-full-geometry | PASS | 4,134 | all 173 cases `PASS_FRESH_INDEPENDENT_RETURNED_CASE` |
| 6 symmetry | PASS | 1 | D4 bridge, conditional on stage 5 (the union of exclusions); cases 999, 1462, 1659 UNSAT by finite search (75, 61, 31 nodes) |
| 7 candidate-construction | PASS | 0 | |
| 8 candidate-cover | PASS | 0 | 16 cell hulls rebuilt exactly, total area 2; 4,368 eleven-cell masks, 2,184 canonical |
| 9 candidate-local-algebra | PASS | 13 | |
| 10 candidate-local-baseline | PASS | 15 | |
| 11 candidate-local-weighted | PASS | 6 | |
| 12 candidate-focused | PASS | 6 | |
| 13 candidate-feature-bridge | PASS | 3 | |
| 14 candidate-root-geometry | PASS | 525 | |
| 15 candidate-far15-geometry | **FAIL** | 556 | 12 of the 13 compared fields agree; only `final_state_sha256` differs |
| 16 candidate-far13-geometry | **FAIL** | 801 | as stage 15; `branch_exclusion_proved = true` agrees with the receipt |
| 17 candidate-far2-geometry | **FAIL** | 895 | as stage 15; `branch_exclusion_proved = true` agrees with the receipt |
| 18 candidate-near-geometry | **FAIL** | 1,202 | `Portable geometry differs at final_state_sha256` |
| 19 candidate-composition | **FAIL** | 2 | `Final pose state drift`: `audit_complete_capture438.py` compares the receipts' `final_state_sha256` with `digest(final_state)` of the published leaves; same cause |
| 20 candidate-consumer-tests | **FAIL** | 2 | same `Final pose state drift` |
| 5, 21–23 | not run | | they need the result of stage 3 |

**Summary.** Passed: stages 1, 2, 4 and 6–14 (13 stages). Failed: 3 and 15–20.
Not run: 5 and 21–23.

Stages 4 and 6–20 were run one by one with the same commands as `RUN_ALL.py`,
since `RUN_ALL.py` stops at stage 3.

## Why stages 3 and 15–20 fail: the published receipts, not the geometry

- `audit_capture_v9.py` recomputes
  `final_state_sha256 = sha256(canon(final_state))` from the input file and
  compares it with the saved receipt.
- For publication, private paths in the inputs were rewritten to
  `/workspace/eleven-square/…` (PUBLICATION.md). The `final_state` of the inputs
  contains such path strings.
- The saved receipts still carry the hash of the content *before* the rewrite.
  For mask 1000, the published input gives `ed26647a82af…` (our recomputation
  agrees), while the receipt says `9d5b8c669fb4…`.
- The mathematical fields compared (`source_sha256`, `constraints`, `bootstrap`,
  `seed`) agree. The `nodes` field differs only in path strings.
- Read-only, we checked all 76 stage-3 cases. In all 75 comparable cases the
  receipt hash does not match the published input:
  - in 74 of them, `final_state` contains a rewritten path;
  - in the remaining one (mask 1839), an embedded seed-file hash was
    re-assigned at publication.
- The inputs of the four candidate branches (far15, far13, far2, near) each
  contain rewritten paths in two places. Stages 15–18 therefore stop at the
  same comparison after finishing the geometry, and stages 19–20 at the
  corresponding digest comparison.

**Conclusion.** Every failure has the same cause, the publication rewrite:
path strings were replaced and embedded file hashes re-assigned, so the
`final_state` of the published inputs changed, while the receipts'
`final_state_sha256` kept the values from before the rewrite. No discrepancy
was found in any compared mathematical field (`source`, `root`, `mask`,
`constraints`, `branch_exclusion_proved`, …). The private versions of
`final_state` are not available, so the comparison can only go as far as the
fields recorded in the receipts. As published, `VERIFY.py` cannot pass stage 3.
This is consistent with PUBLICATION.md, which states that a full re-run of the
published version has not been done.

**Possible repairs** (on the author's side; not done here). Either recompute the
receipts' `final_state_sha256` from the published inputs, or canonicalize the
paths before hashing. The stages that were not run (5, 21–23) could then be
run.
