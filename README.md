# Eleven-square simplification: unverified checkpoint

This branch is **one Lean project with selective native numerical checks**.
Run `python3 scripts/verify.py --jobs 1` as before. Generated tree-coverage and
T07 certificate arithmetic use `native_decide`; geometry, checker soundness,
ownership soundness, and proof assembly retain their ordinary Lean proofs. The public
theorem inherits trust in Lean's compiler from the numerical results. This is
not a kernel-only verification claim, and no new `sorry` is introduced.

There are **10,464 inventoried numerical declarations in 1,839 tracked files**.
The exact sources and declaration names are recorded in
`verification/native-certificates.json`; source hashes prevent native evaluation
from silently spreading to other proofs. The original certificate values and
theorem statements are unchanged. Eleven finite field-data modules also enable
code generation for 119 existing `atomN`, `atoms`, and `optsN` definitions;
only their unnecessary `noncomputable` modifiers are removed. The exact original
and executable source hashes are recorded in
`verification/native-data-compatibility.json`. The baseline generator applies the same
policy when restoring derived coverage bundles.

This includes the 3,079 previously kernel-evaluated `soundDec` numerical
hypotheses in `F00`, `Split/U2G`, `Split/U2P`, `Split/U2R`, and `Bundled/Own`.
Only the finite certificate check passed to the existing soundness theorem
changes to `native_decide`; certificate values, theorem statements, and the
soundness theorem applications are byte-for-byte preserved. The source audit
checks the exact inverse against each recorded `kernel_sha256`, including when
the inventory changes during a resumed build. Historical simplification audits
authenticate that inverse before checking their original source hashes.

Oversized indexed triangle tables compile their existing stage literals in
separate private definitions before assembling the same array. This avoids
compiler recursion limits without changing the numerical witnesses, stage order,
or public lookup functions. `python3 scripts/split_indexed_data.py --check`
authenticates the exact inverse against the original indexed-stage source receipt;
the normal source audit also performs this check. Full Lean replay remains required.
Bounded isolated Lean 4.34.1 checks passed for the complete split C1311 data and
the large Root240 `S3C.pc2`, `S0C.pc10`, and `S5C.rs` initializers, with code
generation enabled and the existing recursion limit. These checks use the exact
data declarations and matching finite types; they do not replay the geometry,
and the C1311 check omits `.olean` serialization.

The verifier now prints `checking MODULE` before starting each module; `cached`
and `accepted` report completed work. Existing unchanged receipts can be reused.
A successful final replay with numerical native evaluation reports
`OPTIMALITY_PROVED_WITH_NATIVE_CERTIFICATES`, zero admissions, and the actual
native axiom dependencies. Full proof replay and whole-build timing remain
unverified on this branch. Focused infrastructure tests and a Lean 4.34.1
native-check/ordinary-composition smoke test pass; the smoke test is not a replay
of the large production certificates.
The `F50.Leaves023` numerical obligation also passes in an isolated Lean 4.34.1
reproduction using the unchanged numerical checker and corrected field data;
the same test with the original data reproduces the `noncomputable opts5` error.
This focused check does not replace the full module and proof replay.
Additional isolated native checks pass for the 205,628-digit C1311 `cov4_3`
certificate and the 211,408-digit bundled ownership certificate
`t_o6_10045414353_7258430193_1`. Both use unchanged finite checker definitions
and exact numerical inputs at the production proof recursion limit of 512;
the C1311 test at that limit uses only the selected stage's data. Geometry and
the assembled theorem still require the production replay.

On the larger verification machine, `bash scripts/run_verification.sh --jobs 1`
wraps the complete `verify.py --all` replay and final axiom audit, preserving
the compiler trust report and resumable module receipts. Adjust `--jobs` for the
available hardware; modules still compile serially. On Linux, `--bootstrap`
prepares the pinned toolchain and dependency cache. The runner reports bounded
compiler diagnostics for the failing module and keeps full logs under
`.verification/`. Completed modules are not blamed for later audit failures.
This branch does not configure or start a hosted verification workflow.

The size figures and performance measurements below describe the preceding
kernel-checking checkpoint; its source-hash manifests are historical evidence.
The native inventory records the new hashes and exact inverse hashes.

The `ElevenSquare.Optimality` source closure contains **365,392 physical Lean lines in 4,257 local modules**, including all reached certificate data. Compared with the prior 394,204-line / 6,326-module checkpoint, this removes **28,812 lines and 2,069 reachable modules**. The 300,000-line target has not been reached.

**The complete assembled theorem remains unverified; the full verification target has not been run on this checkpoint.** Source-preserving module bundling removes 2,032 module launches from a cold theorem replay. The slower compact-witness experiment was excluded; active T07 certificates retain their original literal data. No complete-build runtime is established.

Certificate-data trimming now removes **34,739,375 bytes** across 459 T07 stages: **5,964,331 trailing zero weights** and **20,152 unused collision-core lists**. The active source closure is **1,051,109,682 bytes**. The production checker is unchanged. Exact inverse audits and the frozen 38-row pruning fixture pass; the entire transformed corpus has not been replayed through Lean.

An optional determinant checker has kernel-checked soundness proofs. In two mirrored S135 trials, combining it with unused-core removal reduced median CPU time from **51.78 to 36.31 seconds** (about **30%**) and reduced the standalone input source by about **46%**. This checker remains an inactive pilot; the figures do not establish a full-build speedup or the 2–3 hour target. See [the certificate-data report](simplification/T07_DATA_PROFILE_20261003.md).

The selected S0/S1 replay was stopped cleanly because of low disk space and heavy swapping. Dependencies through `S1D` passed, but `S0` was not accepted and `S1` was not attempted. Source audits pass; no complete merged-stage kernel acceptance is claimed. Full Lean verification should run on the larger computer; the later certificate experiments used bounded, isolated fixtures.

The main verification command is `python3 scripts/verify.py --jobs 1`. It checks `ElevenSquare.Verification`, its dependencies and the public axiom audit. The optional `--all` audit also checks retained historical and compatibility modules and does not gain the module-startup reduction.

Read [PC_RESUME.md](PC_RESUME.md) for the branch and verification steps, and [simplification/REVIEW_317.md](simplification/REVIEW_317.md) for the reductions. [SIMPLIFICATION_HANDOFF.md](SIMPLIFICATION_HANDOFF.md) preserves the earlier imported 494,346-line checkpoint's history; its old build-status notes are superseded by the current handoff.
