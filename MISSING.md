# Remaining verification

The selective-native branch uses one project and the existing verification
command. Its generated numerical declarations use `native_decide`; soundness,
geometry, and assembly retain their ordinary proofs. The whole theorem inherits
compiler trust, which must be reported explicitly. All inventoried source
changes still need production Lean replay; the successful native smoke tests
do not establish acceptance of these large certificates.

The additional 3,079 finite `soundDec` hypotheses in F00, Split, and Bundled/Own
now follow the same compiler-backed numerical policy. Their exact source
inverse is authenticated; no numerical values or theorem statements change.
Bounded compilation checks of the largest selected data initializers pass, but
neither those tests nor source audits establish completion or whole-build
runtime on the verification machine. Production replay remains necessary.

The preceding kernel-checking checkpoint's `ElevenSquare.Optimality` closure was **365,392 lines in 4,257 modules**, down from 394,204 lines / 6,326 modules. Those historical figures precede the indexed-table compilation helpers. The 300,000-line target remains unfinished. Read [PC_RESUME.md](PC_RESUME.md) first.

The active certificate-data pass removes **34,739,375 bytes** (zero weight tails and unused collision cores) with the original checker. Its source inverse audit and S135 fixture pass; all 459 transformed stages still need the full replay. The separately proved determinant checker remains an inactive pilot. Its repeated S135 test is about 30% faster in median CPU time, which is not a whole-build result. The next rollout must validate support pairs and preserve literal fallback for degenerate pairs; see [the data report](simplification/T07_DATA_PROFILE_20261003.md).

**The complete assembled theorem remains unverified.** The selected S0/S1 replay was stopped cleanly because of low disk space and heavy swapping. Dependencies through `S1D` passed; `S0` was not accepted and `S1` was not attempted. The full `ElevenSquare.Verification` target has not been run on this checkpoint. Source audits pass, but no complete merged-stage kernel acceptance is claimed. Do not resume the full history replay on this Mac; use the larger computer. Later bounded fixture checks do not replace that replay.

Run the final target and public axiom audit with:

```sh
python3 scripts/verify.py --jobs 1
```

Resolve any failures without weakening the geometric statements. Require
`OPTIMALITY_PROVED_WITH_NATIVE_CERTIFICATES`, zero admissions, the standard
axioms, and only native axioms owned by the exact inventoried numerical
declarations. The result must disclose `lean_kernel_and_native_compiler` trust.
The optional `--all` plus finalizer audit covers the entire retained repository;
it is broader than the final theorem and does not benefit from the 2,032 removed
module startups.

The compact T07 witness pilot was removed from the active proof after an S135 scout measured 54.126 CPU seconds for original literals versus 132.407 for compact recipes. These are single observations, not a general speed ratio. Its old acceptance receipt is historical experimental evidence. All four conditions in the S135 pruning benchmark fixtures passed Lean. The LCM helper also passed Lean, but its runtime comparison was not run and the prototype is not enabled. Neither result certifies a complete production stage, and no 2–3 hour full-build estimate is established. Preserve the packing definitions, public statements, strict ownership and closed touching/split semantics.
