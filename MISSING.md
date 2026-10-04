# Remaining verification

Current `ElevenSquare.Optimality` closure: **365,392 lines in 4,257 modules**, down from 394,204 lines / 6,326 modules. The census and manifest are refreshed. The 300,000-line target remains unfinished. Read [PC_RESUME.md](PC_RESUME.md) first.

**The complete assembled theorem remains unverified.** The selected S0/S1 replay was stopped cleanly because of low disk space and heavy swapping. Dependencies through `S1D` passed; `S0` was not accepted and `S1` was not attempted. The full `ElevenSquare.Verification` target has not been run on this checkpoint. Source audits pass, but no complete merged-stage kernel acceptance is claimed. Do not resume Lean on this Mac; use the larger computer.

Run the final target and public axiom audit with:

```sh
python3 scripts/verify.py --jobs 1
```

Resolve any failures without weakening the geometric statements. Require `OPTIMALITY_PROVED`, zero admissions and only the permitted standard axioms. The optional `--all` plus finalizer audit covers the entire retained repository; it is broader than the final theorem and does not benefit from the 2,032 removed module startups.

The compact T07 witness pilot was removed from the active proof after an S135 scout measured 54.126 CPU seconds for original literals versus 132.407 for compact recipes. These are single observations, not a general speed ratio. Its old acceptance receipt is historical experimental evidence. All four conditions in the S135 pruning benchmark fixtures passed Lean. The LCM helper also passed Lean, but its runtime comparison was not run and the prototype is not enabled. Neither result certifies a complete production stage, and no 2–3 hour full-build estimate is established. Preserve the packing definitions, public statements, strict ownership and closed touching/split semantics.
