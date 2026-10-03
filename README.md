# Eleven-square simplification: unverified checkpoint

The current `ElevenSquare.Optimality` source closure contains **394,204 physical Lean lines in 6,326 local modules**, including all reached certificate data. Source bytes total **1,087,162,218**. The 300,000-line target has not been reached.

**The complete assembled theorem and the latest simplifications have not passed Lean verification.** Read [PC_RESUME.md](PC_RESUME.md) for the current branch, checks, and next steps. [SIMPLIFICATION_HANDOFF.md](SIMPLIFICATION_HANDOFF.md) preserves the earlier imported 494,346-line checkpoint's history; its old build-status notes are superseded by the current handoff.

## Verification on the cluster

Branch `codex/simplification-verifier-20261003` merges the parallel verifier,
Slurm launcher, resumable receipts and final completion gate into the simplified
checkpoint. Follow [LEAN_VERIFICATION_RUNBOOK.md](LEAN_VERIFICATION_RUNBOOK.md).
On this branch, `verify.py --setup` installs only Lean and mathlib dependencies;
the simplified Lean sources are already tracked. Do not run the older
`materialize_wand125.py` restoration workflow here.

The mathematical sources are unchanged from simplified checkpoint `34e6b035`.
Parallel scheduling and source checks do not establish Lean acceptance; full
replay and public axiom audits remain required.
