# Eleven-square simplification: unverified checkpoint

The `ElevenSquare.Optimality` source closure contains **365,392 physical Lean lines in 4,257 local modules**, including all reached certificate data. Compared with the prior 394,204-line / 6,326-module checkpoint, this removes **28,812 lines and 2,069 reachable modules**. The 300,000-line target has not been reached.

**The complete assembled theorem remains unverified; the full verification target has not been run on this checkpoint.** Source-preserving module bundling removes 2,032 module launches from a cold theorem replay. The slower compact-witness experiment was excluded; active T07 certificates retain their original literal data. No complete-build runtime is established.

Certificate-data trimming now removes **34,739,375 bytes** across 459 T07 stages: **5,964,331 trailing zero weights** and **20,152 unused collision-core lists**. The active source closure is **1,051,109,682 bytes**. The production checker is unchanged. Exact inverse audits and the frozen 38-row pruning fixture pass; the entire transformed corpus has not been replayed through Lean.

An optional determinant checker has kernel-checked soundness proofs. In two mirrored S135 trials, combining it with unused-core removal reduced median CPU time from **51.78 to 36.31 seconds** (about **30%**) and reduced the standalone input source by about **46%**. This checker remains an inactive pilot; the figures do not establish a full-build speedup or the 2–3 hour target. See [the certificate-data report](simplification/T07_DATA_PROFILE_20261003.md).

The selected S0/S1 replay was stopped cleanly because of low disk space and heavy swapping. Dependencies through `S1D` passed, but `S0` was not accepted and `S1` was not attempted. Source audits pass; no complete merged-stage kernel acceptance is claimed. Full Lean verification should run on the larger computer; the later certificate experiments used bounded, isolated fixtures.

The main verification command is `python3 scripts/verify.py --jobs 1`. It checks `ElevenSquare.Verification`, its dependencies and the public axiom audit. The optional `--all` audit also checks retained historical and compatibility modules and does not gain the module-startup reduction.

Read [PC_RESUME.md](PC_RESUME.md) for the branch and verification steps, and [simplification/REVIEW_317.md](simplification/REVIEW_317.md) for the reductions. [SIMPLIFICATION_HANDOFF.md](SIMPLIFICATION_HANDOFF.md) preserves the earlier imported 494,346-line checkpoint's history; its old build-status notes are superseded by the current handoff.
