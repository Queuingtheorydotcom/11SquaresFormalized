# Verification execution boundary

The verifier and Slurm job run directly under the invoking account's permissions.
Source restoration, Python helpers, Lake configuration and Lean elaboration can
perform filesystem, process and network operations. Lean checking is not an
isolation boundary: tactics, metaprograms and dependency initializers can execute
code during compilation even without running a program's `main`.

This workflow assumes the checked-out repository sources, official elan/Lean/Lake,
mathlib and its pinned dependencies and downloaded artifacts are trusted. Keep
`lean-toolchain` and `lake-manifest.json` unchanged for reproduction. The mathlib
cache bootstrap may download and execute its upstream static curl fallback.
The earlier source review covered the original proof branch. It does not cover
the new simplified Lean sources, and commit provenance does not authenticate
all code as safe. Verification runs with the invoking account's permissions.

On this simplified branch, `verify.py --setup` installs only Lean and mathlib
dependencies. All simplified proof sources are tracked; the older generated
proof archives are not restored by the job.

Slurm supplies the allocation and site resource policies. The verifier's
memory-headroom guard is advisory, and large certificate checks may disable
Lean heartbeat limits. Interrupted checks preserve accepted module receipts
and objects; unfinished modules restart on the next invocation. Use a
persistent checkout to retain those checkpoints.

See [LEAN_VERIFICATION_RUNBOOK.md](LEAN_VERIFICATION_RUNBOOK.md) for the supported
setup, launch and recovery procedure. No container runtime is required or
provided by this workflow.

The optional `scripts/wand125_u5` certificate generators load and save validated
JSON states with exact rational numbers, rather than executable pickle objects.
Their checkpoint and final-state filenames now end in `.json`. Regenerate old
`.pkl` states from the original JSON archives; there is no pickle compatibility
loader. Update `U5_P2STATE` to the new `p2_state.json` path when using those
generators. The Slurm verifier does not invoke them, and its `.verification/`
receipts and `.lake/` resume data use the existing format. Archive `node_id` text
is escaped before being placed in generated Lean comments.
