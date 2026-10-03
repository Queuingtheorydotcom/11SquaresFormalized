# Verification execution boundary

The verifier and Slurm job run directly under the invoking account's permissions.
Source restoration, Python helpers, Lake configuration and Lean elaboration can
perform filesystem, process and network operations. Lean checking is not an
isolation boundary: tactics, metaprograms and dependency initializers can execute
code during compilation even without running a program's `main`.

This workflow assumes the reviewed repository sources, official elan/Lean/Lake,
mathlib and its pinned dependencies and downloaded artifacts are trusted. Keep
`lean-toolchain` and `lake-manifest.json` unchanged for reproduction. The mathlib
cache bootstrap may download and execute its upstream static curl fallback.
The source review found no malicious payload; it is not a proof that every
compiler or dependency behavior is harmless, nor a review of future changes.

Slurm supplies the allocation and site resource policies. The verifier's
memory-headroom guard is advisory, and large certificate checks may disable
Lean heartbeat limits. Interrupted checks preserve accepted module receipts
and objects; unfinished modules restart on the next invocation. Use a
persistent checkout to retain those checkpoints.

See [LEAN_VERIFICATION_RUNBOOK.md](LEAN_VERIFICATION_RUNBOOK.md) for the supported
setup, launch and recovery procedure. No container runtime is required or
provided by this workflow.
