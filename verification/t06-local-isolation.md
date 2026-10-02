# T06 local-isolation port: verified

Verified October 2, 2026 against integration base
`525f4a68bd06a431ed81c19218b2666fe1cdff2e`, with the unchanged
Lean `leanprover/lean4:v4.34.1` toolchain and mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Accepted result

- All 128 required integer-certificate modules passed ordinary Lean checking.
- The official `S08_ExactPacket` replay accepted its entire 833-module closure.
- The official `LocalIsolationAudit` replay accepted its 834-module closure,
  including the actual public completion targets.
- All 8,448 rational dual checks, their numerical data, and the existing public
  theorem statements are preserved.

Actual output from the new audit module:

```text
'ElevenSquare.Pending.exact_local_packet_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'ElevenSquare.Pending.construction_locally_isolated' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The selected closure's other explicit axiom queries also passed the official
audit. No new admission, custom axiom, computational oracle, or weakened
statement is introduced.

This is a **T06 local-isolation result**. Whole-project replay and global
optimality remain outside this verification. The source assembly still has the
same two documented admissions elsewhere; this result does not certify them.

## Proof changes

Each `CertificateIntegerNNN.lean` now proves its 33 sparse-vector projections
as small private function-equality lemmas using `rfl`. The existing `branchDots`
case proof transports those opaque equalities with `congrFun`, avoiding the
large definitional-equality reduction that caused kernel deep recursion.

The 33 column proofs and all 66 integer-check declarations per shard are
unchanged. Reversing only the private helpers and their transports reproduces
every original shard byte-for-byte. `CertificateBridge.lean` adds only
`zero_mul` to an existing simplification proof. `S08_ExactPacket.lean` is
unchanged. `LocalIsolationAudit.lean` supplies the two public axiom queries.

The representative `CertificateInteger087` first reproduced the original
kernel recursion failure. Its final focused replay passed all 50 selected
modules, with the certificate itself compiling in 92.96 seconds. That verifier
invocation took 97.884 seconds with a peak child RSS of 2,907,464 KiB. These are
observations from that run, not a performance guarantee.

## Reproduce

Use the exact integration base above. Apply the supplied commit/patch, or copy
the complete source overlay onto that base. The overlay is not a standalone
repository and does not contain the compiler or dependency caches.

Restore the repository's pinned generated sources and dependencies according
to `README.md`; do not update `lean-toolchain` or `lake-manifest.json`. Then run:

```sh
python3 -m unittest discover -s scripts -p 'test_check_t06_preservation.py' -v
python3 scripts/check_t06_preservation.py
python3 scripts/verify.py --module ElevenSquare.Tasks.T06.CertificateInteger087 --keep-going
python3 scripts/verify.py --module ElevenSquare.Pending.S08_ExactPacket --keep-going
python3 scripts/verify.py --module ElevenSquare.Tasks.T06.LocalIsolationAudit --keep-going
```

The preservation checker is read-only and needs Python 3, Git, and the fixed
base commit. Its 18 regression tests reject changed data, changed statements,
missing checks, incorrect transports, unexpected dependencies, and weakened
audit queries. It is additional source evidence, not a mathematical premise.

The compiler runs used the unchanged official serial verifier. Accepted
source/compiler/dependency/object fingerprints were reused after execution
interruptions. Bounded, disjoint certificate prechecks used that same verifier;
the final serial packet and audit passes validated the complete selected
closure. This was **resumed verification**, not one uninterrupted fresh build.
Add `--fresh` to an official verifier command to disregard local receipts.

## Portable evidence

`verification/t06-local-isolation.json` records the exact compiler version and
arguments, all nine checked dependency revisions, configuration and verifier
hashes, source hashes for all 834 selected modules, source-preservation hashes,
actual axiom output, and the final replay counts. All nine dependency checkouts
matched their pinned revisions with no tracked changes.

Machine-specific compiler logs, receipts, object caches, recovery controls, and
discarded experiments remain in ignored directories and are not part of the
portable source commit. No required selected module remains failed or untested.
Modules outside the selected audit closure remain unverified by this result.
