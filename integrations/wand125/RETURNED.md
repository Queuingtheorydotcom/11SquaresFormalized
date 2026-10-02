# Complete returned-family source integration

The returned-family source now includes all 173 indices, including case1465.
The upstream source is pinned independently of the earlier field and prior
snapshot to commit `8126ef4d5ce0ecc967d7223388bac65ee5ffce5e` of
`wand125/n11-optimality-lean`. Its `n11-certs-v1` release supplies all 173
`n11-u2r-C<case>.tar.xz` archives. This supersedes the earlier release inventory
that lacked case1465.

`Sqpack/S11Opt/Split/U2Returned.lean` is the exact upstream dispatcher from
`lean/Sqpack/S11Opt/Split/U2Returned.lean` at that commit. Its SHA-256 is
`d08dbe915528441767c09e84e6d8d4290eeea27f57cb86c91d7302c0483551ed`.
It combines the per-case `U2R.C<case>.excluded` proofs into
`SquarePacking.S11Opt.Split.returned_excluded`.

The authenticated generated-source metadata at the same commit is:

| File | Upstream path | SHA-256 |
| --- | --- | --- |
| `MANIFEST_U2R.sha256` | `scripts/u2p/MANIFEST_U2R.sha256` | `ea1451c6000a991915209202167e92b9c024d7bb78aa17a765566f7c730f8610` |
| `SHA256SUMS_U2R` | `scripts/u2p/SHA256SUMS_U2R` | `2bb7fe4f0b35277822a77688d10f268f6ac4fe64fed1cf7c2867ee7929961f9e` |

The case1465 archive has SHA-256
`75fc500837266b6c28144ba56c196229fb5d9afafb158451d656e3d5458a3eb6`.
The loader must validate both the archive and each extracted source against
these pinned records. Source availability and hash checks do not certify Lean
acceptance.

`ElevenSquare/Interop/Wand125/Families/Returned.lean` applies the existing
`returned_certificate_of` transport to the complete upstream family. The public
`returned_certificate_exists` and `returned_excluded` signatures remain unchanged:
the initializer still quantifies over every packing at `coverCap`, its chart and
actual occupied case mask, and produces the same relabeled `StateHolds`,
`VerifiedTrace`, and `Terminal` contract. The adapter does not depend on baseline
exclusion, the final symmetry bridge, or optimality. Independent T03 progress
remains intact.

After restoring the pinned sources, run the repository's serial checker:

```sh
python3 scripts/verify.py --module ElevenSquare.Pending.S06_Returned --keep-going
```

The adapter and public wrapper include explicit axiom queries. Their complete
dependency replay must pass on the pinned Lean 4.34.1 toolchain with only
`propext`, `Classical.choice`, and `Quot.sound`. This source integration has not
yet earned that native acceptance. Full optimality additionally requires the
remaining dependency closures and final public axiom audits.
