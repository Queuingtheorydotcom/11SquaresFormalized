# Complete-family release integration

This directory pins the expanded `split` source at
`a8b51d3e0682beb1bf911048bdc8e7fa62329124` from
[wand125/n11-optimality-lean](https://github.com/wand125/n11-optimality-lean).
`upstream/` is an exact source snapshot, outside the active Lean library roots.
The earlier `../main/` and `../split/` snapshots retain their original identities.

The [n11-certs-v1 release](https://github.com/wand125/n11-optimality-lean/releases/tag/n11-certs-v1)
publishes the following generated certificate sources:

| Unit | Coverage | Archives |
| --- | --- | ---: |
| F, FCOMMON | 1,904 field cases | 59 plus shared data |
| U2G | 27 generic cases | 27 |
| U2P | 76 prior cases | 76 |
| U2R | 172 returned cases | 172 |

Field and generic cases partition the 1,931 native baseline cases. Returned case
1465 is absent. The complete upstream `U2Returned.lean` imports that missing
case and must not be used as evidence of a complete returned family. Case438
capture also remains unfinished. The upstream compiler was Lean4.33.1; native
acceptance requires the project's pinned Lean4.34.1 compiler and actual axiom
audits. Downloading or matching hashes does not establish a Lean proof.

## Fetching

Restore the generated sources required by a fresh checkout from the repository
root:

```sh
python3 scripts/materialize_wand125.py
```

This command restores F, FCOMMON, U2G, and U2P into the active `Sqpack/` tree.
U2R belongs to the separate returned-family workstream and is not fetched.
Rerun the same command to resume an interrupted restoration. Every run validates
the pinned metadata and checks all existing destination sources before fetching.
An asset whose Lean sources already match needs neither its archive nor network
access. Missing assets are verified and installed one at a time, avoiding a
temporary extraction of an entire multi-gigabyte unit. A differing source or a
symlink is rejected; local changes are never overwritten.

For an existing local archive collection or a separate destination:

```sh
python3 scripts/materialize_wand125.py --from-dir /path/to/assets
python3 scripts/materialize_wand125.py --destination /path/to/checkout --cache-dir /path/to/cache
```

The destination is the directory containing `Sqpack/`. The default archive cache
is `.verification/wand125/releases`. F00's `Roots.txt` is checked when its archive
is needed, but is not required or installed in the active source tree.

From the native repository root, inspect a selection without downloading:

```sh
python3 scripts/fetch_wand125_release.py --unit U2P --case 221 --list
```

Fetch and check the same selection into an ignored staging tree:

```sh
python3 scripts/fetch_wand125_release.py --unit U2P --case 221
```

To install verified generated sources into the active native source tree:

```sh
python3 scripts/fetch_wand125_release.py --unit U2P --case 221 --destination .
python3 scripts/fetch_wand125_release.py --unit U2G --case 220 --destination .
```

Omit `--case` to select a whole unit; `--field` is its alias for F. FCOMMON has no
case selector. `--from-dir` reads an existing local archive collection. Repeated
calls reuse the hash-verified archive cache and retain identical destination
files. Existing differing sources are rejected; review an upstream source
update rather than deleting local changes to force installation.

The loader checks pinned archive digests, exact extracted membership, and every
source digest before writing the selected destination files. Metadata digests
are embedded in the loader and recorded in `provenance.json`; it does not trust
a newly downloaded checksum list. It rejects unsafe archive paths and links.
F00's auxiliary `Roots.txt` is verified but is not installed as a Lean source.

Size limits default to1GiB per compressed archive and4GiB total extracted data
per invocation. Increase `--max-archive-mib` or `--max-extracted-mib` only after
checking available resources. The complete release is approximately2.18GB
compressed, and sources plus compiler objects require additional space. A
failed or interrupted fetch does not count as proof acceptance.

## Validation and ownership

Generated case/field source directories are ignored by Git; the pinned release
and manifests reproduce them. Already tracked certificate files remain tracked.
The native source checker still scans every materialized Lean file, including
ignored generated sources. Compile selected import closures with the existing
serial `scripts/verify.py`; full integration additionally requires the native
public-target axiom audit and complete supported-source replay.

The integration line owns field/generic baseline and prior-family wiring. The
returned172 component can be developed independently on a collaborator branch.
Its public partial theorem must carry an explicit case1465 exception. The T03
branch and its independently audited release sources remain separate.

Loader regressions run without Lean or network access:

```sh
python3 scripts/test_fetch_wand125_release.py
python3 scripts/test_materialize_wand125.py
```

Only actual completed native compiler results may be published as acceptance
evidence. `provenance.json` currently records this release's native replay as
incomplete. Global optimality remains unfinished.
