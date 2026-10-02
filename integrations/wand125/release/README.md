# Complete-family release integration

The original expanded `split` snapshot is pinned at
`a8b51d3e0682beb1bf911048bdc8e7fa62329124` from
[wand125/n11-optimality-lean](https://github.com/wand125/n11-optimality-lean).
`upstream/` is an exact source snapshot, outside the active Lean library roots.
The earlier `../main/` and `../split/` snapshots retain their original identities.
F, FCOMMON, U2G, and U2P retain these original pins. The active U2R metadata is
overridden separately at `8126ef4d5ce0ecc967d7223388bac65ee5ffce5e`, adding
case1465. The native U5 extension is integrated from
`2b539e977c9e5daf2a68cb896c2acc1a21d49e39`. `provenance.json` preserves original
snapshot hashes and records the active per-file metadata overrides separately.

The [n11-certs-v1 release](https://github.com/wand125/n11-optimality-lean/releases/tag/n11-certs-v1)
publishes the following generated certificate sources:

| Unit | Coverage | Archives |
| --- | --- | ---: |
| F, FCOMMON | 1,904 field cases | 59 plus shared data |
| U2G | 27 generic cases | 27 |
| U2P | 76 prior cases | 76 |
| U2R | 173 returned cases, including case1465 | 173 |
| U5 | case438 phase 2, capture branches, and near inclusion | 11 |

Field and generic cases partition the 1,931 native baseline cases. The active
`U2Returned.lean` and native adapter now use the complete 173-case family. The
native U5 extension supplies the original case438 certificate interface. Both
former admissions have proof bodies, but all complete native paths still require
compiler replay and transitive axiom acceptance. The original snapshot used
Lean 4.33.1; native acceptance uses pinned Lean 4.34.1. Downloading, matching
hashes, and an empty admission inventory do not establish a Lean proof.

## Fetching

Restore the generated sources required by a fresh checkout from the repository
root:

```sh
python3 scripts/materialize_wand125.py
```

This command restores F, FCOMMON, U2G, U2P, and U2R into the active `Sqpack/`
tree, and U5 into `ElevenSquare/Tasks/T07/Ext/Gen/`.
Rerun the same command to resume an interrupted restoration. Every run validates
the pinned metadata and checks all existing destination sources before fetching.
An asset whose Lean sources already match needs neither its archive nor network
access. Missing assets are verified and installed one at a time, avoiding a
temporary extraction of an entire multi-gigabyte unit. A differing source or a
symlink is rejected; local changes are never overwritten.

After restoration, the command derives `Sqpack/S11Opt/Bundled/` from the
authenticated originals. The same step runs before source discovery in
`verify.py --setup`. F01–F58's 2,007 coverage modules become 559 independent
leaf bundles and 58 aggregators; the 134 shared ownership modules become three
independent leaf bundles. Original declaration bodies and numeric data are
preserved. Fresh namespaces, original-statement type checks, and axiom queries
keep the derived proofs independently auditable. F00 remains unchanged.

Derived sources and provenance manifests are ignored by Git and require about
1.6 GiB in addition to the originals and compiler objects. Source generation
does not establish Lean acceptance. Existing different generated files are
rejected, including stale generation manifests; inspect those differences before
regenerating. Use `--raw-only` to restore just the original release files into a
staging directory without the repository's tracked assembly sources.

For an existing local archive collection or a separate destination:

```sh
python3 scripts/materialize_wand125.py --from-dir /path/to/assets
python3 scripts/materialize_wand125.py --destination /path/to/checkout --cache-dir /path/to/cache
```

The destination is the directory containing `Sqpack/` and `ElevenSquare/`.
The default archive cache is `.verification/wand125/releases`. F00's `Roots.txt` is checked when its archive
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
python3 scripts/fetch_wand125_release.py --unit U2R --case 1465 --destination .
python3 scripts/fetch_wand125_release.py --unit U5 --destination .
```

Omit `--case` to select a whole unit; `--field` is its alias for F. FCOMMON and U5
have no case selector. `--from-dir` reads an existing local archive collection. Repeated
calls reuse the hash-verified archive cache and retain identical destination
files. Existing differing sources are rejected; review an upstream source
update rather than deleting local changes to force installation.

The loader checks pinned archive digests, exact extracted membership, and every
source digest before writing the selected destination files. Metadata digests
are embedded in the loader and recorded in `provenance.json`; it does not trust
a newly downloaded checksum list. It rejects unsafe archive paths and links.
F00's auxiliary `Roots.txt` is verified but is not installed as a Lean source.

Size limits default to 1 GiB per compressed archive and 4 GiB total extracted data
per invocation. Increase `--max-archive-mib` or `--max-extracted-mib` only after
checking available resources. The expanded collection, dependencies, and
compiler objects require substantial additional space. A
failed or interrupted fetch does not count as proof acceptance.

## Validation and ownership

Generated case/field source directories are ignored by Git; the pinned release
and manifests reproduce them. Already tracked certificate files remain tracked.
The native source checker still scans every materialized Lean file, including
ignored generated sources. Compile selected import closures with the existing
serial `scripts/verify.py`; full integration additionally requires the native
public-target axiom audit and complete supported-source replay.

The complete returned adapter preserves the native initialized-terminal-trace
contract. The U5 extension preserves strict ownership, closed split coverage,
and the original physical-side certificate. Existing native T03 progress remains
intact. The baseline adapter still uses original fields until the F04 bundled
pilot is reproduced and the switch in `NEXT_COMPUTER.md` is made.

Loader regressions run without Lean or network access:

```sh
python3 scripts/test_fetch_wand125_release.py
python3 scripts/test_materialize_wand125.py
python3 -m unittest discover -s scripts -p 'test_*bundle*.py'
```

Only actual completed native compiler results may be published as acceptance
evidence. `provenance.json` currently records this release's native replay as
incomplete. Finish the full fresh `verify.py --all` replay and validate current
receipts with `scripts/finalize_verification.py` before publishing completion.
A focused final-theorem audit does not satisfy that full-source gate.
