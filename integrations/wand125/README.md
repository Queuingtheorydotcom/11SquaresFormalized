# Integration of wand125's published progress

This integration compares the native baseline at `b237948` with
[wand125/n11-optimality-lean](https://github.com/wand125/n11-optimality-lean):

- `main`: `ee96259ef815443587bd168658322efc8bb4b494`;
- `split`: `41b06d524a7240311d4675ee786f765cea8be507`.

The integration branch upgrades the project from Lean 4.10.0-rc2 to the latest
stable release checked on 2026-09-30, **Lean 4.34.1**, with mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`). The upstream release
itself used Lean 4.33.1. Compilation and axiom checking on the new version are
required; upstream reports alone do not certify this integration.

## What is additional

The reproducible certificates on upstream `main` are fields 0, 3, 6, and 19.
Their combined support excludes 1,103 canonical masks. Of these, 247 lie outside
the 1,132-case union of the previously completed native G003/G004/G007 groups.
Field 3 alone overlaps G003; the additional coverage comes from the other fields.
The exact lists and comparison are in `coverage.json`.

| Field | Cases covered | Outside native G003/G004/G007 |
| --- | ---: | ---: |
| 0 | 126 | 88 |
| 3 | 764 | 0 |
| 6 | 126 | 48 |
| 19 | 252 | 126 |
| Union | 1,103 | 247 |

The last column is not additive because the fields overlap. The combined native
and imported coverage is 1,379 baseline cases, leaving 552 outside that union.
The concrete coverage theorem has passed Lean 4.34.1 checking with only the
standard axioms. The wider native toolchain migration is still being checked.

The `split` branch additionally publishes batch ownership promotion, triangle
ownership, and closed-half-plane branching rules, with their generators. These
are included in `Sqpack/S11Opt/Split/U2Rules.lean` and `Split/U2P/`.

The `split` README reports checked individual prior and returned cases, and
additional field/generic work on a separate build machine. Those generated
individual certificates are absent from the pinned Git tree. They are not
counted as imported proofs. The public family theorems still contain placeholders.
The upper bound, canonical-case reduction, D4 bridge, and local isolation overlap
already completed native stages. Neither repository completes case438 capture.

## How the proofs connect

`Sqpack/` contains the imported checker and regenerated certificates, adapted to
the pinned toolchain. `ElevenSquare/Interop/Wand125/` supplies the connection:

- `Geometry.lean`: preserves closed square bodies and open interiors, and proves
  `Packable 11 S ↔ SquarePacking.Packs 11 S` for the actual models.
- `Cells.lean`: proves equality of the physical Voronoi sites after the native
  normalization, and converts native closed-cell occupancy into `Realizes`.
- `Certificates.lean`: transports imported exclusions into the original
  initialized-terminal-trace contract, as the native completed groups do.
- `Coverage.lean` and `Coverage/`: check the concrete 247 new cases and their disjointness from
  the old completed groups.
- `Families.lean` and `Families/CaseOrder.lean`: check that the recorded case tuples equal
  upstream `maskAt` (one kernel check per 64-row chunk), that the prior, returned, and
  candidate arrays equal upstream `priorIdx`, `returnedIdx`, and `candIdx`, and that the 27
  upstream generic cases are baseline cases. They turn any upstream family statement
  `∀ i ∈ …, CaseExcluded (maskAt i)` into the `S06` trace contract. Every theorem there is
  conditional on that statement; no admission site changes.

The T01 dispatcher tries the imported certificate before the existing groups
and residual plan obligations. Public packing definitions and theorem statements
are preserved. The six original admissions remain; the integration does not
claim a proof of global optimality.

Evan Daniel's general packing definitions and lemmas were extracted verbatim
from the beginning of `Sqpack/S32.lean` into `Sqpack/Packing.lean`; the unrelated
32-square data/certificate is retained only as reference. Narrower explicit
mathlib imports replace the blanket `import Mathlib` to reduce compiler memory.
The native compatibility changes update renamed list-chain, array, function-update,
and convex-half-space APIs, plus the affected arithmetic and derivative proofs.
Certificate data and geometric predicates retain their mathematical meaning.

## Reproduction and checking

From the repository root:

```sh
# Exact source comparison and finite coverage calculation; NOT a Lean proof.
python3 integrations/wand125/check_comparison.py

# Reproduce upstream numerical witnesses, checking the upstream SHA256 manifest.
# The destination must not already exist. This downloads pinned public inputs.
N11_NO_BUILD=1 N11_JOBS=2 sh integrations/wand125/main/build.sh .verification/wand125-replay

# Check the imported proof, native bridge, and concrete new-case theorem serially.
python3 scripts/verify.py --setup --module ElevenSquare.Interop.Wand125.Geometry \
  --module ElevenSquare.Interop.Wand125.Cells \
  --module ElevenSquare.Interop.Wand125.Coverage \
  --module Sqpack.S11Opt.Axioms --module Sqpack.S11Opt.Split.U2P.Branch

# Check the full upgraded local source tree and final public axiom audit.
python3 scripts/verify.py --all --fresh
```

`main/` and `split/` are exact upstream reference snapshots. Their hashes and
commit identities are in `provenance.json`; the source comparator verifies them.
They are not Lean library roots. In particular the five upstream `split`
placeholders are not imported into the native proof. Upstream's VM-specific
shell helpers in `split/scripts/u2p/` are preserved as reference; use the local
serial verifier for compilation. Machine build output belongs in `.verification/`.

`imported-source-hashes.json` records the initial import before compatibility
edits. `evand-provenance.json` identifies its external geometry dependency.
The generated data reproduction completed with `N11_DATA_VERIFIED`; that marker
checks data hashes, not Lean proofs. The 180-module focused integration replay passed, including the imported axiom
audit and the split-branch rules. Its target axioms and source hashes are saved in
`verification/wand125-integration.json`. Full-project compilation remains pending;
this focused result does not certify the entire toolchain migration.

## Attribution

Wand125's formalization is MIT licensed; see `main/LICENSE` and `split/LICENSE`.
Evan Daniel's geometry/checker is MIT licensed; see `EVAND-LICENSE.txt` and
`main/UPSTREAM-LICENSE.txt`. The packing is Walter Trump's, and the optimality
argument and original certificate data are by Queuing Theory #1 Fan. Preserve
these notices when redistributing the imported source.
