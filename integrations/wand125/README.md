# Integration of wand125's published progress

The initial integration compared the native baseline at `b237948` with
[wand125/n11-optimality-lean](https://github.com/wand125/n11-optimality-lean):

- `main`: `ee96259ef815443587bd168658322efc8bb4b494`;
- `split`: `41b06d524a7240311d4675ee786f765cea8be507`.

The expanded family source is pinned separately at `split`
`a8b51d3e0682beb1bf911048bdc8e7fa62329124`; see
[release provenance and restoration](release/README.md). Baseline and prior
family source wiring is now active, but full native compiler and axiom validation
is pending. Two explicit source admissions remain; this is not a claim that all
other new source has been accepted by Lean.

The integration branch upgrades the project from Lean 4.10.0-rc2 to the latest
stable release checked on 2026-09-30, **Lean 4.34.1**, with mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`). The upstream release
itself used Lean 4.33.1. Compilation and axiom checking on the new version are
required; upstream reports alone do not certify this integration.

## What is additional

The initial comparison used the upstream `main` fields 0, 3, 6, and 19.
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
That initial coverage theorem passed Lean 4.34.1 checking with only the standard
axioms. Its historical audit does not validate the expanded generated witnesses
or the complete-family dependency paths, which still require fresh replay.

The `split` branch additionally publishes batch ownership promotion, triangle
ownership, and closed-half-plane branching rules, with their generators. These
are included in `Sqpack/S11Opt/Split/U2Rules.lean` and `Split/U2P/`.

The later published release supplies source for 1,904 field, 27 generic, and
76 prior exclusions. The field and generic families together cover the 1,931
native baseline indices, and the prior family covers the original 76 prior
indices. The source wrappers now use those families without changing the public
native statements. All new complete-family paths remain compiler-unverified.
Returned-family work is separate; its public admission remains open. Case438
capture is supplied by the extended traces of `ElevenSquare/Tasks/T07/Ext/`, whose
generated node modules are the release unit U5. The upper bound, canonical-case reduction, D4 bridge, and local isolation
overlap already completed native stages.

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
  conditional on that statement.
- `Families/BaselineCore.lean`: derives the native baseline contract from explicit
  field and generic family hypotheses, independently of generated certificate data.
- `Families/Baseline.lean` and `Families/Prior.lean`: apply the published family
  sources to those bridges. Their complete dependency paths await fresh compiler
  and axiom validation.

The T01 dispatcher retains the imported-field branch and completed native
groups, then uses the published baseline family. Its three admitted private plan
claims were retired as an unused alternative route and replaced by explicit
requirement types; they were not proved. All completed native proofs remain.
The prior wrapper keeps its original baseline premise, while its new source proof
uses independent imported exclusions. Public packing definitions and theorem
statements are preserved. Two explicit source admissions remain, alongside the
unverified new family paths; global optimality is still unfinished.

Evan Daniel's general packing definitions and lemmas were extracted verbatim
from the beginning of `Sqpack/S32.lean` into `Sqpack/Packing.lean`; the unrelated
32-square data/certificate is retained only as reference. Narrower explicit
mathlib imports replace the blanket `import Mathlib` to reduce compiler memory.
The native compatibility changes update renamed list-chain, array, function-update,
and convex-half-space APIs, plus the affected arithmetic and derivative proofs.
The geometric predicates retain their mathematical meaning. Expanded generated
witnesses are separately pinned and must be checked by the native compiler.

## Reproduction and checking

From the repository root:

```sh
# Restore pinned generated field/generic/prior sources; hashes are not Lean proofs.
python3 scripts/materialize_wand125.py

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
