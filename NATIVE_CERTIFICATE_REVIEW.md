# Native numerical certificate checkpoint review

Reviewed checkpoint: `69d4daf0` on
`codex/native-numerical-certificates-20261004`, dated 2026-10-05.
The parallel verifier is merged from `01d45863` on
`codex/simplification-verifier-20261003`. This review concerns source changes
and verification machinery. The complete production Lean replay is still
required before reporting formalization success.

## What changed in the numerical proofs

The current inventory, [verification/native-certificates.json](verification/native-certificates.json),
contains 10,464 numerical declarations in 1,839 Lean source files. Their closed
finite checks use `by native_decide` in place of `by decide +kernel`.
These include the T07 arithmetic and promotion/coverage checks, generated
field and ownership checks, and the numerical hypotheses supplied to the
existing `soundDec` soundness theorems. The later expansion in `c4724fe1`
converts 3,079 such hypotheses under `F00`, `Split/U2G`, `Split/U2P`,
`Split/U2R` and `Bundled/Own`.

The computations and certificate data remain in the Lean project and execute
during compilation. What changes is how their result is established:

- Kernel evaluation reduces the finite decision procedure inside Lean's
  proof kernel.
- Native evaluation compiles and executes the decision procedure. Lean then
  uses a generated axiom asserting the successful result. The kernel checks
  the surrounding proof using that axiom.

Thus numerical verification additionally trusts Lean's compiler/interpreter
and arithmetic runtime. Geometry, checker soundness and theorem assembly
retain ordinary Lean proofs. This is exact finite arithmetic, rather than
replacing a certificate with an unchecked Python answer or deleting its test.
See [the pinned Lean tactic implementation](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Elab/Tactic/Decide.lean)
and [Lean's axiom documentation](https://lean-lang.org/doc/reference/latest/Axioms/).

If full replay and the final axiom audit succeed, an appropriate description
is: **“Formalized in Lean using native evaluation for finite numerical
certificates; verification additionally trusts Lean's compiler and runtime.”**
The expected successful status is
`OPTIMALITY_PROVED_WITH_NATIVE_CERTIFICATES`, with
`trust_model: lean_kernel_and_native_compiler` and zero admissions.
This statement is conditional on that future replay; it is not a claim that
this checkpoint has already passed it.

## Other changes on this branch

In [verification/native-data-compatibility.json](verification/native-data-compatibility.json),
11 generated field-data files drop `noncomputable` from 119 closed finite
definitions. Their types and bodies stay the same; the modifier change lets
the compiler execute their data constructors.

The indexed-data compilation pass in `2d673746` splits oversized array
initializers into private definitions for literal rows, then constructs the
same arrays from those definitions: 21 tables in 21 files become 1,574
private literal-row definitions. Its authenticated ledger is
[simplification/indexed-data-compilation.json](simplification/indexed-data-compilation.json).
It addresses compilation of enormous initializer expressions; it does not
remove the table entries or introduce a further proof oracle.
All 21 predecessor source hashes match the actual `e5200e0e` Git versions;
the complete source preflight passes the authenticated inversions and checks
the same literal rows, row order and deterministic reconstruction.

Relative to the previous simplified checkpoint `34e6b035`, this branch also
inherits the earlier source reductions described in
[simplification/REVIEW_317.md](simplification/REVIEW_317.md) and
[PC_RESUME.md](PC_RESUME.md): module bundling, indexed triangle/target data,
shared geometric arguments, and trimming unused T07 certificate data.
The trimming removes 5,964,331 trailing zero weights and 20,152 unused
collision-core lists across 459 stages. The active T07 checker is retained;
the optional determinant checker is an inactive pilot. These structural
changes are distinct from the subsequent native evaluation substitution.
Their source ledgers and small historical fixtures do not establish acceptance
of the whole current proof.

Git object comparisons confirm that `ElevenSquare/Optimality.lean`,
`Foundations.lean`, `Construction.lean`, `BasicGeometry.lean` and
`EndpointBounds.lean` are byte-identical to `34e6b035`. In particular, the
public theorem still asserts the lower bound for the actual `Packable 11 S`
predicate, and `Optimality` still includes both construction and lower bound.

## Source and remaining-computation audit

An independent static scan covered **all 7,920 tracked Lean modules
(1,051,992,052 source bytes)**. The final verification import closure contains
4,258 modules, including the 4,257-module optimality closure. Every source
matched the reviewed commit's Git blob.

For all 1,839 inventoried native files, reversing only the tactic spelling
reproduced both the recorded kernel-source SHA-256 and the actual pre-native
Git blob from `e5200e0e`. There are exactly 10,464 native tactic occurrences;
none occurred outside that inventory. All 11 field-data files likewise
reconstructed the pre-native Git blobs after restoring their 119 modifiers.
This independently confirms that the native conversion and modifier changes
preserve the earlier theorem statements, certificate values and expressions.

The scan found **15,238 remaining decision-tactic occurrences in 1,188 files**:
6,371 explicit `decide +kernel` and 8,867 plain `by decide` sites. Of those,
14,256 are inside the final verification import closure. These are lexical
occurrence counts, not runtime costs or counts of independent computations.
No remaining decision line contained a literal of at least 100 digits, but
imported data can still make a short proof line expensive.

The remaining families include:

- Mask equalities, small index/distinctness facts, row counts and label lookups.
- Thousands of finite subset checks passed to `CovF.weaken`.
- Ownership trace validation in 267 generated main proofs, including
  `Split/U2R/C1311/Main.lean:313`. `OwnedTrace.check` and
  `ConditionalOwnedTrace.check` traverse promotions/branches and validate
  triangle orientation, point membership and dependencies. They use the
  supplied coverage proofs rather than recomputing their numerical certificates.
  Nevertheless, large traces and repeated list membership are potential
  secondary kernel bottlenecks.
- Barycentric conditions and final weighted inequalities in the bundled field
  proofs; finite hull/alias checks and the large inventory tree's bookkeeping.
- Retained experimental numerical pilots outside the final theorem closure,
  such as `CompactWitnessRealPilot.lean`, which the launcher's `--all` scope
  also compiles. They still contain kernel-backed numerical tests.

The targeted giant-integer certificate checks were converted. No further
kernel-backed check of that same giant-integer family was identified in this
static review. **This does not establish that all expensive kernel computation
is gone.** The trace and other finite checks above need runtime observation;
normalization through `rfl`, `simp` or `norm_num` and imported data is not fully
classified by a decision-tactic scan. This review makes no complete runtime
guarantee and introduces no additional native permissions.

Large native inputs also remain: the longest numeral found has **418,642
decimal digits**, in
`Simplified/ReducedConditional/U2P/C1383/SharedStages002.lean`.
Parsing, elaboration, generated code, compiled evaluation and ordinary proof
checking can all take substantial time even after removing kernel reduction
of the main numerical certificates.

The comment/string-masked Lean scan found no local `unsafe`, `implemented_by`,
`extern`, `#eval`, `run_cmd`, `initialize` or `builtin_initialize` forms.
That is a focused static finding, not an isolation mechanism or a guarantee
about arbitrary executable behavior in dependencies or tactics.

Source checks alone cannot bound elaboration time, native computation time
or peak memory. Large literal data and compiled numerical checks remain.
Acceptance and practical performance require the production replay.

## Merged verification behavior

The parallel scheduler preserves the native branch's source inventory and
axiom policy. It permits native axioms only for the exact inventoried
declaration owners, and rejects an unapproved owner or `sorryAx`.
Source preflight authenticates the native source hashes and the inverse
`decide +kernel` sources, the computable data variants and split initializers.
The merge reconstructs native inverses by joining original source spans once,
avoiding repeated copies of large files while retaining the same exact hashes.
`--setup` installs dependencies only; it preserves the tracked native sources.

The Slurm launcher checks all local modules, validates their receipts and
final theorem axiom logs, then writes a completion receipt that explicitly
records native compiler trust. Its defaults are one node, 192 CPUs,
96 concurrent Lean processes with two threads each, 1,300 GiB RAM and one day.
Accepted module checkpoints can resume after allocation loss; a module still
running at cutoff restarts from its beginning. Instructions are in
[LEAN_VERIFICATION_RUNBOOK.md](LEAN_VERIFICATION_RUNBOOK.md).

Local validation exercises source policies, inverse transformations,
scheduling, resources, cancellation, resume, finalization and successful-job
receipts using fixtures: **238 distinct tests passed**, with 80 relevant
source-policy tests rerun after the inverse reconstruction optimization.
Shell syntax checks also passed. `python3 -B scripts/verify.py --all --plan`
passed for all 7,920 modules, reporting `SOURCE_ASSEMBLY_PASS`, zero admissions
and 10,464 approved native declarations. This source-only result explicitly
reports `global_optimality_proved: false`. These checks do not replace compilation with pinned Lean
4.34.1 and mathlib on the cluster. No toolchain or dependency installation
was performed for this review.
