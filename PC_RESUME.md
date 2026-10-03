# Resume the unverified simplification checkpoint

Branch: `codex/simplification-unverified-20261003`.

This is a source candidate, not a verified full proof. Work stopped at the user's request before full replay. Main and the T03 progress branch were not changed. The imported bundle commit is `dac90e2f02d4afe8482096e13b9dcf546d871fde`, based on `c82cff63e48b2d3f2da60cb998bbab48e557c012`.

## Exact current size and scope

The reachable closure of `ElevenSquare.Optimality` contains **394,204 physical Lean lines, 6,326 local modules, and 1,087,162,218 bytes**. All local certificate sources are counted; Lean and Mathlib are excluded. The independent census found zero missing local imports, zero import cycles, and zero symlinked source files. See `simplification/checkpoint-census.json` for file hashes and import edges.

The imported checkpoint had 494,346 lines. This pass removes 100,142 reachable lines. **The 300,000-line goal remains unfinished.** Most exact numerical witness data remains, so the byte count is still about 1.09 GB. A smaller line count does not imply a faster kernel replay.

## Completed source changes

- Conditional coverage: shared bounded module contexts and removed 4,186 redundant intermediate aliases. Public coverage propositions retain their original certificate proofs; an exact source reconstruction audit passed.
- T07: shared `CTreeChain.build` reconstructs repeated binary split spines. All 22,931 transformed trees were expanded and compared with the original constructor tokens, including numerical witnesses and branch directions. The original tree checker remains in use.
- T07 stage proofs: removed repeated declarations around 3,303 width-eight checks; the same finite goals are now generated within each stage proof. This has not been replayed and may change elaboration memory use.
- T06: shared support lemmas for 1,734 zero-coordinate gradients and a common endpoint-polynomial reduction for 908 identities.
- Pending inventory: reused existing named tables rather than repeating literal tables; shared label lookup lemmas replace repeated append traversals.
- Ownership: one private singleton bridge replaces 134 repeated proofs, preserving all public statements and axiom queries.
- Endpoint: carried forward the previously focused-checked small-coefficient derivative decomposition from commit `1051254`.
- Restored `ElevenSquare.Verification` with axiom queries for the certificate families, global bound, and both final public theorems.

Source audits establish preservation properties, not Lean acceptance. New helper elaboration, regrouped modules, and all changed concrete certificates require replay.

## Run on the larger computer

With Git, Python 3, and elan installed, use an existing clone:

```sh
git fetch origin
git switch --track origin/codex/simplification-unverified-20261003
lake exe cache get
python3 scripts/check_sources.py
python3 scripts/verify.py --all --jobs 1 --keep-going
```

If the local branch already exists, switch to it normally. On Windows use `python` or `py` instead of `python3`. For a fresh clone:

```sh
git clone --branch codex/simplification-unverified-20261003 https://github.com/Queuingtheorydotcom/11SquaresFormalized.git
cd 11SquaresFormalized
```

The pinned toolchain is Lean **4.34.1** and Mathlib is **d13f23b723b8a846827a245b89c10fc7d3f11612**. Keep `lean-toolchain` and `lake-manifest.json`. **Do not run `verify.py --setup` or `materialize_wand125.py` on this branch**: they restore the older generated source layout.

The verifier compiles modules serially; `--jobs` controls Lean worker threads within each module. Start with one. Ctrl-C stops the current run; rerun the same command to reuse matching accepted receipts. Check `.verification/incomplete-result.json` and module logs for failures. Compilation may still require substantial RAM and time.

After the entire `--all` replay succeeds, validate the final current-source receipts and axiom reports:

```sh
python3 scripts/finalize_verification.py
```

Require `OPTIMALITY_PROVED`, zero admissions, and only the permitted standard axioms. Historical files under `verification/` and `simplification/accepted-components.json` do not certify this new checkpoint. Do not merge to main merely because source audits pass.

## What ran on the Mac

Before this latest source pass, the selected-field dispatcher and inventory classifier completed a focused replay: 83 modules and 20 standard-only axiom queries. A subsequent full replay stopped on request after 359 modules; the assembled theorem was never reached. Those earlier receipts do not certify subsequently changed files. All proof compiler processes were stopped before handoff; machine-local objects and logs are excluded from Git.

## Next simplification work

1. Diagnose any Lean failures in this checkpoint before building more abstraction on it.
2. Consider indexed stage data: an unapplied source-preservation dry run projected a further 16,593-line reduction across 267 cases, but it was deliberately excluded when work paused.
3. Explore exact reconstruction of T07 rational witnesses from supporting facet indices and geometry. A read-only Python pilot on the original `P2/S137C0` reconstructed all 3,618 multiplier vectors and matched 163 of 187 split planes to existing row edges. No corresponding Lean builder or additional line reduction is implemented or claimed here.
4. Recount the actual final theorem closure after each change. Preserve the packing model, final theorem statements, strict owned interiors, legal touching, and closed split boundaries. Do not replace proof checking with an external oracle.
