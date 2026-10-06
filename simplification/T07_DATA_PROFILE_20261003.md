# T07 certificate data reductions and determinant-checker pilot

This is a source analysis of the active theorem closure at `b62bfd079d795971152cea3e051b057886c75d6a`. It does not establish full Lean acceptance or a complete-build runtime. The active T07 extension sources occupy 693,947,360 bytes; the entire theorem closure occupies 1,085,849,057 bytes.

The combined trimming pass below has now been applied to all 459 stages. The refreshed active T07 extension occupies 659,207,985 bytes, and the entire theorem closure occupies 1,051,109,682 bytes. The 365,392-line and 4,257-module counts are unchanged. The before/after source hashes and exact inverse edits are in `t07-certificate-trimming.json`; all 459 final files pass its inverse/recomputation audit. The original bundle ledger is unchanged and is checked after undoing this later layer.

## Removing work from existing certificates

The structural audit visits only the Farkas weight fields in the 24,908 literal `certN : List Sub` declarations across 459 active stage files. It follows every supported cover-tree constructor, including triangles and chained splits, while preserving geometric data, row and partner indices, outer weight-list lengths, closed intervals and split boundaries.

| Candidate | Exact source reduction | Eliminated data/checks |
| --- | ---: | --- |
| Remove trailing zero Farkas weights | 29,821,655 bytes | 5,964,331 zero weights in 604,636 vectors |
| Clear unused collision cores when the region list is empty | 4,917,720 bytes | 20,152 unused core lists and their vertex checks |
| Combined | 34,739,375 bytes | Both changes above |

There are 608,949 audited vectors. The first transformation reduces their entries from 8,495,979 to 2,531,648, a **70.2% reduction**. The existing `comb` function stops when either list ends, so an omitted zero suffix contributes exactly the same zero half-plane. The nonnegativity check is unchanged, and no inner-list length is required by `impliesB`, `emptyB` or `subsetB`.

`Sub.ccore` is used geometrically only by `Sub.regs`. When that list is literally empty, the original core still triggers vertex-validity checks but has no geometric consumer. The optional second transformation replaces that unused field with `[]`; the original checker still validates the candidate certificate. This is not a claim that arbitrary previously failing certificates have the same Boolean result.

These transformations remove data and checks instead of adding runtime arithmetic reconstruction. They leave the checker and its soundness proofs unchanged. They still require ordinary Lean acceptance of the resulting generated certificates. The source reduction is about 5.0% of the T07 extension bytes, while the larger weight-count reduction is a more relevant runtime opportunity; neither number predicts full compilation time.

For the production P2/S135 module, the combined candidate removes 43,791 bytes from 556,032 bytes. The standalone frozen benchmark additionally embeds the required state context: it shrinks from 678,405 to 634,614 bytes. Both delete 5,931 of 13,143 weight entries and clear 76 unused collision-core lists. This stage has a smaller weight reduction than the whole active population.

The transformer is `scripts/trim_t07_zero_tails.py`. Its default is a read-only proposal. `--clear-unused-cores` enables the second transformation. Receipts bind the before/after source hashes and checker hash, and include exact inverse edits. `--check RECEIPT` restores the original bytes and recomputes the transformation. `--apply-receipt RECEIPT` preflights the complete batch, then atomically replaces each file, accepting an exact mixture of original and candidate files to recover after interruption. Twenty-one tests cover structural field selection, every tree constructor, short and overlong Farkas lists, exact rational combination preservation, inverse corruption, unused-core selection and interrupted-application recovery.

## Kernel checks and runtime evidence

The frozen S135 test checks all 38 input rows and 76 subrows and derives the same `ExtStep prev (replaceRows prev 0 rs)` conclusion. It embeds the state entries read by this pruning step. It does not certify the production state history, promotion, or full theorem.

The original-checker scout accepted both the original and combined-trim inputs: 49.700244 versus 42.135205 CPU seconds. This is a single observation for each, not a reproducible whole-corpus speed claim. The records are in `t07-certificate-data-scout.json`.

The optional `DirectSupport` and `DirectTree` helpers use one- or two-facet indices instead of huge rational weight vectors. Two-facet implication is checked using signed determinants and a scaled bound, with no division or weight reconstruction. Triangle barycentric data, closed splits, owner checks and the final geometric conclusion are retained. Both helper modules and their soundness proofs passed Lean; the reported axioms are only `propext`, `Classical.choice` and `Quot.sound`. This checker is **not enabled in the active proof**.

The direct checker combined with unused-core removal passed two mirrored trials. Median CPU time fell from **51.775641 to 36.3148995 seconds**, a **29.9% reduction**, while the standalone input source is about **46% smaller**. Original trials took 54.013742 and 49.537540 CPU seconds; direct trials took 36.434618 and 36.195181. Wall timings were noisier under memory pressure, so CPU time is the primary comparison. Exact input hashes, resource bounds and results are in `t07-certificate-data-benchmark.json`; helper source/object fingerprints are in `t07-direct-helper-checks.json`.

Reproduce on a machine with sufficient memory and disk:

```sh
python3 scripts/verify.py --jobs 1 --module ElevenSquare.Tasks.T07.Ext.DirectTree
python3 scripts/benchmark_t07_certificate_data.py --variants direct_core --repeats 2
python3 scripts/benchmark_t07_certificate_data.py --variants tail_core --repeats 2
```

The benchmark runs one compiler at a time, caps its Lean memory setting and elapsed time, stops if free disk drops below 2 GiB, reaps interrupted children, and writes no compiler objects. It never changes production sources. Initial trials at a 1,536 MiB Lean limit exhausted the limit before checking the baseline; successful comparisons used 3,072 MiB. Neither result establishes a 2–3 hour whole-proof build.

The next direct-checker rollout must read certificates from merged stage files, reconstruct the actual input polygons, validate support determinants/signs/bounds with exact rationals, and keep literal fallback for dependent facet pairs. Two nonzero weights alone do not guarantee a nonzero determinant. Preserve the public pruning/trace statements and audit external certificate consumers. The existing state reader can handle later P2 stages; initial `siteSeedFor roleCell` rows need an exact seed evaluator. Broad conversion remains pending, and the full theorem still requires replay.

## Sharing literal data: lower priority

A separate lexical survey found smaller opportunities to share exact repeated literals. These are estimates using an eight-character reference and 32 characters of declaration overhead, not emitted or Lean-checked changes. They overlap and must not be added together.

| Sharing unit | Estimated bytes saved | Added constants |
| --- | ---: | ---: |
| Repeated rational atoms within each module | 56,070,551 | 470,980 |
| Rational atoms, keeping only gains over 500 bytes | 23,787,296 | 17,510 |
| Repeated rational points within each module | 27,218,794 | 27,118 |
| Repeated rational vectors within each module | 7,428,421 | 14,104 |

Exact repeated complete certificate expressions account for another 11,266,356 duplicate source bytes globally: 24,908 expressions have 22,812 distinct bodies. Sharing them does not remove their separate contextual checks. In particular, a smaller source file from adding shared constants does not establish less kernel arithmetic. These routes should follow measured reductions that delete actual checks.

Promotion and partner-cover weight lists are deliberately excluded from the structural transformation above. A broader lexical scan saw 782,989 rational vectors and 6,834,497 trailing zeros, so typed handling of those additional certificate structures may expose further savings. Such a scan is not sufficient authorization to edit those fields.
