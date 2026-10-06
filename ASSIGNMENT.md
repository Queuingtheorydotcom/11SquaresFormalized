# Who is working on what

A small table to avoid duplicated work on the six remaining `sorry` sites (see
[MISSING.md](MISSING.md)). Before starting on an obligation, check this table; if it is free, add your
name in the same commit or PR as your first piece of work. Please keep the status line short and
update it when something lands.

Status as of 2026-10-02 (updated 06:10 JST). @wand125 updates its rows frequently.

| obligation | file | who | approach | status |
|---|---|---|---|---|
| baseline: `planData`, `program_calculations`, `leaf_calculations` (1,931 cases) | `Tasks/T01/Handoff/` | @wand125 (field + generic) | box-tree certificates checked by the kernel against a checker proved sound once ([wand125/n11-optimality-lean](https://github.com/wand125/n11-optimality-lean), branch `split`), passed through `Interop/Wand125` | generic: 27/27 and field: 1,904/1,904 kernel-checked (`excludedField_all`, standard axioms only); generated data in the release [n11-certs-v1](https://github.com/wand125/n11-optimality-lean/releases/tag/n11-certs-v1) |
| prior: `prior_certificate_exists` (76 cases) | `Pending/S06_PriorSupport.lean` | @wand125 | same (owned-hull induction with box trees); passed through `Interop/Wand125` | 76/76 kernel-checked (`prior_excluded`, standard axioms only), also re-checked on the Lean 4.34.1 branch; data in the same release; PR in preparation |
| returned: `returned_certificate_exists` (173 cases) | `Pending/S06_Returned.lean` | @wand125 (box trees) · @Benjamin-Gurevitch (T03 traces) | two independent routes | box trees: 172/173 kernel-checked; the last case, 1465, is now generated and in the kernel check. T03 traces: 154 audited (`t03-proof-progress-20260930`, Lean 4.10). All 19 cases open in T03 are covered by the box trees |
| case 438: `case438_near_certificate` | `Tasks/T07/UnfinishedCapture.lean` | @wand125 | data-driven checker for the T07 step semantics (proved sound once), with the author's capture data converted to `VerifiedStep` traces; added as new files only | Phase-2 root induction route in place (author's 14 rounds, ownership hulls matching the author's records); all 464 steps of the case-438 tree generated and the Lean build is running, no errors so far; near rows next |
| upgrade to Lean 4.34 and integration | whole repository | @Queuingtheorydotcom | `codex/import-wand125-progress` | in progress |
| | | *(free)* | e.g. independent cross-checks, a second route for the last returned cases, preparing n = 17 | |

## Conventions

- Work happens on branches; changes reach `main` through pull requests reviewed by @Queuingtheorydotcom.
- Large generated certificate data is not committed. Generators, small search hints and a MANIFEST
  (SHA-256) are committed; the data itself is attached to GitHub releases, so it can be either
  downloaded or regenerated and then checked by the kernel.
- No new `sorry`, `axiom` or `native_decide`; existing public statements are preserved.
