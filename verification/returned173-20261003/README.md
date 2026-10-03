# Independent Returned-173 acceptance

On 2026-10-03 at 06:28:29 UTC, the complete Returned/native path at
`1dae90961450215ee5e507b30632361a5d126dfc` passed Lean 4.34.1 compilation and
actual transitive axiom queries. This is an independent replay of the existing
upstream proof sources. It adds no proof, certificate data, semantic changes or
source wiring. It does not establish global optimality or accept unrelated
baseline, prior or case438 paths.

The checked path is:

`SquarePacking.S11Opt.Split.returned_excluded` →
`ElevenSquare.Interop.Wand125.returned_certificate` →
`ElevenSquare.Pending.returned_certificate_exists` →
`ElevenSquare.Pending.returned_excluded`.

## Evidence

- [acceptance.json](acceptance.json): exact source/compiler/package pins,
  173 case identifiers including 1465, release hashes, result scope, resource
  observations, historical checkpoints and evidence digests.
- [module-fingerprints.tsv](module-fingerprints.tsv): all 5,616 checked modules,
  distinguishing 5,556 reused dependencies from 60 freshly checked modules.
  Columns identify source bytes, compiled object, recursive input fingerprint
  and retained receipt. These are provenance identifiers, not proof certificates
  usable without their actual matching objects and inputs.
- [Axioms.lean](Axioms.lean) and [axioms.txt](axioms.txt): the actual query source
  and its complete 177-line declaration/axiom output (four path declarations and
  all 173 per-case exclusions). Every query contains only `propext`,
  `Classical.choice` and `Quot.sound`. Compilation and the query process both
  exited zero. Published text uses LF line endings; `artifact_sha256` identifies
  those portable bytes, while `raw_output_sha256` identifies the retained original
  output. Machine paths and operational logs are not published.

Reuse required exact matching source bytes, Lean compiler identity, compiler
arguments, three build-context hashes, direct dependency object hashes and
recursive dependency input digests. All nine package pins and 35,668 external
objects were checked before transfer. Objects and logs were copied individually;
receipts were rebuilt with provenance after validation. The accepted dependency
prefix was not recompiled. The 60 fresh checks include the reconciled aggregate
and native wrappers, and all exited zero. The input fingerprint algorithm is
`sha256(json.dumps(receipt["inputs"], sort_keys=True).encode())`, as implemented
by the pinned upstream verifier.

The original 172-case checkpoint and incremental C1465 checkpoint are retained
separately, together with the frozen component replay. That earlier aggregate
needed a declaration-scoped `maxRecDepth 2048` compatibility setting. This is
historical provenance only: the reconciled replay used the unchanged upstream
aggregate with its own `maxRecDepth 100000` setting. No `2048` patch was carried
forward. A separately hashed, read-only local snapshot preserves the successful
reconciled sources, receipts, objects, compile output and axiom output. Such
local file protection is not a claim of tamper-proof storage.

## Replay method and reproducibility

The recorded replay intentionally materialized only the Returned generated
sources. Its local preflight adapter replaced the upstream all-repository
lexical check with a check of the complete 5,616-module Returned/native import
closure. It used the upstream lexer, recorded every source hash, verified each
dependency edge against the closure plan, and rejected `sorry`, `admit`, `sorryAx`, custom
`axiom`, `native_decide` and `unsafe` code tokens. It verified an empty admission
inventory. The upstream compiler invocation, receipt validation, dependency
scheduling and axiom auditing code were unchanged. This was not a successful
whole-repository source preflight or full-proof replay.

A fresh independent reproduction can use the stock verifier without that local
adapter: restore the sources required by its broader source preflight, then
select only the Returned/native closure. In a separate clean checkout at the
exact accepted commit, with the pinned Lean toolchain available:

```sh
python3 -X utf8 scripts/verify.py --setup --jobs 1 --max-parallel 1 \
  --module Sqpack.S11Opt.Split.U2Returned \
  --module ElevenSquare.Interop.Wand125.Families.Returned \
  --module ElevenSquare.Pending.S06_Returned
```

`--setup` uses the repository's pinned restoration process and can download
generated families outside Returned to satisfy the repository-wide preflight;
those families are not thereby compiler-accepted. Inspect the pinned
[release restoration instructions](../../integrations/wand125/release/README.md)
and available storage before running it. On Windows, use the pinned Python
interpreter with `-X utf8` and enter the command on one line.

Copy the published `Axioms.lean` into that checkout (the evidence directory is
an addition after the accepted commit), then run:

```sh
lake env lean -j1 Axioms.lean
```

Require zero exits, the complete 5,616-module selected result and all 177 named
axiom outputs. Compare the query output with `axioms.txt`; missing output is not
PASS. Source hashes should match the table. Object and compiler executable
hashes are platform/build specific: differing fingerprints invalidate receipt
reuse and require checking the affected dependency closure, not replacing
expected hashes. Static checks and this published report cannot replace Lean.

Only one compiler was used in the reconciled replay. Earlier four-lane checking
reached 99% physical-memory load; the later lower load does not erase that peak.
Resource figures in `acceptance.json` are sampled observations, not guaranteed
continuous maxima or a performance prediction for another machine.

## Upstream reconciliation

The inspected stronger-computer tip `1dae90961450215ee5e507b30632361a5d126dfc`
and single-node tip `5f03579427807e9d199bff215c0bb08bac459d76` (which contains
`6768d4cc`) have identical tracked Lean sources, build pins and core verifier
code. Neither branch supersedes the other. Their differences concern deployment,
verification infrastructure and generator tooling; this report does not certify
new generator outputs. The stronger-computer branch was chosen because current
integration PRs #5 and #6 target it. Already-present Returned wiring was retained
unchanged. This acceptance belongs to the exact source commit and fingerprints,
not automatically to future branch tips.
