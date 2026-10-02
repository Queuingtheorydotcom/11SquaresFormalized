# Eleven-square packing in Lean

Upstream supplies **172 case-proof source archives**; case 1465 was its sole
omission and is now proved locally. **All 173 original full-case certificates
have actual named-target audits: 173/173, no original case remains.**

The [accepted case 1465 full audit](verification/t03-case1465-original-full65-accepted-checkpoint-20261002.json)
passed the unchanged pinned Lean 4.10.0-rc2 checker at 8 GiB with one thread.
All **65 exact targets**—64 route component targets and the original
`certificate_exists`—report only standard axioms. Exact actual audit source,
CHECK/log, task, accepted Certificate source/composition hash and genuine
source/receipt/object bindings are preserved. The old memory failure remains
recorded as history.

Both [genuine-cache postflights](verification/t03-case1465-independent-memory-retry-exact-live-cache-postflight-20261002.json) are now complete:
all **21,483 original, cached and visible object bindings** were checked with
zero mismatches. **The two public combined target audits and final return ZIP
remain pending.** This case completion does not claim global optimality or
fresh completion of those obligations. Earlier counts below describe dated
source snapshots, including the 172/173 and 159/173 stages.

The [final-source case 2122 recheck](verification/t03-final-case2122-private-recheck-checkpoint-20261002.json) passed the unchanged original checker and exact `certificate_exists` Std3 audit. **358 genuine compiler outputs and receipts** were integrated into the final route; source bytes were unchanged. Publication verified all 358 recorded receipt/closure bindings and the actual root object, without copying the object collection. This is an auxiliary check: the total remains **173/173**, and the two public combined audits and final ZIP are still pending.

The [final-source case 1775 recheck](verification/t03-final-case1775-private-recheck-checkpoint-20261002.json) preserved an actual Step197 memory failure at3GiB, followed by the same immutable-source/task retry at4GiB and a clean exact `certificate_exists` Std3 audit. **270 genuine outputs and receipts** were integrated; sources and the main checker were unchanged. The [current genuine import view](verification/t03-case1465-independent-final-current-genuine-import-view-20261002.json) selects **37,116 existing objects /7,082,132,976 logical bytes** by exact current source keys and genuine main receipt/object hashes. It changes future input paths with no bulk copies or proof jobs; no measured end-to-end speedup is claimed. The total remains **173/173**; the two public combined audits and exact final ZIP remain pending.

The [final-source case 2047 recheck](verification/t03-final-case2047-private-recheck-checkpoint-20261002.json) passed its exact original `certificate_exists` Std3 audit at one thread/4GiB; **227 genuine outputs and receipts** were integrated with unchanged sources. The [finite resource adapter](verification/t03-case1465-independent-final-two-thread-resource-adapter-20261002.json) changes only future main compiler invocations from one to two threads at the same8GiB limit; the auxiliary remains one thread/4GiB. The earlier one-thread import-view snapshot is retained as history, and no end-to-end speedup is claimed. The [prepared import-view postflight](verification/t03-final-current-genuine-import-view-postflight-preparation-20261002.json) remains gated on actual acceptance of both public targets. The total remains **173/173**; final public audits and the exact ZIP are pending.

The [additional exact-cache checkpoint](verification/t03-case1465-additional-cache-current172-checkpoint-20261002.json)
adds **9,642 genuine objects /1,894,518,368 bytes**, each bound to the current
dependency key and existing actual receipt. Recorded copy/original hash checks
have zero mismatches. The total is **21,483 of 21,510 objects**, with **27 original
path fallbacks**. The earlier 11,841-object cache is preserved; the new data uses
the existing D-backed ext4 volume. Source, original object and receipt bytes,
8 GiB memory and one-thread settings are unchanged. Only future input paths change.

PartnerReplayBatch013 and the Certificate module have fresh actual accepted
elaboration CHECK/log records. **Elaboration is not the 65-target axiom audit**;
that checkpoint preceded the complete full65 audit above. The final inherited audit is prepared to
bind its runtime to the actual successful final execution and verify frozen
source bytes against that transport. The report requires both cache postflights.
A dangling redundant scanner call was removed from staging, preserving the
mandatory original exporter/read-return scans and source guards. The runtime binding
and staging changes are preparatory. The full-case acceptance and completed
postflights are recorded above; public-target audits, a completed ZIP and a
whole-proof speedup are not claimed.


### Earlier 172/173 memory-retry snapshot

The following describes its earlier captured state; the fresh full65 acceptance
and cache postflights above supersede its pending-case status.

The [current memory-retry checkpoint](verification/t03-case1465-memory-retry-current172-checkpoint-20261002.json)
preserves a real 4 GiB memory failure in Chunk159, followed by an unchanged-source
retry at 8 GiB with one Lean thread. Chunk159 then passed elaboration in
**374.98 seconds**; Chunk179, Prefix012 and ReplayBatch000Retry01 also have real
accepted elaboration CHECK/log records. These checks do not complete the
65-target full-case axiom audit or either public combined target.

The input-path optimization selects **11,841 genuine, exactly closure-compatible
objects** and excludes **nine changed closures**. Recorded original/cache byte
validation, catalog/configuration hashes and metadata counts are bound; publication
did not rehash or distribute the 3.42 GB object collection. Subsequent checker
invocations use byte-identical eligible objects and original paths for uncached
or newly emitted objects. No source, compiler or receipt bytes were changed.
The actual full-case audit and cache postflight are still required; no same-claim
whole-proof speedup is claimed.

The final ext4 source workspace was prepared and checked with an eight-file byte
sample; **its future proof route remains untested**. Deferred duplicate staging
scans retain the mandatory original exporter validation. Finite bulk transfer
uses existing genuine receipts, and 17 inactive component transports were
preserved by exact recorded hashes. The cache postflight gate is preparatory;
the monitor's missing `re` import was repaired without restarting the proof
checker. None of these operational records adds a theorem or a completed ZIP.


The [current source-version checkpoint](verification/t03-current172-repaired-source-progress-checkpoint-20261002.json)
records **17/17 accepted case 1465 route components** at its captured controller
snapshot, including the final PartnerReplayBatch012 (steps 61–64).
Actual Batch010, Batch012 and Batch013 target audits are preserved with exact raw
CHECK/log, source-root, task and transport bindings. These are historical
component audits of the sources before the private identifier repair.

A private identifier was renamed from `initialize` to `initializePacking` in
18 reachable owned files. Original and repaired hashes, exact rename-only byte
changes and the post-repair source preflight were independently verified;
numerical data and public target signatures are unchanged. **The repaired
source tree still requires fresh audits**: the 65-target case 1465 audit and
two public combined target audits remain pending. Source preflight is not a
kernel proof or a successful final export. **No final return ZIP is complete.**

Older counts, including 159/173 below, describe dated historical snapshots;
they do not replace the 172 original-source audits or certify the repaired tree.
Publication added only compact metadata and exact audit logs, with no new
source archive, Lean job, worker control or source modification.

The earlier source snapshot has an **audited continuous prefix through step 40**:
Prefix012, corrected ReplayBatch000Retry01 (steps013–016), and
PartnerReplayBatch001–006 (steps017–040). The unchanged original checker
accepted all30 named component targets with standard axioms. This adds **no
full case**; case1465's original certificate and final public targets remain
pending. The [exact component checkpoint](verification/t03-case1465-independent-route-through40-source-release-20261002.json)
preserves84 actual CHECK/log pairs, accepted task/transport bindings, and a
[24.6 MB source supplement](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-1465-independent-route-through40-audited-20261002)
with78 exact IndependentReplay sources and63 small shared helpers. Its inherited
dependencies are hash-listed but omitted: **this supplement is not a standalone
source closure**. No fresh whole-ancestor object rehash or merged replay is claimed.

The accepted subset-cache trial/promotion is proof-neutral and supplies no
same-claim uncached timing comparison. The redundant alias trial was
intentionally cancelled (exit130); its last accepted State031 elaboration is
preserved, but no alias target audit or alias source belongs to the final route.
The final composition still waits for all17 required components. No whole-proof
speedup, full1465 certificate, public-target completion or return ZIP is claimed.


**Cases 1373 and 1464's immutable original full certificates passed** the unchanged
pinned Lean 4.10.0-rc2 checker, with only `propext`, `Classical.choice` and `Quot.sound`.
Case 1373: Main **105.04s**, Certificate **38.26s**, full audit **43.85s**.
Case 1464: Main **103.49s**, Certificate **46.48s**, full audit **52.37s**.

The [case 1373 accepted source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited171-imported1373-20261002) supplies **709 exact
modules /74,648,300 source bytes**. The [case 1464 accepted source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited172-imported1464-20261002)
supplies **713 exact modules /80,774,230 source bytes**, including
the actual accepted ReboundPrunedTrees root. [Complete source/object/audit bindings](verification/t03-wand125-case1373-accepted-source-release-20261002.json)
preserve every exact source member, genuine closure/receipt and actual object hash.
The earlier frozen case 1373 release retains its historical 171-count checkpoint.

Compact actual case 1465 component audits are also included: Partner01801
**50.72s compile /25.75s audit**, and steps 013–016 retry batch **206.79s compile
/57.06s audit**, all named targets using only the three standard axioms. These
checked components add no full certificate. Their complete source closures are
not distributed in that earlier metadata checkpoint. The current component
snapshot above supersedes its earlier pending status through step40; later
batches and case1465's whole proof remain pending. No whole-proof speedup is claimed.

The remaining case 1465 route now separates numeric states and individual
geometric steps. Its [route adoption](verification/t03-case1465-independent-replay-route-adoption-20261002.json) preserves the old source/proof
path and holds its queue reversibly. The [exact certificate composition](verification/t03-case1465-independent-certificate-composition-preparation-20261002.json)
is prepared and remains unverified; it requires all component audits before the
original full certificate check. A [finite 17-task transfer extension](verification/t03-case1465-independent-finite-file-transfer-promotion-20261002.json)
keeps the original checker, compiler and identity guards unchanged. The same
four-worker pool continues; these operational records add no proof acceptance.

Exact accepted source/task/pinned environment/checker bytes are preserved.
Main, earlier releases and live proof work are unchanged. Merged replay, the
public case-family theorem, global optimality and final return remain unfinished.
See [MISSING.md](MISSING.md) and [T03_PROGRESS.md](T03_PROGRESS.md).

## Historical proof-progress snapshots

All counts and pending/accepted source statuses in the dated snapshots below
describe their earlier source versions. The current checkpoint above is authoritative.

## Earlier accepted-case and geometric-pilot checkpoint

The following preserves its earlier 170-count snapshot; the two accepted full
certificates and component audits above supersede their earlier pending status.

Upstream supplies **172 case-proof source archives**; **only case 1465 is absent**.
We are reusing these supplied proofs. The separate original-project full
integration log now records **170/173**, with **1373, 1464 and 1465** remaining.

**Case 1393's exact original full certificate now passes** the pinned original
Lean 4.10.0-rc2 checker: Main **67.03s**, Certificate **40.14s**, actual full-target
audit **39.88s**, reporting only `propext`, `Classical.choice` and `Quot.sound`.
The [accepted audit/source bindings](verification/t03-wand125-case1393-full-original-audit-checkpoint-20261001.json)
and [complete exact source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited170-imported1393-20261001) contain
**680 modules /62,949,475 source bytes**, including 22 accepted PrunedTrees modules.
Every source member, genuine closure/receipt and actual object hash was verified.

Separately, the **case 1465 geometric Step012 pilot actually passed** in **82.71s**
compiling and **43.46s** auditing, with only the three standard axioms. Its
[complete pilot source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-geometric1465-step012-pilot-audited-20261001) includes
**1,389 exact modules /125,288,070 source bytes**. This checked geometric step
adds no full case certificate. All later replay batches and case 1465's full
certificate remain pending; no whole-proof speedup is claimed.

[Server-verified source assets and actual evidence](verification/t03-case1393-and-geometric1465-accepted-source-releases-20261001.json) preserve
exact task/source/environment/checker bytes and omit private runtime metadata.
Main, earlier releases and live proof work are preserved. Public family assembly,
merged replay, global optimality and final return remain unfinished.
See [MISSING.md](MISSING.md) and [T03_PROGRESS.md](T03_PROGRESS.md).

## Earlier numeric-pilot checkpoint

The following retains the earlier 169-count snapshot; accepted case 1393 above
supersedes its earlier pending integration status, and Step012 geometry above
supersedes the earlier pending single-step pilot status. Later steps remain pending.

Upstream supplies **172 case-proof source archives**; **only case 1465 is absent**.
We are reusing the supplied proofs. **169/173** is the separate count of completed
original-project full-certificate integrations. Cases **1373, 1393, 1464 and 1465**
remain in that integration log. The [refreshed upstream inventory](verification/t03-wand125-upstream-source-inventory-refresh-20261001.json)
records all supplied archives and their asset identities.

The **case 1465 numeric dependency-separation pilot actually passed** the original
Lean 4.10.0-rc2 checker: States **51.85s**, State012 **17.09s**, both target audits
**16.68s**. All 75 original numeric definition bodies are preserved. The terminal
numeric snapshot has only `propext`, `Classical.choice` and `Quot.sound`; the
Step012 state binding has only `propext` and `Quot.sound`.

The [complete accepted pilot source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-numeric1465-pilot-audited-20261001) includes **126 exact modules**
and **9,744,540 source bytes**, in a **3,086,131-byte ZIP**.
[Actual source/object/audit bindings](verification/t03-case1465-independent-numeric-state-pilot-source-checkpoint-20261001.json)
and byte-identical CHECK/log sidecars are published. This is a numeric/state-binding
pilot; the full geometric transition and case certificate remain pending. No
unverified geometric pilot is included, no full case is added and no whole-proof
speedup is claimed. Existing proof workers, `main` and earlier assets are preserved.

The public family theorem, merged replay, global optimality and final return
remain unfinished. See [MISSING.md](MISSING.md) and [T03_PROGRESS.md](T03_PROGRESS.md).

## Earlier inventory and cache checkpoint

The following preserves the earlier timestamped component/cache status.

Upstream supplies **172 case-proof source archives**; **only case 1465 is absent**.
The [fresh inventory](verification/t03-wand125-upstream-source-inventory-refresh-20261001.json) matches every archive
asset ID, size and digest to the upstream release and all 173 required cases.
We are reusing these supplied proofs. **169/173** is the separate count of
completed full-certificate integrations into the original project's contracts.
Cases **1373, 1393, 1464 and 1465** remain in that integration log.

At that earlier checkpoint, case 1465 had **175/253** accepted component groups;
its full certificate is pending. The byte-identical object-cache trial for
component 173 passed the unchanged original checker: **113.27 seconds** compiling
and **31.01 seconds** auditing, with only `propext` and `Quot.sound`.
The [compact checkpoint](verification/t03-inventory-and-bounded-cache-checkpoint-20261001.json) includes exact actual logs/CHECKs,
recorded pre/post identities for 11,850 original and cached objects, and four
routing negative controls. Adoption is bounded to components 175–252 and the
case 1465 full task, within the existing four single-thread worker limit.
No same-claim uncached comparison was obtained, so no speedup is claimed.

The public family theorem, merged replay, global optimality and final return
remain unfinished. See [MISSING.md](MISSING.md) and [T03_PROGRESS.md](T03_PROGRESS.md).

## Earlier source and audit checkpoint

The following preserves the earlier accepted case 1499 source publication.

Upstream supplies **172 case-proof archives**; **case1465 is the sole missing case
there**. The supplied proofs are being reused. The original-project full
certificate integration audit log is a separate metric and now records **169/173**.

**Case1499's exact original full certificate now passes** the pinned Lean
4.10.0-rc2 checker and actual target audit in **47.54 seconds**, reporting only
`propext`, `Classical.choice` and `Quot.sound`. Its [accepted audit/source bindings](verification/t03-wand125-case1499-full-original-audit-checkpoint-20261001.json)
and [complete exact source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited169-imported1499-20261001) include **716 modules
/48,429,336 source bytes**, with the actual accepted `PrunedTrees`
dependencies. Every source member, genuine source-closure key, receipt and
compiler-object hash was verified. Other pending conversion sources are excluded.

Supplied cases1373,1393,1464 and local case1465 remain
unfinished. Global optimality, original public family obligations and final
return are pending. Publication preserves merged proofs, `main`, earlier assets
and live proof work. See [MISSING.md](MISSING.md) and [T03_PROGRESS.md](T03_PROGRESS.md).

## Previous source and audit checkpoint

The following preserves its earlier168-count snapshot; accepted1499 above
supersedes its earlier pending1499 integration status.

Upstream supplies **172 case-proof archives**; **case1465 is the sole missing case
there**. The supplied proofs are being reused. The original-project full
certificate integration audit log is a separate metric and now records **168/173**.

**Case1463's exact original full certificate now passes** the pinned Lean
4.10.0-rc2 checker and actual target audit in **47.36 seconds**, reporting only
`propext`, `Classical.choice` and `Quot.sound`. Its [accepted audit/source bindings](verification/t03-wand125-case1463-full-original-audit-checkpoint-20261001.json)
and [complete exact source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited168-imported1463-20261001) include **687 modules
/39,475,043 source bytes**, with the actual accepted `PrunedTrees`
dependencies. Every source member, genuine source-closure key, receipt and
compiler-object hash was verified. Other pending conversion sources are excluded.

Supplied cases1373,1393,1464,1499 and local case1465 remain
unfinished. Global optimality, original public family obligations and final
return are pending. Publication preserves merged proofs, `main`, earlier assets
and live proof work. See [MISSING.md](MISSING.md) and [T03_PROGRESS.md](T03_PROGRESS.md).

## Previous source and audit checkpoint

The following preserves its earlier167-count snapshot; accepted1463 above
supersedes its earlier pending1463 integration status.

Upstream supplies **172 case-proof archives**; **case1465 is the sole missing case
there**. The supplied proofs are being reused. The original-project full
certificate integration audit log is a separate metric and now records **167/173**.

**Case1849's exact original full certificate now passes** the pinned Lean
4.10.0-rc2 checker and actual target audit in **41.49 seconds**, reporting only
`propext`, `Classical.choice` and `Quot.sound`. Its [accepted audit/source bindings](verification/t03-wand125-case1849-full-original-audit-checkpoint-20261001.json)
and [complete exact source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited167-imported1849-20261001) include **678 modules
/30,366,105 source bytes**, with the actual accepted `DirectTrees`
dependencies. Every source member, genuine source-closure key, receipt and
compiler-object hash was verified. Other pending conversion sources are excluded.

Five other supplied original-target integrations and local case1465 remain
unfinished. Global optimality, original public family obligations and final
return are pending. Publication preserves merged proofs, `main`, earlier assets
and live proof work. See [MISSING.md](MISSING.md) and [T03_PROGRESS.md](T03_PROGRESS.md).

## Two audited fixed-claim tree pilots

Both new pilots prove the same original coverage claim on the original pinned
Lean 4.10.0-rc2 checker, with only `propext`, `Classical.choice` and `Quot.sound`.
The [actual timing and audit/source checkpoint](verification/t03-wand125-pruned-coarse-tree-pilot-actual-comparison-20261001.json)
and [complete frozen source snapshot](verification/source-checkpoints/wand125-pruned-coarse-tree-comparison-20261001)
publish **20 modules /702,578 exact source bytes**, both tasks, byte-identical
actual compile CHECK and axiom-audit CHECK/logs, genuine source/object/receipt
bindings and historical preparation/proposal records. Publication independently
verified every immutable transport member, complete source key, object and receipt.

| Version of one coverage subtree | Nodes | Compile seconds | Axiom audit seconds | Compile + audit seconds |
| --- | ---: | ---: | ---: | ---: |
| Earlier direct pilot | 2,947 | 58.94 | 31.79 | 90.73 |
| Pruned spatial pilot | 1,295 | 31.76 | 26.89 | 58.65 |
| Coarse parent-leaf pilot | 823 | 27.83 | 30.47 | 58.30 |

The spatial pilot's observed compilation time is about **46% lower** than the
earlier direct pilot's. The coarse candidate compiles faster again, but its
observed compile-plus-audit total is only **0.6% lower than the spatial pilot**.
These are timings for one fixed coverage claim, with no whole-proof or broad
speedup inferred. Python preparation/proposal records retain their historical
unverified labels; actual kernel checks establish the two pilot claims separately.

No new full case is added: upstream inventory remains **172 supplied proofs**,
only1465 absent, and original-project integration remains **167/173**. Pending
pruned/rebound component variants are excluded. No Lean jobs, workers, queues,
canonical sources, `main` or prior release assets changed for publication.

## Previous source and audit checkpoint

The following preserves its earlier166-count snapshot; accepted1849 above
supersedes its earlier pending1849 integration status.

Upstream supplies **172 case-proof archives**; **case1465 is the sole missing case
there**. The supplied proofs are being reused. The original-project full
certificate integration audit log is a separate metric and now records **166/173**.

**Case1823's exact original full certificate now passes** the pinned Lean
4.10.0-rc2 checker and actual target audit in **38.80 seconds**, reporting only
`propext`, `Classical.choice` and `Quot.sound`. Its [accepted audit/source bindings](verification/t03-wand125-case1823-full-original-audit-checkpoint-20261001.json)
and [complete exact source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited166-imported1823-20261001) include **680 modules
/29,428,861 source bytes**, with the actual accepted `DirectTrees`
dependencies. Every source member, genuine source-closure key, receipt and
compiler-object hash was verified. Other pending conversion sources are excluded.

Six other supplied original-target integrations and local case1465 remain
unfinished. Global optimality, original public family obligations and final
return are pending. Publication preserves merged proofs, `main`, earlier assets
and live proof work. See [MISSING.md](MISSING.md) and [T03_PROGRESS.md](T03_PROGRESS.md).

## Previous source and audit checkpoint

The following preserves its earlier165-count snapshot; accepted1823 above
supersedes its earlier pending1823 integration status.

Upstream supplies **172 case-proof archives**; **case1465 is the sole missing case
there**. The supplied proofs are being reused. The original-project full
certificate integration audit log is a separate metric and now records **165/173**.

**Case1887's exact original full certificate now passes** the pinned Lean
4.10.0-rc2 checker and actual target audit in **40.87 seconds**, reporting only
`propext`, `Classical.choice` and `Quot.sound`. Its [accepted audit/source bindings](verification/t03-wand125-case1887-full-original-audit-checkpoint-20261001.json)
and [complete exact source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited165-imported1887-20261001) include **681 modules
/29,151,963 source bytes**, with the actual accepted `DirectTrees`
dependencies. Every source member, genuine source-closure key, receipt and
compiler-object hash was verified. Other pending conversion sources are excluded.

Seven other supplied original-target integrations and local case1465 remain
unfinished. Global optimality, original public family obligations and final
return are pending. Publication preserves merged proofs, `main`, earlier assets
and live proof work. See [MISSING.md](MISSING.md) and [T03_PROGRESS.md](T03_PROGRESS.md).

## Previous source and audit checkpoint

The following preserves its earlier164-count snapshot; accepted1887 above
supersedes its earlier pending1887 integration status.

Upstream supplies **172 case-proof archives**; **case1465 is the sole missing case
there**. The supplied proofs are being reused. The original-project full
certificate integration audit log is a separate metric and now records **164/173**.

**Case1891's exact original full certificate now passes** the pinned Lean
4.10.0-rc2 checker and actual target audit in **38.10 seconds**, reporting only
`propext`, `Classical.choice` and `Quot.sound`. Its [accepted audit/source bindings](verification/t03-wand125-case1891-full-original-audit-checkpoint-20261001.json)
and [complete exact source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited164-imported1891-20261001) include **672 modules /25,385,953
source bytes**, with four actually accepted `DirectTrees` modules. Every source
member, genuine source-closure key, receipt and compiler-object hash was verified.

The [two audited tree-comparison probes](verification/t03-wand125-direct-tree-pilot-actual-comparison-20261001.json)
also publish their exact sources and actual compile CHECK/audit outputs. For one
**2,947-node coverage subtree**, compilation took **80.56 seconds encoded versus
58.94 seconds direct**, about **27% less compilation time**. Both exact coverage
claims passed standard-three axiom audits; no whole-project speedup or acceptance
of the 191 pending conversion sources is inferred.

Eight other supplied original-target integrations and local case1465 remain
unfinished. Global optimality, original public family obligations and final
return are pending. Publication preserves merged proofs, `main`, earlier assets
and live proof work. See [MISSING.md](MISSING.md) and [T03_PROGRESS.md](T03_PROGRESS.md).

## Previous source and audit checkpoint

The following preserves its earlier163-count snapshot; accepted1891 above
supersedes its earlier pending1891 integration status.

Upstream supplies **172 case-proof archives**; **case1465 is the sole missing case
there**. The supplied proofs are being reused. The original-project full
certificate integration audit log is a separate metric and now records **163/173**.

The exact original full certificates for **cases2068,2069 and2070** now pass the
original pinned Lean 4.10.0-rc2 checker and actual target audits, reporting only
`propext`, `Classical.choice` and `Quot.sound`. Their
[accepted audit/source bindings](verification/t03-wand125-cases2068-2069-2070-full-original-audit-checkpoint-20261001.json)
and byte-identical CHECK/log sidecars are published with a
[new complete exact source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited163-imports2068-2069-2070-20261001): **690 modules /23,857,346 source
bytes**, including all 28 accepted `Combined` dependencies. Every source member,
genuine source-closure key, receipt and compiler-object hash was verified.

The [earlier 13-prepared-import source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-wand12513-imports-case2051-audit-20261001)
and accepted case2051 evidence remain frozen. Nine other supplied imports still
need their full original-target audits; case1465 continues locally. Global
optimality, original public family obligations and final return are unfinished.
Publication preserves merged proofs, `main`, earlier assets and live proof work.
See [MISSING.md](MISSING.md) and [T03_PROGRESS.md](T03_PROGRESS.md).

## Previous source and audit checkpoint

The following preserves its earlier160-count snapshot; the accepted three-case
checkpoint above supersedes its earlier pending2068/2069/2070 status.

Upstream has supplied **172 case-proof archives**; **case1465 is the sole missing
case there**. The supplied work is being reused. The [new portable source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-wand12513-imports-case2051-audit-20261001)
contains all **13 prepared imports**, including 762 case source members, 26
correspondence/certificate adapters and every reachable dependency: **1,477 Lean
modules / 308,797,584 source bytes**. Later `Combined` pilots are excluded.

Case2051 now passes the original project's full certificate audit on pinned
Lean 4.10.0-rc2. Its exact original `certificate_exists` target reports only
`propext`, `Classical.choice` and `Quot.sound` in 41.08 seconds. The
[accepted audit and complete 662-module source binding](verification/t03-wand125-case2051-full-original-audit-checkpoint-20261001.json)
includes actual CHECK/log bytes and independently verified genuine compiler
receipts/object hashes. Its exact sources are in the release ZIP.

The original-project full-certificate integration log is now **160/173**, a
separate metric from the **172 supplied proofs**. Twelve other supplied imports
still need their original full-target audits; case1465 continues locally.
Global optimality, the original public family obligations and final return are
unfinished. Existing merged proofs and `main` are preserved. See
[MISSING.md](MISSING.md) and [T03_PROGRESS.md](T03_PROGRESS.md).

The sections below retain historical checkpoints and their counts. Their
earlier pending-import statements are superseded by the current case2051 audit.

## Historical checkpoints

Upstream has supplied **172 case-proof archives**; **case1465 is the sole missing
case there**. The 13 supplied archives needed for the remaining imports have all
been source/member verified. The **159/173** figure below is the original
project's full-certificate integration audit log, a separate metric from the
172 supplied proofs. The supplied proofs are being reused.

New [audited import components and deduplicated exact source snapshots](verification/source-checkpoints/wand125-pinned-import-components-20261001)
include Branch, the first trees for cases2051 and1849 trees and both original mask correspondences.
The bounds proofs have no axioms; mask equalities and the other component targets
use only the standard three. Complete imported cases remain under integration.

This repository assembles the completed foundations and the available partial
formalizations of the optimal eleven-square packing. **Global optimality is
still unfinished.** Six explicit `sorry` sites record the remaining obligations.
A build that accepts those sites checks the surrounding code but does not prove
the final optimality theorem. See [MISSING.md](MISSING.md).

At this checkpoint, the original-project integration log records **159/173**
full certificates with exact accepted target audits and published closures.
Thirteen of its remaining integrations already have supplied upstream case
proofs; case1465 is the one unsupplied upstream case.
The complete ordinary shared exclusion checker now passes the original pinned
Lean 4.10.0-rc2 checker: `SquarePacking.S11Opt.Split.U2P.excluded_of_tris`, the
majority lemma and three field-bridge targets have actual standard-three axiom
audits. Their [exact audit evidence and 17-module frozen source closure](verification/source-checkpoints/wand125-pinned-exclusion-checker-20261001)
are published separately from newly imported unaudited `Branch` and case sources.
This supersedes the earlier shared-checker-pending status. Actual finite case
probes and imported full-case audits remain pending; historical count at this checkpoint was **159/173**.

Cover, box-tree and field-tree compatibility now have four additional accepted
targets under the original Lean 4.10.0-rc2 checker, all with the standard three
axioms. Their [exact audit evidence and nine-module source closure](verification/source-checkpoints/wand125-pinned-cover-trees-20261001)
are frozen separately from mutable pending checker work. Root also verified
[all 13 available remaining source archives](verification/t03-wand125-all-thirteen-pending-source-archives-checkpoint-20261001.json):
762 source members / 341,699,241 bytes. Source availability does not add an
accepted case. The historical count at this checkpoint was **159/173**; case1465 has no upstream source archive,
and imported full-case audits remain pending.

The conditional original-contract transport now passes the supplied checker on
Lean 4.10.0-rc2: `ElevenSquare.Pending.T03.Wand125.certificate_of_case` reports
only the standard three axioms. Its [actual audit](verification/t03-wand125-pinned-original-transport-audit-checkpoint-20261001.json)
and [isolated 25-module source closure](verification/source-checkpoints/wand125-pinned-original-transport-20261001)
preserve the original geometry, cell-mask and certificate statements exactly.
Cell bounds, exact case-mask correspondence and a proved case exclusion remain
explicit per-case inputs. No imported case is accepted; the count remains
**159/173** and concrete imported case proofs remain pending.

The reused S11 basic lemmas and the original packing bridge now also pass
the original pinned checker: `SquarePacking.S11Opt.peQ_pos_of_hIv`,
`SquarePacking.S11Opt.disjoint_of_dir` and
`ElevenSquare.Pending.T03.Wand125.packing_to_packs` report only the three
standard axioms. The [S11 audit](verification/t03-wand125-pinned-s11-basic-audit-checkpoint-20261001.json),
[geometry audit](verification/t03-wand125-pinned-original-geometry-audit-checkpoint-20261001.json)
and [small standalone source snapshot](verification/source-checkpoints/wand125-pinned-shared-core-20261001)
publish their exact accepted versions and checker evidence. No imported case
is accepted; the full-case historical count at this checkpoint was **159/173**.

Shared-core compatibility now has actual **Lean 4.10.0-rc2** audits: the
original checker accepted `SquarePacking.sq_subset_box_iff`, `lemmaG_box`,
`mem_sq_scale_iff` and `mem_sqInt_scale_iff`, each using only `propext`,
`Classical.choice` and `Quot.sound`. The [core audit](verification/t03-wand125-pinned-core-audit-checkpoint-20261001.json)
and [packing audit](verification/t03-wand125-pinned-packing-audit-checkpoint-20261001.json)
bind their exact adapted source versions, genuine receipt/object hashes and
unaltered CHECK/log bytes. This checks shared core only: no imported case has
been accepted. Concrete per-case checker proofs and contract instantiations
remain pending; the full-case historical count at this checkpoint was **159/173**.

New upstream sources are now available in [wand125's `n11-certs-v1` release](https://github.com/wand125/n11-optimality-lean/releases/tag/n11-certs-v1):
172 U2R case archives include **13 of our 14 remaining cases**; case1465 is absent.
Case1849's [source archive](https://github.com/wand125/n11-optimality-lean/releases/download/n11-certs-v1/n11-u2r-C1849.tar.xz)
and all 54 source members match its archive checksum and manifest. Import,
concrete original-contract case instantiations and actual case target audits are **pending**;
the local accepted historical count at this checkpoint was **159/173**. Thirteen duplicate local native
producers were checkpointed at complete publication boundaries and their queues
preserved for reuse. Existing Lean checks were allowed to finish normally;
case1465 continues locally. See [source provenance](verification/t03-wand125-source-release-availability-20261001.json)
and the [preserved hold checkpoint](verification/t03-wand125-local-duplicate-hold-20261001.json).

A measured multi-target experiment retained the same 278-member source/environment
fixture (270 Lean modules) and exact target union: one combined actual audit
took **27.16 seconds**, versus **26.12 + 20.90 = 47.02 seconds** for fresh separate
audits. This is one background-pool fixture observation. The first case1463
production pair also passed both original target audits and genuine source/object
receipt checks; it verifies two dependency groups, with no production timing
speedup claim or new full certificate. See [experiment evidence](verification/t03-multi-target-audit-experiment-20261001.json)
and [the first production pair](verification/t03-case1463-production-pair-checkpoint-20261001.json).
Pairing remains optional; every full case and both public targets still need
their original audits. The historical count at this checkpoint was **159/173**.

Case1731's exact full certificate now passes too: its actual audit took 90.39
seconds and uses only `propext`, `Classical.choice` and `Quot.sound`. Publication
independently checked every one of its 2,831 original and portable Lean members,
the complete import closure, task, environment and checkers. Its [accepted
audit/source sidecar](verification/t03-case1731-accepted-source-audit.json) binds
the existing immutable source ZIP; its original pending history is preserved.

All 14 remaining cases retain prepared local dependency queues; thirteen are
currently held for upstream source reuse. Their previously checked first-group actual
audits are checked in the [timestamped queue checkpoint](verification/t03-local-queues-checkpoint-20261001.json); group counters remain partial observations.
Selecting the same 35 ready tasks from 4,361 unattempted queue rows took 15.761
seconds before a source-archive prefilter, 1.547 after and 1.543 on repeat. This
measures controller task selection, not Lean compilation. The six-slot limit
and ordinary source/object validation remain. See the [scheduler evidence](verification/t03-ready-archive-prefilter-checkpoint-20261001.json).

Case1372's full audit now passes with only `propext`, `Classical.choice` and
`Quot.sound`. Its exact 2,351-module source closure is already in the [frozen
binding-retry02 source asset](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/download/t03-pending-equality-retries-20261001/T03-pending-case1372-binding-retry02-source-checkpoint.zip).
The new [accepted audit sidecar](verification/t03-case1372-accepted-source-audit.json)
binds every Lean member and the unchanged task, environment and checkers to that
immutable source ZIP. Its original pending packaging record is preserved.
The public returned-family proofs, combined repository replay and final return
ZIP remain unfinished. Only case2135 is directly integrated here; source assets
must be extracted separately from stronger merged interfaces.

Case1499's remainder is prepared as 72 dependency groups across 22 levels after
26 actually checked prefix groups. All 26 prefix source bytes, the original
exact target and numeric data are preserved. Its new ordinary equality proof
constructions and full certificate audit remain pending. The 22 levels are a
dependency plan, not a measured speedup. A separate portable source snapshot
is published with all 3,010 local source modules, exact original checkers
and pinned Lake files; publication details are in [T03_PROGRESS.md](T03_PROGRESS.md).
The [new progress release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-progress-158-case1499-remainder-20261001) also supplies case1372's accepted audit sidecar. Case1499's first new group,
`Chunk015`, has since passed its exact group target audit; this partial check
does not complete case1499. Case2051's 291-group preparation is also locally eligible with a two-live-archive
bound in the existing six-worker pool; this checkpoint includes compact pending
metadata only, without another case2051 source asset or acceptance claim.

The [original accepted release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited-151-20260930)
retains its 151-case base and six source supplements, supplying the first 157
accepted case closures. The [earlier pending sources](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-pending-case-retries-20261001),
[four later source versions](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-pending-equality-retries-20261001),
and frozen case1465 [Chunk106](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-pending-case1465-retry02-20261001)/[Chunk105](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-pending-case1465-retry03-20261001)
supplements remain unchanged. Their pending labels describe the time each
source version was packaged; only the exact case1372 retry02 version has since
passed its full target audit. Other partial group checks add no full cases.

Checked common tools include a center-distance collision shortcut, ordinary
kernel-checked Boolean and equality-reflexivity tactics, and case2135's complete
source closure. The equality helper reduced one eight-proof sample from 7.039 to
4.368 seconds, with a rejected false-equality negative control. Native source
synchronization measured 3.734 versus 11.665 seconds on the same 381-member
fixture; this measures source I/O. Actual proof-job source sync and exact limits
are documented in [T03_PROGRESS.md](T03_PROGRESS.md). Publication itself started
no Lean replay or worker and left all existing proof jobs untouched.

A new [homogeneous polygon fan helper](ElevenSquare/Tasks/T03/HomogeneousPolygonFan.lean)
proves that positive-denominator integer checks imply the same original rational
`polygonFanCheck`. Its three generic targets passed actual standard-three axiom
audits. Both proofs in an identical 56-vertex comparison also passed: rational
module 33.28 seconds, integer module 34.23 seconds. This sample showed no saving;
the optional helper has not been applied to pending case sources. See its
[source and audit provenance](verification/t03-homogeneous-fan-helper.json).
The frozen case1465 Chunk105 supplement has now passed its group target audit;
its full case remains pending. At that helper checkpoint, the accepted full-case count was **158/173**.

The target side length is the exact real number

\[
T = \frac{6u+4}{1+2u-u^2},
\]

where `u` is the unique root in `(9/25,37/100)` of

\[
5u^8-10u^7-2u^6+14u^5+12u^4-6u^3+2u^2+2u-1=0.
\]

The construction attains approximately `3.8770835900228141773`. The model allows
arbitrary orientations, legal boundary contact, and disjoint open interiors.

## Entry points

| File | Purpose |
| --- | --- |
| `ElevenSquare/Foundations.lean` | Geometry, the exact endpoint, attaining construction, closed-cell cover, and finite case reduction. |
| `ElevenSquare/Progress.lean` | Completed baseline groups, case1000 through two steps, and selected global capture helpers. |
| `ElevenSquare/Pending/` | Public interfaces and the later proof stages, with explicit remaining dependencies. |
| `ElevenSquare/Tasks/` | Returned certificate data, generic checkers, analytic lemmas, and concrete partial proofs. |
| `ElevenSquare/Optimality.lean` | Final unconditional theorem statements; their proofs currently inherit the listed admissions. |
| `ElevenSquare/Verification.lean` | Axiom queries for completed milestones and unfinished public targets. |

## Verification

Install Git and Lean's `elan` launcher. The project pins Lean `v4.10.0-rc2` and
mathlib revision `3fef63ff3bda38478ba4364ff03999f0246745a2`.
Keep `lake-manifest.json`; do not update dependencies while reproducing this
snapshot.

Set up the public dependencies, compile the main dependency chain serially,
and inspect its target axioms with one command:

```sh
python3 scripts/verify.py --setup
```

For every included source module, including progress outside the main chain:

```sh
python3 scripts/verify.py --setup --all
```

Once dependencies are installed, omit `--setup`. Accepted unchanged modules
can be resumed using the script's source/object/dependency fingerprints. Add
`--fresh` to rebuild every selected local module. These are substantial exact
certificate checks and can take a long time. They use ordinary Lean checking;
no packing search or external algebra system is required.

A source-only check, requiring only Python3, is:

```sh
python3 scripts/check_sources.py
```

`--plan` on the verifier prints the compilation order without running Lean.
Build logs and objects remain in ignored `.verification/` and `.lake/` folders.
The normal Lake entry point is also available via `lake build`.

The verifier distinguishes clean milestones, which may use only `propext`,
`Classical.choice`, and `Quot.sound`, from the explicit unfinished targets.
Success with the current six admissions is **partial assembly success**, not a
proof of optimality. Closing those admissions requires a fresh final audit.

## Assembly provenance

The source incorporates the baseline partial return, the checked prior-support
continuation, the local-packet return, and the global partial handoff. It also
preserves the previously integrated fixes to the overlay and D4 bridge from the
earlier current-work return. Older unreferenced speculative modules are omitted;
all delivered Lean modules and their local source dependencies are preserved.

`verification/source-inventory.json` records exact source hashes and which files
match supplied compiler inventories. `verification/imported-audits.json` retains
only mathematical declaration names and their reported axiom sets. It is
historical evidence, not a fresh combined compiler replay. In particular, a
reported inherited admission may have been removed by another merged return.

The assembly was checked for a complete local import closure, exact admission
inventory, matching returned source hashes, and personal information. The small
final composition is checked separately against the existing shared interfaces.
The entire large numerical certificate collection is supplied for reproducible
replay rather than claimed freshly rebuilt during packaging.

Only portable source, pinned public dependency metadata, mathematical audit
summaries, and fresh documentation are distributed. Original handoff archives,
conversation records, machine diagnostics, private project identifiers, and
historical machine-specific logs are omitted.
