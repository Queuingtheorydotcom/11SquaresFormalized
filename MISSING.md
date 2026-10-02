# Remaining proof obligations

Six explicit `sorry` sites remain. The exact files and line numbers are recorded
in `verification/admissions.json` and checked by `scripts/check_sources.py`.
They are intentional placeholders, not certified conclusions.

## 1. Complete the baseline case family

Three sites under `ElevenSquare/Tasks/T01/Handoff/` remain:

- `PlanData.lean:planData`: provide the full finite ancestry and branch plans.
- `ProgramCalculations.lean:program_calculations`: check cores, walls, coverage,
  ownership, interval coverage, and exact predecessor links for those plans.
- `LeafCalculations.lean:leaf_calculations`: prove every terminal leaf closes.

The reduced inventory covers all 1,931 baseline indices with 71 selected groups.
Groups G003, G004, and G007 are already integrated into the dispatcher; their
completed certificates cover 1,132 distinct required cases. The other 799 cases
remain outside that completed union. The number of cases is not an estimate of
remaining computational effort.

The return also includes all 188 shared owned-point proofs, uniform wall and core
lemmas, shared Bernstein sign certificates, finished parts of G005, and partial
G070 transitions. Conditional transitions do not complete an initialized program.
In particular, G005's completed cells and G070's terminal certificates cannot be
used to assert a whole group exclusion before their remaining links are proved.

The public `baseline_certificate_exists` and `baseline_excluded` preserve their
original statements and inherit the three private admissions. Their definitions
of the packing, closed cells, masks, and trace semantics are unchanged.

## 2. Complete the prior-support family

`ElevenSquare/Pending/S06_PriorSupport.lean:prior_certificate_exists` remains
admitted. It requires an initialized `VerifiedTrace` ending in `Terminal` for
all 76 prior indices. Its original baseline-exclusion premise is deliberate.
Early D4 cuts must use that premise, without appealing circularly to the final
symmetry or optimality result.

Case1000 is proved through archived steps0 and1. The checked continuation
establishes genuine predecessor/self-cut implications, all 64 closed rows in
step1, normalized integer coverage, strict ownership promotion, preservation of
the owner permutation, and transport to the exact archived outer state.

For the straightforward full case1000 chain, nonterminal steps2–11, linkage of
terminal step12, and the final contradiction still remain. The other cases also
need their full ancestry, refined intervals, branch coverage, and special
collision/support mechanisms. Existing conditional terminal-row results are
useful components, not a complete case exclusion.

## 3. Complete the returned-exclusion family

Upstream supplies **172 case-proof source archives**; case 1465 was its sole
omission and is now proved locally. **All 173 original full-case certificates
have actual named-target audits: 173/173, no original case remains.**

The [import-only diagnostic](verification/t03-final-batch04-import-only-accepted-checkpoint-20261002.json) **actually passed** the unchanged checker at **8 GiB with two threads in 2,073.22 seconds**, using the exact same sixteen imports and `True.intro`. Its raw accepted CHECK, empty compiler log and exact source are preserved. This is diagnostic elaboration only: it adds **no case or named-target axiom audit**. The run used [both page-adviser policies in sequence](verification/t03-final-batch04-page-policy-actual-chronology-20261002.json); the refined finite adviser completed, and no general speedup is claimed. The [main retry snapshot](verification/t03-final-batch04-memory-retry-validation-phase-snapshot-20261002.json) records source validation starting at **2026-10-02 at 13:56 UTC**, not final acceptance. **All 173/173 original cases remain audited**, with unchanged proof sources. The **two public combined audits and exact return ZIP are still pending**.

**The earlier final delivery attempt stopped with an [actual assembly import-memory failure](verification/t03-final-batch04-import-memory-failure-checkpoint-20261002.json).** The original final checker stopped at `Assembly/Batch04.lean` on **2026-10-02 at 13:12 UTC**, reaching its **8 GiB memory limit** with two threads. A separate diagnostic using the exact same sixteen imports and only `True.intro` also failed at that limit. The actual failed CHECK/log/source bytes are preserved. This leaves **all 173/173 original case audits intact**, with unchanged proof sources and no missing original cases. The then-pending [read-only object-page adviser diagnostic and resume controller](verification/t03-final-readonly-olean-page-adviser-pending-provenance-20261002.json) were recorded as pending at that dated checkpoint; the subsequent diagnostic result is documented above. The **two public combined target audits and exact return ZIP remain incomplete**.

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

The [three final-source rechecks](verification/t03-final-three-current-source-rechecks-checkpoint-20261002.json) for cases **2048, 1885 and 1848** each passed the exact original certificate Std3 audit at one thread with a 4 GiB limit. Their **148, 163 and 123 genuine outputs** were integrated with unchanged sources. Publication verified every recorded receipt/closure binding and each actual integrated root object; bulk tables and caches are omitted. These auxiliary checks do not increase the **173/173** case count. The two public combined audits and the exact exporter ZIP remain pending.

**All 173 original cases are audited; no original case remains unfinished.** The [same-final-source rechecks](verification/t03-final-current-source-rechecks1840-2125-checkpoint-20261002.json) for cases **1840 and 2125** also passed their exact original certificate Std3 audits at one thread with a 4 GiB limit. Their **134 and 122 genuine outputs** were integrated with unchanged sources. Every recorded receipt/closure binding and each actual integrated root object was verified; bulk tables and caches are omitted. These are final-route compatibility rechecks, with no case-count increment. Only the two public combined audits and exact exporter ZIP remain pending.

**All 173 original cases remain audited, with none unfinished.** The [final-source rechecks](verification/t03-final-current-source-rechecks1889-1950-1810-checkpoint-20261002.json) for cases **1889, 1950 and 1810** passed their exact original certificate Std3 audits at one thread with a 4 GiB limit. Their **80, 68 and 64 genuine outputs** were integrated with unchanged sources; every recorded receipt/closure binding and all three actual integrated root objects were verified. Bulk output tables and caches are omitted. The [sequential queue snapshot](verification/t03-final-bounded-auxiliary-queue-snapshot-20261002.json) is timestamped and does not accept any still-running recheck. Only the two public combined audits and exact exporter ZIP remain pending.

The [four accepted final-source rechecks](verification/t03-final-small-queue-completed-rechecks-checkpoint-20261002.json) for cases **1476, 2049, 1478 and 1783** each passed the exact original certificate Std3 audit at one thread with a 4 GiB limit. Their **55, 52, 50 and 42 genuine outputs** were integrated with unchanged sources. Every recorded receipt/closure binding and each actual integrated root object was independently verified for publication. The [finite six-case auxiliary queue](verification/t03-final-bounded-auxiliary-queue-completed-checkpoint-20261002.json) finished with **331 integrated outputs**, including the previously published cases 1950 and 1810. All **173/173 original cases are audited**; these auxiliary rechecks add no cases. The later case 1731 recheck is not counted as accepted here. The two public combined audits and the exact exporter ZIP remain pending.

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


The [case 1373 exact full certificate and source release](verification/t03-wand125-case1373-accepted-source-release-20261002.json) and case1464 closures add
two original integrations, now 172/173. The separately audited case 1465 partner
and four-step components add no full case certificate. Earlier dated checkpoint
paragraphs below preserve their historical scope and integration metrics.


Historical original-source full-certificate audits total **172/173**, with case 1465 alone remaining; the repaired tree requires fresh audits. The [accepted case 1393 and geometric Step012 source releases](verification/t03-case1393-and-geometric1465-accepted-source-releases-20261001.json)
provide the new full certificate and a separate checked single-step pilot. The
pilot adds no full case; the current prefix-through40 component checkpoint above
supersedes the earlier pending component status. Earlier dated
checkpoint paragraphs below preserve their historical integration metrics.


The [accepted numeric-state pilot](verification/t03-case1465-independent-numeric-state-pilot-source-release-20261001.json) preserves 75 numeric definitions
and checks Step012 state binding, but adds no full case certificate. Its geometric
transition and whole case audit were required at that earlier checkpoint, which
recorded169/173. The geometric pilot and later component targets now pass;
the full1465 certificate remains pending at the current172/173.


The refreshed [upstream inventory](verification/t03-wand125-upstream-source-inventory-refresh-20261001.json) supplies
172 source archives; only case 1465 is absent upstream. This is distinct from
the earlier original-project integration log of169/173, with cases1373,1393,
1464 and 1465 still pending. The [bounded cache checkpoint](verification/t03-inventory-and-bounded-cache-checkpoint-20261001.json)
is an actual component audit and contributes no additional full certificate.


`ElevenSquare/Pending/S06_Returned.lean:returned_certificate_exists` remains
admitted for the 173 returned indices. The generic terminal-trace wrapper and
checked common geometry/checker tools are present. Case2135's complete certificate
source closure is also included; the accepted generated collections are
published as release assets. Their exact sources still need assembly into the
merged public family theorem, and local1465's full certificate remains pending.

The checkpoints are documented in [T03_PROGRESS.md](T03_PROGRESS.md). The
[partial T03 release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited-151-20260930) supplies a standalone exact source collection
for 151 independently audited case certificates. Their actual target audits have
only the three standard axioms. A standalone source supplement adds the fully
audited case1484 and case2122 closures. The accepted grouped case1646 source
closure and the audited case2047 and case1848 closures are also published as
standalone supplements, with later accepted 1311, 1372 and 1731 checkpoints:
**172 published original-project full certificate audits** in total, now including
accepted imported cases1373,1393,1464,1463,1499,1823,1849,1887,1891,2051,2068,2069 and2070. Upstream separately supplies 172 case-proof archives;
only case1465 is absent there. All 13 prepared import source closures are
published in the prepared source release, with exact accepted Combined,
DirectTrees, PrunedTrees and ReboundPrunedTrees source closures for2068/2069/2070,1891,1887,1823,1849,1463,1499,1393,1373 and1464. All supplied immutable original-source full-target audits are complete; the repaired source versions still need fresh audits, and local case1465
remains pending. See T03_PROGRESS.md for exact source/audit bindings.
The Git source tree contains case2135 directly; the full generated source
collections are distributed as release assets.

The remaining local case1465 and assembly of all 173 certificates into the exact public
family theorem remain unfinished. Its clean combined target audit and the final
return package are also pending. No fresh merged repository Lean replay or
completed T03 case-family return is claimed; the public admission remains open.

## 4. Complete case438 capture into the local rectangle

`ElevenSquare/Tasks/T07/UnfinishedCapture.lean:case438_near_certificate` remains
admitted. Its type is the existing `Case438NearCertificate` interface: every
centered case438 packing of side at most `T` must admit a representation in the
focused local rectangle at the same physical side length.

This named obligation replaces the old opaque `sorry` body of the public
`global_lower_bound`. The public theorem now uses the returned, checked
`global_lower_bound_of_case438_certificate` composition. The three unfinished
exclusion families remain upstream dependencies of that composition.

The T07 return supplies occupied-cell seed geometry, role and chart transport,
physical field conversion, far-row collisions, terminal polygon/triangle checks,
strict core fits, and conditional near-box/rigidity interfaces. It does not
supply the complete trace from the genuine occupied seed to the stronger
archived root and branch states.

Remaining work includes the phase 2/root ancestry, both promoted terminal partner
hulls' actual ownership, all required far-branch eliminations, and final near-row
inclusion. The returned counterexamples rule out direct promotion from mere
closed-cell occupancy and a simple rowwise near inclusion. They are obstructions
to proposed shortcuts, not counterexamples to the optimality theorem.

## Completed stages to preserve

- Exact construction, geometric foundations, closed-cell cover, and finite case
  reduction.
- Generic owned-hull, core, residual-cover, trace, and local analytic arguments.
- The finite case inventory, overlay, strict distance bans, finite search, and
  conditional D4 bridge, including the previously checked integration fixes.
- The T01 groups and the initialized two-step T02 milestone described above.
- **T06:** `exact_local_packet_exists` and `construction_locally_isolated` have
  complete returned proofs. They cover the actual nonlinear gap aliases,
  derivatives, Taylor bounds, excluded features, branch cover, and 128 exact dual
  branches. The return reports clean audits with only the three standard axioms.

## Closing the proof

Discharge the six sites while preserving their semantics, then run the full
fresh source build and axiom audit. The final `global_lower_bound`,
`optimal_side_lower_bound`, and `optimality` must have no `sorryAx` or custom
computational axiom in their transitive dependency sets. A successful build of
this admitted snapshot alone does not satisfy that requirement.
