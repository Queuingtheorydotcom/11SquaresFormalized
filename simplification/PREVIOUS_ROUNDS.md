# Simplifying the eleven-square proof: T03 audit and complete simplification record

Prepared 3 October 2026. This report covers the new investigation of the T03 branch and all three earlier simplification rounds. It distinguishes new mathematical arguments, exact finite checks, kernel-checked Lean lemmas, existing upstream results, and work still needed to assemble a replacement optimality proof.

## Main findings

The strongest new geometric result is an **orientation-independent triangle barrier**. If three points have pairwise distance strictly less than one, every unit square whose center lies in their triangle strictly contains at least one of them. If the three points are already strictly owned by other squares, the entire triangle is forbidden to the target center.

Applied to the actual T03 case 2135, this lets the proof **stop after two of its six updates**. Three already-owned points, their triangle, and six elementary disk regions cover the remaining center hexagon. The four later updates are unnecessary for this argument. This eliminates 32 angle-row geometry proofs, 110 collision-polygon invocations, and 356 region-cover tree nodes in the original suffix. It is a shorter geometric argument, now checked in Lean from the original packing assumptions. With the additional initialization cleanup, its imported source falls from 109,487 to 66,202 lines (39.53%).

A separate structural simplification reconstructs planar linear-implication coefficients from **two facet indices**. On all 339 original case-2135 cover leaves, the witness expressions shrink from **982,172 to 27,274 bytes**, a **97.22% reduction of that particular payload**. This does not mean the whole proof is 97% smaller.

The strongest earlier results remain: a local argument with **two force balances and eleven scalar inequalities instead of 8,448 coordinate dual certificates**; a **two-bar geometric trap reducing G003 to six quartics**; a small symmetry argument; and stronger orientation and ownership lemmas. Their exact formalization boundaries are recorded below.

**No new complete global optimality theorem is claimed.** The inspected T03 branch records 173 individually audited original case certificates, but its two combined public targets remain pending, and its Git source still contains six admitted obligations. Some of our replacement arguments are now actual Lean geometry; others remain complete mathematical arguments with exact arithmetic checks and only partial Lean integration.

## Reading the evidence

The following distinctions apply throughout:

| Label | Meaning |
|---|---|
| Mathematical replacement | An argument with explicit premises, including ownership and coverage; it need not yet be assembled in Lean. |
| Exact replay | A finite arithmetic or source-binding check using integers, rational numbers, or certified algebraic calculations. It is not itself Lean kernel certification. |
| Kernel checked | The named Lean declaration compiled with the pinned toolchain and passed an axiom audit. |
| Published audit | Evidence inspected from the upstream branch/release; not a fresh full rebuild performed here. |
| Proposal | A plausible further improvement for which the concrete replacement has not been proved or measured. |

All our accepted Lean targets use only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`, or a subset. No custom axiom, `sorry`, `native_decide`, or trusted external numerical oracle was introduced in the replacement modules. The six pre-existing global admissions remain separately inventoried.

## A. What T03 actually proves

### A1. Sources and reproducibility

The main source examined is [the T03 branch](https://github.com/Queuingtheorydotcom/11SquaresFormalized/tree/t03-proof-progress-20260930), pinned to commit:

```
86502c40d8c04b5ee43a805a94223ca02afd3d6c
```

Earlier rounds used `11SquaresFormalized` at `b237948fa44eb8876ed87eeb21329ab5577c833c` and [the computer-assisted proof](https://github.com/Queuingtheorydotcom/11SquaresOptimal) at `f9e0de713a0949d1bc6a0fa6b59d96edf6c3d65c`. The separate public returned-case sources examined here are pinned to `wand125/n11-optimality-lean` commit `a8b51d3e0682beb1bf911048bdc8e7fa62329124`.

Fresh Lean checks use **Lean 4.10.0-rc2**, compiler commit `702c31b80712`, and Mathlib revision `3fef63ff3bda38478ba4364ff03999f0246745a2`, with the remaining dependencies checked against the pinned manifest. New T03 sources and build objects are isolated from the earlier checkout.

The source packet contains the detailed audit, arithmetic certificates, replacement Lean sources, generators, and compilation receipts. Repository-relative source paths below identify the upstream definitions precisely.

### A2. The theorem is a family of 173 exclusions

The public statement `ElevenSquare.Pending.returned_certificate_exists`, in `ElevenSquare/Pending/S06_Returned.lean`, concerns each index in a specific list of **173 of the 2,184 half-turn-reduced center-cell configurations**.

For each such index it asserts the existence of initial and terminal states such that:

1. Every genuine charted packing of eleven unit squares occupying that configuration, in the rational container below, initializes the first state after relabeling.
2. A verified trace carries that state to the terminal state.
3. The terminal state is impossible for a packing.

The rational container side is

\[
U=\frac{387708359002281417731}{100000000000000000000}
 =3.87708359002281417731.
\]

The soundness theorem then yields `returned_excluded`, whose conclusion for each index is:

```lean
∀ P : Packing 11 coverCap, ¬ Occupies P (caseMask k)
```

The chart parameterization chooses an axis representative for every physical square orientation; it does not rescale the packing or assume axis alignment. Actual `Packing` uses arbitrarily oriented unit squares, containment of their closed squares, and disjoint open interiors. Touching is legal. Cell membership and angle intervals keep their closed boundary ties.

The global inventory is:

| Family | Number of configurations |
|---|---:|
| Baseline | 1,931 |
| Prior support | 76 |
| T03 returned | 173 |
| Candidates `{438,999,1462,1659}` | 4 |
| Total | 2,184 |

Thus T03 is a substantial exclusion family, not the entire optimality theorem. Symmetry reduction, candidate capture, and the local argument are separate obligations.

### A3. The underlying geometry is much smaller than the generated source

A state gives each square two kinds of information:

* **Possible poses:** a union of closed center polygons crossed with closed angle intervals.
* **Owned points/hulls:** points proved to lie strictly inside that square in every actual packing represented by the state; convexity extends ownership to their hull.

A transition discards poses only when it proves an interior collision, then promotes points that every remaining pose consistent with the owner’s existing owned hull must contain. A typical collision uses a strict inner core of one square and another square's owned hull. Their Minkowski difference is a forbidden center region. A final contradiction is an empty pose list or an intersection between two distinct owners' strict hulls.

This explains both the proof's strength and its size: short geometric updates are supported by many polygon covers, orientation slices, and linear implication certificates. The original case 2135 has six updates. The large original case 1311 has only 24, despite its million-line dependency closure.

T03 already has generic induction and reflection machinery: `OwnershipTree`, `RowRefinement`, `PolygonCertificates`, `PosewiseReplay`, `SemanticCertificate`, and integer polygon-fan checks. Those are upstream achievements. Simply proposing “use one generic checker” would overlook them.

An especially useful existing bridge is `certificate_of_charted_refutation` in `Tasks/T03/SemanticCertificate.lean`. A direct contradiction for every actual charted packing of a mask can satisfy the original certificate interface without reproducing its historical trace. This provides a legitimate integration route for shorter geometry. It does not supply the contradiction for free.

### A4. Current formal status

The latest inspected records support **173 individually audited original full-case certificates**. The 172-entry reconciliation matches the returned-case list exactly except for case 1465; the later accepted case-1465 audit fills that gap. Its four published audit/source files match their checkpoint hashes. The recorded named-target axiom sets contain only the standard axioms.

However, the latest checkpoint explicitly leaves the **two combined public theorem audits pending**, with the final standalone source closure/return ZIP not complete. A successful import-only diagnostic ends with `example : True := True.intro`; it is not an audit of the combined family theorem.

The pinned Git source still contains these six admissions:

| Declaration or task | Remaining obligation |
|---|---|
| `Pending/S06_Returned.lean` | Public assembly of the 173 returned certificates |
| `Tasks/T01/Handoff/PlanData.lean` | Baseline plans |
| `Tasks/T01/Handoff/ProgramCalculations.lean` | Baseline transition calculations |
| `Tasks/T01/Handoff/LeafCalculations.lean` | Baseline leaf closures |
| `Pending/S06_PriorSupport.lean` | Prior-support certificates |
| `Tasks/T07/UnfinishedCapture.lean` | Case-438 capture into the focused local neighborhood |

The source checker passed with exactly these six admissions. That source check is distinct from kernel verification. We did not freshly rebuild all 173 case certificates. None of our simplifications should be read as a claim that the original packing result is false; the distinction concerns what the inspected formal source and audit evidence presently establish.

## B. New simplifications found in T03

### B1. A small-diameter hull forbids a center, in every orientation

**Lemma.** Let a finite set of points have pairwise distances strictly less than one. If the center of a unit square lies in their closed convex hull, at least one point lies strictly inside the square.

**Proof.** Translate the center to the origin and use the square's own orthonormal coordinates. The coordinate widths of the point set are both strictly less than one. Consequently, there cannot be points at or beyond both opposite facets of the square. Reflect each coordinate, if necessary, so every point has

\[
x>-\tfrac12,\qquad y>-\tfrac12.
\]

If a point is not strictly inside the square, it must have either \(x\ge\tfrac12\) or \(y\ge\tfrac12\), so \(x+y>0\). Every convex combination of these points also has positive coordinate sum. The origin cannot be such a combination, a contradiction. ∎

The proof permits zero barycentric weights and a center on an edge or vertex of the hull. The strict diameter bound is essential: the two points \((-1/2,0)\), \((1/2,0)\) have diameter one, bracket the center, and both lie on the unit square's boundary.

**Packing consequence.** The points may belong to different owners. If each is strictly inside some square different from the target, the target's center cannot lie in their convex hull. We do not assume that a mixed-owner triangle is itself owned by one square.

This is stronger than the usual radius-\(1/2\) disk exclusion. An equilateral triangle of side \(.9\) has a center at squared distance \(.27>1/4\) from each vertex. All three individual disks miss it, yet the triangle lemma excludes that center for every square orientation.

**Implementation.** `OwnedTriangleBarrier.lean` proves the stronger scalar coordinate-width statement for any finite number of points. `OwnedTrianglePacking.lean` bridges it to the repository's actual `UnitSquare`, `OpenSquare`, and `Packing` definitions. The two scalar targets and four actual-geometry targets have passed kernel checking and axiom audits.

### B2. Case 2135 terminates after two updates

The owner-to-cell list for this case is `[1,2,3,5,7,8,9,10,11,13,14]`; owner indices and cell labels are different. The target is **owner 7**, in cell 10.

Choose these three existing hull vertices:

\[
\begin{aligned}
p_6&=\left(
\frac{74247801998837882212044616329}{38200000000000000000000000000},
\frac{83587250502589988941554015679}{38200000000000000000000000000}
\right),\\
p_8&=\left(\frac{288115159}{100000000},\frac{554210361}{250000000}\right),\\
p_{10}&=\left(\frac{2305035533}{1000000000},\frac{1474001781}{500000000}\right).
\end{aligned}
\]

| Point | Actual source hull and zero-based vertex | Availability |
|---|---|---|
| \(p_6\) | `Hull2baf8973e8c4b2ed8e82[4]` | Promoted by `Step001`, the second update |
| \(p_8\) | `Hulld03e90ac6f0cc222ce40[0]` | Initially owned |
| \(p_{10}\) | `Hull895fb5170ea86a7cf77e[1]` | Initially owned |

All three pairwise squared distances are strictly below \(22/25<1\). The squared distances are approximately .87971429, .70797306, and .86650775; the proof uses the exact fractions.

At the end of `Step001`, owner 7 still has eight initial angle rows. **All eight have the same six center halfplanes.** Their common center region is a hexagon \(H\). Let \(\Delta=\operatorname{conv}\{p_6,p_8,p_{10}\}\). The exact finite cover is

\[
H\subseteq\Delta\cup B(p_6,1/2)\cup B(p_8,1/2)\cup B(p_{10},1/2),
\]

where the disks are open. Centers in the triangle are excluded by B1. Centers in a disk make its owned point lie in the target's open inscribed disk, hence strictly inside the target square. Either way, two square interiors meet.

The complete state-to-contradiction argument is kernel checked as `ElevenSquare.Simplified.Case2135EarlyRefutation.state_false`, with no unproved cover or ownership premise. This contradiction is available immediately after the first two original updates. We can bypass `Step002` (owner 5), `Step003` (owner 0), `Step004` (owner 9), and `Step005` (the old terminal elimination of owner 7).

### B3. The cover needs six convex pieces and no angle subdivision

For each counterclockwise triangle edge \(a\to b\), intersect \(H\) with its closed exterior halfplane:

\[
\operatorname{cross}(b-a,c-a)\le0.
\]

Split this region by the perpendicular bisector

\[
2(b-a)\cdot c\le\|b\|^2-\|a\|^2
\]

and its reverse. The result is two quadrilaterals, assigned to the nearer endpoint. Doing this for three edges produces six quadrilaterals. Every point outside the closed triangle belongs to at least one of them; all split ties remain covered.

A convex quadrilateral lies in an open disk if all its vertices do. Every assigned vertex has squared distance strictly below

\[
\frac{49}{200}=.245<\frac14.
\]

The squared-radius margin is greater than \(1/200\). The three edge-pair maxima are approximately .232788765298, .244969437947, and .240052712674.

The arithmetic checker verifies all 24 listed vertex occurrences. Only **nine distinct vertices need independent norm calculations** in a hand proof: six hexagon vertices and three bisector intersections with alternate hexagon edges. All other vertices lie on triangle sides within half a side length of their assigned endpoint, so their squared distance is below \((22/25)/4=.22\). The concrete Lean cover may retain the redundant 24 checks for a simpler implementation; no nine-check Lean performance claim is made.

The certificate also proves \(H\subseteq[1,4]^2\) with four exact two-facet implications. Thus polygon clipping starts from a justified bounding box; it does not silently discard an unbounded component. Positive edge factors and polygon-fan checks certify each quadrilateral's complete halfplane description.

**Physical units matter.** These are the actual local T03 `QPoint` coordinates. `IntegerRow.center_mem` connects them directly to the physical `UnitSquare` center, whose half-width is exactly \(1/2\). They are not coordinates from the separate scaled U2R field archive. Using the wrong scale would invalidate the distance thresholds.

### B4. What the new geometry removes—and what it retains

| Work in the original suffix | Amount bypassed |
|---|---:|
| Forward updates | 4 of 6 |
| Angle-row geometry proofs | 32 |
| Collision-polygon invocations | 110 |
| Region-cover tree nodes | 356 |
| Strict-core fitting invocations | 32 |
| Difference-vertex witnesses | 1,331 |

The final update alone used eight angle bands and 27 collision-polygon invocations; the stronger early-termination argument removes three preceding updates as well.

The exact source-closure comparison is:

| Root | Local modules | Physical source lines | Source bytes |
|---|---:|---:|---:|
| Original `Forward.Certificate` | 723 | 109,487 | 15,690,011 |
| Retained `Forward.Step001Trace` | 698 | 104,124 | 14,532,308 |
| Gross original dependencies bypassed | **25** | **5,363** | **1,157,703** |

The new geometric argument adds **nine modules, 685 lines, and 43,107 bytes**. Before the additional initialization pruning in B8, including that overhead gives a source closure of **707 modules, 104,809 lines, and 14,575,415 bytes**: a net reduction of **4,678 lines (4.27%)** and **1,114,596 bytes (7.10%)** from this original case closure. These are static source-import counts, excluding Mathlib and compiler objects; the exact inventories and hashes are in `case2135-net-closure-counts.json`. The original files remain available; the new theorem no longer imports the bypassed suffix.

The original initialization and first two updates are retained. They contain most of the shared source, so reducing six updates to two does not reduce the whole imported source by two-thirds. The small generic barrier modules can be shared by further case replacements.

The generic barrier is reusable across other cases. Its cost should be shared, but no extrapolation to all 173 cases is justified until their actual owned points and center domains have been checked.

### B5. Two facet indices replace large linear multipliers

Suppose a point satisfies \(u\cdot x\le\alpha\) and \(v\cdot x\le\beta\), and we want \(w\cdot x\le\gamma\). Define

\[
D=\det(u,v),\quad A=\det(w,v),\quad B=\det(u,w).
\]

The two-dimensional identity

\[
Dw=Au+Bv
\]

proves the implication whenever

\[
D>0,\quad A,B\ge0,\quad A\alpha+B\beta\le D\gamma.
\]

Everything can be checked with integer cross products; there is no division. Swap the source facets if needed to make the determinant positive. The accepted one-facet constructor handles equal normals with a weaker offset. Other degenerate forms can retain an existing fallback.

The original source stores denominator and multiplier integers, even though in these leaves the source normals determine them. Our replacement stores only the selected facet indices and reconstructs the coefficients inside the proved checker.

| Actual case-2135 data | Count or size |
|---|---:|
| Cover leaves checked | 339 |
| Target-edge implications | 4,465 |
| Two-facet implications | 3,835 |
| One-facet implications | 630 |
| Old witness expressions | 982,172 UTF-8 bytes |
| New index-pair expressions | 27,274 UTF-8 bytes |
| Witness-payload reduction | **97.22%** |
| Multiplier/denominator digits removed | 767,219 |

The producer rechecks the old Farkas equations before constructing replacements and checks every new determinant inequality exactly. `DeterminantImplications.lean` supplies the generic soundness proofs; six generated step modules contain the actual replacement leaves. All six batches passed the pinned kernel: 339 leaves and 4,465 implications, covered by 17 named-target axiom audits across the generic checker, pilot, and batches. They do not import the enormous original trace just to prove a planar implication.

This preserves the original geometric decomposition. It is useful independently, especially for early updates that our triangle shortcut retains. Savings overlap on the discarded suffix, so they must not be added as percentages.

### B6. Three indices replace barycentric certificates

The new `IndexedTriangle.lean` checker uses three vertex indices and four oriented-area sign checks to certify hull membership, reusing the existing `triangle_mem_convex` theorem. No explicit barycentric weights need be stored for a positively oriented nondegenerate triangle. Closed edge and vertex cases remain valid; degenerate cases need their old fallback or another constructor.

The two generic targets passed kernel checking. This is a proved representation improvement, but there is no measured replacement census across the original archives yet. It must not be counted as a concrete whole-proof size reduction.

For the case-2135 cover, `OrientedTriangleWeights.lean` supplies an explicit adapter from three closed triangle halfplanes to nonnegative normalized barycentric weights. It uses signed subtriangle areas divided by the positive total area. This adapter and the disk-convexity helper connect the finite polygon cover to the actual packing barrier.

### B7. Structural lessons from the large proof

The original case-1311 archive contains **105,662 one- or two-term indexed linear witnesses** in 47 modules. Their literal witness data total 17,970,125 bytes; facet-index lists would total 514,699 bytes. This identifies approximately **17.46 MB of potentially redundant data**. It is a structural census, not an instantiated or kernel-checked rewrite of that case.

Most of its 431.7 MB dependency closure is outside this particular literal form. Shorter coefficients alone will not make the global proof small. The larger mathematical opportunity is to replace long ownership-growth sequences by a few support inequalities or a terminal barrier available much earlier.

A separate upstream case-1311 proof ends by trapping one square with four neighboring owners after many promotion stages. This suggests a four-neighbor analogue of the two-bar and triangle arguments. No such complete replacement has been proved here. Backward pruning alone is not new: the upstream generator already removes unused whole promotion steps.

The assembly memory issue also cannot be attributed solely to a verbose last theorem. An import-only diagnostic reproduces the problem before proving any substantive new target. A useful architectural rewrite must remove repeated data and imported declarations, then measure the new closure and peak memory. Hiding the same imports behind an umbrella module or shortening namespaces does not establish that improvement.

### B8. Initialize only the eleven occupied cells

The case-specific seed originally consisted of one import of the whole batch.
That batch imported both the 64-angle-row and 8-angle-row initialization
libraries, even though case 2135 uses only the latter. The 8-row library in turn
imports ownership and pose proofs for all sixteen cells. Case 2135 occupies only
eleven of them.

We extracted its seed from the batch and replaced the all-cell lookup with
the eleven original cell-specific pose and ownership results. The new proof
uses the existing `occupancy_relabel` lemma, then applies those results once for
each of the eleven owners. The occupied-cell list, injectivity proof, recorded
tuple, mask binding, public initialization type, actual pose rows, and actual
owned hulls are preserved. The other thirteen batch seed bodies are unchanged.

This is proof-dependency pruning, separate from the triangle argument. It
removes imports of the unused 64-row library and of the five unoccupied cells
`{0,4,6,12,15}` from this standalone case. It does not weaken initialization or
replace an ownership theorem with an assumption.

This improvement is local to the case's imported closure. Across all 173
returned configurations, every one of the sixteen cells occurs; the complete
family still needs their initialization proofs. Thus a large standalone-case
reduction must not be extrapolated to the union of the whole family's sources.

The resulting source closure, including the triangle replacement and its full overhead, is **498 modules, 66,202 lines, and 9,598,826 bytes**. Against the pinned original case this saves **225 modules, 43,285 lines (39.53%), and 6,091,185 bytes (38.82%)**. These counts include all transitive local source imports; they exclude external dependencies and compiler objects. The source and patch hashes are recorded in `initialization/selected-closure-counts.json` and `patch-manifest.json`.

### B9. Exact verification boundary

The complete new case certificate has been checked from the original packing
and occupied-cell assumptions through the selected-cell initialization, the
first two original updates, and the triangle/disk contradiction. The accepted
public-contract theorem is:

```lean
ElevenSquare.Simplified.Case2135EarlyCertificate.certificate_exists
```

It has exactly the original case-2135 existential certificate type. Its
`charted_refutation` input is proved, not assumed. The simpler intermediate
result remains useful independently:

```lean
Case2135EarlyRefutation.state_false :
  StateHolds P Step001State.state → False
```

The new-source receipt records **40 named-target audits across 18 new modules**:

| Component | Audited targets |
|---|---:|
| Determinant engine, pilot, six leaf batches | 17 |
| Indexed triangle membership | 2 |
| Triangle geometry, actual Packing bridge, disk convexity, barycentric adapter | 9 |
| Actual state bindings, exact cover, state contradiction | 10 |
| Initialized case refutation and original-contract certificate | 2 |

The concrete cover also contains 21 finite Boolean checks: three triangle-edge
bindings, six quadrilateral fans, six source-facet bindings, and six bundled
strict vertex-distance checks. The final theorem's axiom audit includes only
`propext`, `Classical.choice`, and `Quot.sound`. The selected seed and the remaining batch-seed module were also compiled after the import refactor.

The replacement case closure contains no admitted proof dependency. This is a
fresh completed check of **one simplified case**, not the combined 173-case
family or global optimality. Case 2135 was already proved upstream; this is a
shorter replacement and does not close any of the six global admissions.
All earlier-round limitations in section D remain
as stated. `review/verification.json` and `initialization/verification.json`
bind the accepted source, object, dependency, compiler, and target evidence.
## C. Correcting the earlier whole-proof size estimate

My earlier estimate based on the main checkout did **not** account for T03's large release-source collection. It was therefore not a valid estimate of the full formalization, and I withdraw that extrapolation.

| Precisely identified scope | Lean files/modules | Lines | Bytes |
|---|---:|---:|---:|
| T03 Git-tracked Lean, including verification snapshots | 9,372 files | 965,296 | 118,237,007 |
| Actual `ElevenSquare` project in that checkout | 8,562 modules | 827,708 | 101,424,239 |
| Included original case-2135 closure | 723 modules | 109,487 | 15,690,011 |
| Published original case-1311 closure, including `lakefile.lean` | 2,533 files | 1,255,432 | 431,689,357 |
| Published 151-case collection metadata | 101,494 modules | Not established | 5,499,202,925 |

All member hashes of the sampled original case-2135 and case-1311 source collections were checked against their manifests. The multi-gigabyte 151-case collection was not downloaded in full; its module/byte totals are published metadata. Its ZIP is approximately 1.519 GB. These closures share sources, so adding their line counts would double-count.

The precise “3.5 million lines” total is neither established nor disproved by this audit. It needs an exact archive/version and counting convention. In some alternative generated sources a single line contains a huge encoded certificate integer, which makes line counts particularly misleading.

**What can be stated now:** the case-2135 geometric replacement saves 4,678 source lines after its new overhead (5,363 gross); with the case-specific initialization refactor, the standalone closure shrinks from 109,487 to 66,202 lines. Its separate linear-witness payload can be reduced by 97.22%; the earlier local and G003 arguments have much smaller mathematical certificates. A defensible total for the rewritten full proof requires integrating those replacements, regenerating the remaining cases, and measuring the deduplicated resulting closure. A guessed total would give false precision.

## D. Complete record of the earlier simplifications

The following sections retain the full progression, including intermediate methods superseded by stronger geometry. Counts from successive replacements are not additive. The strongest local progression is **8,448 → 66 → 0 coordinate duals**; the strongest G003 progression is **270 two-angle rectangles → 87 one-angle intervals → six quartics**.

### D1. Construction and endpoint algebra

Use the half-angle parameter

\[
c=(1-u^2)/(1+u^2),\qquad s=2u/(1+u^2),\qquad
T=3+(2-c)/(c+s)=(6u+4)/(1+2u-u^2).
\]

The endpoint parameter is the root in `9/25≤u≤37/100` of

\[
P(u)=5u^8-10u^7-2u^6+14u^5+12u^4-6u^3+2u^2+2u-1.
\]

The offsets simplify to
`ρ=1−(T−3)c`, `η=(c(2−s)−1)/(c+s)`, `v=c−s`,
`ζ=1+(2−3c)/s`, and `x₀=T−1−s/c`. These identities hold throughout the
parameter interval; they do not require the endpoint polynomial.

The only non-identical closing contact is between squares 2 and 10:

\[
g=c+\zeta-sx_0,
\qquad \frac{P(u)}{(1+u^2)^4}=cs(c+s)g.
\]

Positive denominators on `9/25≤u≤37/100` make `g=0` equivalent to the source
degree-eight equation, without squaring or extra roots. The endpoint can thus
be specified geometrically by

\[
c^2+s^2=1,\quad (T-3)(c+s)=2-c,\quad
(T-1)cs^2=(c+1)s+2c-3c^2.
\]

The exact construction check uses **44 wall-support inequalities and 55 pair
separations**. Of these 99 constraints, **74 are strictly positive throughout
the interval, 24 are identities, and only one uses `P(u)=0`**. The checker
also verifies the selected extremizing vertices and axes exactly.

The endpoint derivative has the short decomposition

\[
P'(u)=(2-9u^2)+u(4-9u)+12u^3(4-u^2)
 +70u^4(1-u^2)+40u^7>0
\]

on `0≤u≤2/5`. This replaces eight large Bernstein coefficients. The original
`u` and `T` polynomials are irreducible over the rationals, so this does not
turn either algebraic number into a rational quartic root.

**Files:** `algebra-analysis.md`, `simplify_construction.py`,
`construction_geometry.json`; Lean
`11SquaresFormalized/ElevenSquare/Simplified/Endpoint.lean`.
**Status:** exact SymPy/rational construction replay; two derivative targets
compiled with standard axioms. The full rational-coordinate construction
replacement is not Lean-integrated. Fine bounds separating `T` from the
rational cap `U` are still needed by the global proof.

### D2. A small, honest global interface

`GlobalReduction.lean` preserves the actual `Packing`, `CenteredPacking`,
`LocalFeasible`, `T`, and `Optimality` definitions. It introduces `NearPacking`
and proves the final conclusion from precisely mask reduction, capture of
**strict improvements `S<T`**, and local isolation.

Two useful specification reductions are formalized or exposed:

- The lower bound needs capture only for `S<T`, not equality classification
  of every `S≤T` packing.
- The final contradiction needs only the occupied point `(T,0)` or an
  equivalent no-shrink/span conclusion; proving all 33 displacements zero is
  stronger than the endpoint contradiction requires.

The original physical side `S` is retained through centered containment;
there is no scaling of unit squares. A right-wall witness in the target frame
forces `T≤S`.

The measured interface closure shrinks from **4,126 modules / 499,477 lines /
40,684,640 bytes** for `Optimality` to **23 modules / 6,194 lines / 426,830
bytes**. This is a small statement/interface, not removal of the evidence
required for its three hypotheses.

**Files:** `lean-structure-analysis.md`;
`11SquaresFormalized/ElevenSquare/Simplified/GlobalReduction.lean`.
**Status:** four theorem targets compiled; first-round combined receipt
`output/bundle/verification/lean-scoped.json` records nine audited targets in
three modules and a 25-module scoped build. Only standard axioms occur.

### D3. Baseline inventory compression and exact limits

Every one of the **93 original groups** can be represented by one partial
16-cell mask `P`: a case belongs precisely when `P⊆M` or `P⊆halfTurn(M)`.
Exact comparison recovers all original lists. Thus **4,232 group-membership
literals become 93 masks**, a 97.80% reduction of that payload.

The existing **71-group selection was already upstream work**. We proved it
minimal among those same 93 groups: 69 groups have unique witness cases, and
the four remaining cases require two further groups. Either `{G026,G058}` or
`{G049,G058}` completes the forced 69.

The union of the **1,931 baseline cases** also has an exact minimal
**50-pattern monotone classifier**. A matching 50-case lower-bound witness
is checked against all 65,536 partial masks. This does **not** reduce 71
geometric certificates to 50: 27 classifier patterns combine cases with
different geometric proof provenance.

**Files:** `compression-analysis.md`, `audit_baseline_compression.py`,
`baseline-compression-certificate.json`.
**Status:** exact finite audit, including lower bounds; no replacement Lean
group-table bridge or new geometric exclusions. A reduction below 71 needs
stronger geometry or a changed certificate family.

### D4. Symmetry: from a global overlay to small pigeonhole facts

The original cover yields `choose(16,11)=4,368` masks, or **2,184** under its
actual half-turn symmetry. The original noncandidate exclusions leave masks
`438,999,1462,1659`. The cover is not fully D4-invariant, so division by eight
would be invalid.

The first reduction retained the 220-region overlay but reduced **1,572
distance bans to one**, by staged elimination. A further three-row mask table
checks the 216 possible other-view mask triples for each non-438 source,
using only sound distinct-label domain propagation.

The stronger geometric version removes the global overlay entirely:

- **Twelve explicit pigeonhole/Hall-type obstructions** use local closed-cell
  intersections, with more centers than available labels.
- **One two-view collision** confines two centers to boxes whose normalized
  squared distance is at most `221/2500`. Since physical scale `U−1<3`, their
  squared physical distance is below `1989/2500<1`.
- After excluding 1462 and 1659 in every view, the eight remaining view-bit
  triples fall into **four symmetry orbits**, each contradicted using at most
  three centers.

Boundary assignments are transported through the exact half-turn instead of
assuming a tie-break commutes with symmetry. Closed point/segment
intersections are retained.

**Files:** `d4-simplification/README.md`, `verify_one_ban_bridge.py`,
`verify_mask_table.py` in that directory;
`geometric-round2/symmetry/GEOMETRIC_SYMMETRY.md`,
`verify_geometric_lemmas.py`, `geometric_lemmas_result.json`.
**Status:** exact source-matched rational replay; no new complete Lean bridge.
Every version remains conditional on all **2,180 noncandidate exclusions**.

### D5. Local rigidity, first reduction: a sharper generic certificate

For necessary rows `A_i h≥−τ²K_i/2`, nonnegative dual weights `λ_i`, and
`|h_k|≤τr_k`, the correct residual is

\[
E=\sum_k r_k\left|\sum_i\lambda_i A_{ik}-\sigma\mathbf1_{k=j}\right|.
\]

The single strict condition `E+(λ·K)/2<r_j` gives isolation by choosing a
saturated coordinate with the opposite sign. It improves the old bound
`ε max r` because `Σr_k|e_k|≤max r Σ|e_k|`. Only one-sided Taylor upper
bounds are needed for the mathematical argument.

This permits rounding every old dual to denominator **1000**, retaining all
**8,448** successful checks; worst ratio is approximately **.9692843792**.
Denominator **512** also passes the weighted interface; denominator **10,000**
passes even the original uniform-residual interface. Coarser negative controls
fail. Denominator 1000 yields **2,883 distinct sparse vectors**, 86,789 stored
nonzeros instead of 354,816 dense slots. The self-contained packet is 861,246
bytes versus 3,772,308 bytes for the old 128 dual-data source files.

**Files:** `local-analysis.md`, `compress_local_duals.py`,
`verify_compact_duals.py`, `local-duals-compact.json`, `local-duals-replay.json`;
Lean `ElevenSquare/Simplified/LocalRigidity.lean` in the formal checkout.
**Status:** three generic lemmas compiled; exact source-matched numeric replay.
Rounded concrete certificates are not Lean replacements. This is superseded
mathematically by the later dual-free proof, but remains a conservative
integration option.

### D6. Local rigidity, second reduction: 128 systems become one

At each parallel reference contact, the two possible owners' tangent-row
pairs have the same common necessary pair, by convex combinations with
nonnegative weights. For an appropriate tangential offset `d∈[0,1]`, the
combined condition is the angular penalty

\[
v+\tfrac d2(a+b)\ge\tfrac{1-d}{2}|a-b|.
\]

This is used on reference gradients, not as an assertion that perturbed
squares stay parallel. The shared error bound includes every nonlinear alias
and either owner. **660 exact coordinate identities and 20 convex-weight
bounds** verify the five contacts. All 128 source branches imply the same
**40 rows: 30 fixed + 5×2 common rows**. Contact `(4,5)` is unnecessary.

The single system needs **66** signed-coordinate duals rather than 8,448.
All denominator-1000 duals pass the original focused rectangle; worst ratio
is **.9665418398787586**. The packet is **47,369 bytes**. An optional probe
also removed one further wall row, but the natural 40-row presentation is
the accepted main version; no minimality claim was made.

**Files:** `geometric-round2/local/README.md`, `ParallelContact.lean`,
`single-system.json`, `verify_single_system.py`, `single-system-replay.json`.
**Status:** three generic contact/convexity lemmas compiled, concrete bridge
and finite checks exact in Python. This proof is superseded by the next
dual-free version, not counted as an additional independent reduction.

### D7. Local rigidity, strongest reduction: two balances and eleven checks

The forty necessary rows group into **24 force constraints**, with positive
weights in **two balances** (8 and 16 constraints). Both sums cancel all
22 translation coordinates. Their common-inner-angle loads have opposite
signs, approximately `−.5410345902` and `+.5798968594`.

The key analytic improvement is that gap errors vanish with the angles:

\[
|\operatorname{rem}g_{ij}|\le .019|\theta_i|+.005|\theta_i-\theta_j|,
\qquad |\operatorname{rem}g_{\rm wall}|\le .0025|\theta_i|.
\]

These follow from exact rotation estimates and hold on the closed uniform
box `|δx_i|,|δy_i|≤.004`, `|θ_i|≤.007`. Thirteen exact reference-distance
checks give the needed bound `‖D‖<2`; aliases of either owner are covered.

Add the two balances with equal weights. A simple flow on edges
`67,68,79,89,9–10` bounds the inner angular load. Let `α=θ₉` and let `z`
contain six outer absolute angles and the five absolute edge-angle differences.
The result is `K·z≤.27|α|+B·z`. The two sign cases for the common angle are
both bounded by one rational vector: `|α|≤q·z`.

The final table has only **eleven inequalities**
`K_j−B_j−.27q_j>1/100`; its smallest margin is **53/5000=.0106**.
Hence `z=0`, `α=0`, and all angles vanish. Both positive force sums then have
zero total and nonnegative individual gaps, so all 24 gaps vanish. Boundary
anchors and orthogonal contact propagation fix every center, with no matrix
rank computation and **zero coordinate dual certificates**.

The complete final scalar table is below. Every decimal in it denotes an exact rational bound.

| Energy coordinate | `K` | `B` | `q` | `K−B−.27q` |
|---|---:|---:|---:|---:|
| \(\lvert\theta_0\rvert\) | .46 | .007 | .12 | .4206 |
| \(\lvert\theta_1\rvert\) | .64 | .009 | .15 | .5905 |
| \(\lvert\theta_2\rvert\) | .46 | .011 | .25 | .3815 |
| \(\lvert\theta_3\rvert\) | .77 | .042 | .06 | .7118 |
| \(\lvert\theta_4\rvert\) | .32 | .023 | .18 | .2484 |
| \(\lvert\theta_5\rvert\) | .31 | .030 | .25 | .2125 |
| \(\lvert\theta_6-\theta_7\rvert\) | .57 | .047 | .24 | .4582 |
| \(\lvert\theta_6-\theta_8\rvert\) | .21 | .045 | .23 | .1029 |
| \(\lvert\theta_7-\theta_9\rvert\) | .42 | .092 | .39 | .2227 |
| \(\lvert\theta_8-\theta_9\rvert\) | .46 | .120 | 1.22 | .0106 |
| \(\lvert\theta_9-\theta_{10}\rvert\) | .22 | .048 | .39 | .0667 |

The companion feature estimate proves that **all 88 unavailable feature
corners stay below −.003 throughout this same uniform box**; the worst exact
upper bound is `−1213333743/400000000000`. It checks 616 reference projection
polynomials. Together with the source's exhaustive 112-feature inventory and
24 allowed features, it removes the focused-box feature-availability limit.

**Files:** `geometric-round3/local/README.md`, `verify_angular_energy.py`,
`exact_field.py`, `angular-energy-replay.json`, `AngularContraction.lean`;
`geometric-round3/features/README.md`, `verify_uniform_features.py`,
`uniform-features-check.json`; independent reviews under
`geometric-round3/review/` and `geometric-round3/root/`.
**Status:** complete mathematical local replacement with exact source-bound
arithmetic; two abstract contraction targets compiled. Source gradient/tie
identities, new analytic remainder, uniform feature bridge, concrete scalar
bounds, and translation propagation are not all assembled into a new Lean
packing theorem. Global capture into this box remains separate.

### D8. Two finite geometric lower bounds and support penalties

Two positive contact/wall balances give lower bounds `L≥F₁(u)` and `L≥F₂(u)`
within an explicit structural class. `F₁` increases, `F₂` decreases, and

\[
F_2-F_1=-\frac{2uP(u)}{(1+2u-u^2)H(u)}.
\]

Here the explicit functions are

\[
F_1(u)=\frac{6u+4}{1+2u-u^2},\qquad
F_2(u)=\frac{4(u+1)(u^6-2u^5+2u^4+7u^3-2u^2+u+1)}{H(u)},
\]

with

\[
H(u)=u^8-2u^7-2u^5+14u^4+2u^3+2u+1>0
\]

on the reference interval `9/25≤u≤37/100`.

Thus `min max(F₁,F₂)=T`, uniquely at the endpoint. The derivative bounds
`F₁′>1/2`, `F₂′<−1/5` imply `|u−u_*|≤5(L−T)` in the class. Equality
forces the five inner orientations and all positions. A 23-equation
construction system has determinant `cs²(c+s)>0`; its omitted closing
contact supplies the endpoint equation.

The initial class assumed six axis-aligned outer squares, thirteen directed
projection orders, and two width bounds. The widths were weakened to one
condition `c w₇+s w₁₀≥(c+s)²`. An intermediate-value argument chooses a
reference angle making it equality when the two folded angles lie in the
stated interval.

The stronger support result removes the six axis-alignment hypotheses:

\[
q+r\ge\tfrac12+\tfrac{c+s}{2},
\]

where `q` is a square's coordinate support radius and `r` its support radius
in the reference frame. Sectorwise concavity gives a geometric proof; exact
half-angle factorizations give rational certificates. Five outer squares
then need **no angle restriction**. Square 2 needs only
`|tan(α₂/2)|≤27/100`, which includes all orientations within 30° of an axis.
This also gives equality rigidity and preserves the conditional angle estimate.

**Files:** `geometric-round2/algebra/two-geometric-balances.md`,
`two_balances.json`, `verify_two_balances.py`;
`geometric-round3/algebra/support-penalties.md`, `verify_support_penalties.py`,
`SupportCosts.lean`, `support-penalties-check.json`.
**Status:** exact algebraic and rational checks; four support-chart targets
compiled. The **thirteen directed projection orders in one common reference
frame remain assumptions**. Ordinary nonoverlap or nearby independent angles
do not imply them. This conditional finite theorem is separate from the
arbitrary-angle local proof in section D7.

### D9. G003: 270 rectangles, then 87 intervals, then six quartics

All versions exclude occupied support **`{0,4,8,12}`**, accounting for the
same **764 canonical cases** as G003. G003 was already proved upstream;
these replacements close no original admission.

1. **Core-overlap replacement:** fixed owned endpoint hulls exclude center
   regions; inscribed midpoint-axis square cores force the two middle squares
   to overlap on **270 closed dyadic two-angle rectangles**. A separate
   exact consumer checks the covering tree and all inequalities. The weakest
   overlap margin is approximately `−.00001674474516`. This avoids the
   existing **43 majority-capture windows**. Its certificate is about 54 KB;
   the measured old closure had **495 G003/Field03-specific files totaling
   2,499,093 bytes**, plus shared files. Build savings were not measured.
2. **Common-point replacement:** only four inherited strictly owned endpoints
   are used, forming two horizontal segments. Each middle square must contain
   `q=(49/50,39/20)` strictly. Independent one-angle checks need **34 intervals
   for cell 4 and 53 for cell 8: 87 total**, instead of joint angle rectangles.
   Four of eight projection facets follow immediately from coarse bounds and
   Cauchy–Schwarz.
3. **Analytic two-bar trap:** segment-square separation has three unoriented
   axes. Cell bounds eliminate the three lower directions; combining the
   remaining upper directions with either possible failure of strict point
   containment leaves six short cases. The final orientation checks reduce
   to **six quartics**, two completed-square positivity decompositions and
   **22 positive Bernstein coefficients** for the other four quartics. No
   narrow angle subdivision remains; two broad regimes per cell include
   their switching endpoints.

The four original owned-point premises are
`SymbolicCell00.ownedP006`, `.ownedP007`,
`SymbolicCell03.originalP12_005`, `.originalP12_011`, supported by the
corresponding checked ownership lemmas. The actual sloping Voronoi cuts are
essential. Weakened effective bars are used only after deriving necessary
inequalities from the actually owned bars; no unowned lower segment is
silently asserted owned.

**Files:** `geometric-round2/baseline/strip/G003-simplified-proof.md`,
`verify_adaptive_certificate.py`;
`geometric-round3/g003-dichotomy/README.md`, `replay_segment_certificate.py`,
`PointCaptureFacets.lean`;
`geometric-round3/g003/TWO_BAR_PROOF.md`, `verify_two_bar_trap.py`;
independent analysis `geometric-round3/g003-dichotomy/analytic-bar-review.md`.
**Status:** all three finite acceptance checks passed with exact rationals.
Generic facet lemmas compiled. The final bar-separation/capture implication
and arithmetic bridge are not yet a complete new Lean G003 theorem. The
original four strict-ownership results remain explicit inherited premises.

### D10. Stronger unconditional ownership and angle pruning

The tight cell cover gives center-to-site distance at most
`A=.17(U−1)=.4891042103038784101427`. The inscribed open radius-1/2 disk
therefore makes the closed site disk of radius
**`2179/200000=.010895`** strictly owned, since `A+r<1/2`.

This replaces the old five-point diamond's **.005** axis offsets by
**.010895**: offset factor **2.179**, diamond-area factor **4.748041**,
still five points per owner. It is valid for any occupied-cell assignment,
without assuming capture into the archived root. An owned disk yields
immediate center exclusion `‖c_i−s_j‖≥1/2+r=.510895` for a different square.

Two owned points `p,r` eliminate the unknown center: for their difference
`d`, both `|d·a|<1` and `|d·a⊥|<1`. In half-angle coordinates these are
four strict rational quadratic inequalities. A near-wall center gives
`t(1−t)≤ε(1+t²)`; for example `x≤.51` excludes the entire closed chart
interval `.02≤t≤.97`. If the center is exactly distance 1/2 from a container wall, containment forces an axis-aligned orientation; ordinary vertex–wall contact does not.

**Files:** `geometric-round2/geometry/README.md`, `GeometryLemmas.lean`,
`SiteDisk.lean`, `verification.json`.
**Status:** ten new target theorems compiled in a 29-local-module scoped
closure, using actual geometric definitions. These are sound new seeds and
pruning rules, not a proved reduction in global case count. Optional grid
area estimates are exploratory only.

### D11. Exact finite contact geometry and actual orientation-distance theorem

In the mean orientation frame, write relative centers `(N,T)` and half
relative angle `φ`, with `c=cos φ`, `s=|sin φ|`, `c≥s≥0`. Set
`M=max(|N|,|T|)` and `m=min(|N|,|T|)`. The four separating-axis choices
collapse exactly to the octagonal test

\[
cM+sm\ge c(c+s).
\]

Under the guards `N≥0` and `N≥|T|`, this reduces to
`N≥c+(1−|T|/c)s`. With `0≤T≤c` the forward-owner disjunction is exactly the
smooth pair `cN−c²≥±sin φ(c−T)`. The guard cannot be dropped. For
`|T|≤1/2`, the compiled positive-opening consequence is
`N≥1+(31/120)|sin φ|` under the stated unit-circle/cosine bounds.

Separately, for **actual arbitrary disjoint unit squares** the sharp bound is

\[
\left(\frac{1+|a_1\cdot a_2|+|a_1^\perp\cdot a_2|}{2}\right)^2
\le\|c_2-c_1\|^2.
\]

Equivalently, for folded relative angle `δ∈[0,π/4]`, center distance is at
least `(1+cos δ+sin δ)/2`. Distance one forces equal physical orientations
modulo a quarter turn. This strengthens the old inscribed-disk bound without
assuming a contact graph, chosen separating owner, or local neighborhood.

**Files:** `geometric-round3/finite-contact/README.md`, `FiniteContact.lean`,
`OrientationSeparation.lean`, both verification receipts.
**Status:** four scalar targets and **four actual-square/packing targets**
compiled. The actual orientation-distance theorem is fully bridged to source
geometry; the mean-frame smooth-pair bridge and neighborhood guards remain
separate integration work. No global case is claimed closed by this alone.

### D12. Exact obstructions that rule out tempting shortcuts

- Every one of the **2,184 canonical masks** admits eleven rational centers
  for diameter-one circles in side **3.8770835<T**, in the correct original
  cells and with squared center distances strictly above **1.0001**. Thus
  cell membership plus center-distance-at-least-one cannot exclude even one
  original mask. These are countermodels to that weakened theory, not square
  packings or counterexamples to optimality.
- For G003, replacing the true cells by their individual bounding boxes
  admits four actual unit squares in a smaller container. The violated
  sloping cuts are identified exactly, so those cuts must survive shortcuts.
- The source's archived owned hulls do not follow from bare occupancy. Its
  explicit seed counterexample blocks that promotion. New ownership must
  retain genuine initialization/ancestry.
- A favorable infinitesimal stress does not by itself certify the original
  finite capture rectangle. The round-three quantitative angular argument
  supplies the previously missing finite bound.
- In the conditional nonlinear balances, deleting square 2's angle window
  can make its support penalty negative. Common-frame projection orders also
  cannot be substituted for ordinary owner-axis nonoverlap.

**Files:** `geometric-round2/baseline/BASELINE_FINDINGS.md`,
`verify_all_case_disks.py`, `all-case-disk-countermodels.json`,
`strip/exact_strip_obstruction.py`; source
`CaptureSeedCounterexample.lean` and the support-penalty note.

### D13. Unimplemented suggestions and status rules for the final account

The following were identified as plausible refactors, **not completed
reductions**: parameterize the ordinary/tight disk-cover checker; share typed
quadtree data instead of per-node tactic proofs; unify duplicate rational
site tables; share rigid-frame/D4 transport proofs; target local span instead
of full rigidity; use the new site disk or orientation-distance constraint in
a regenerated global exclusion search.

At the old pinned snapshot, the six admissions were the three T01 baseline
plan/calculation/leaf obligations, T02 prior-support existence, T03 returned
certificate existence, and T07 case438 capture. **None was discharged by the
prior simplification packets.** T06 local isolation was already complete
upstream, and G003 was already integrated. The T03 evidence is audited separately in section A; it does not remove these admissions from the pinned Git source.

Every compiled target in our three prior rounds had only `propext`,
`Classical.choice`, and `Quot.sound`. Round three's combined audit has
**17 targets across five new modules**, recorded in
`geometric-round3/review/lean-verification.json`. These scoped results must
not be described as a fresh full optimality build. Exact Python acceptance
is likewise distinct from a concrete kernel-checked packing theorem.

Across all proposed replacements, preserve independently rotating unit
squares, legal boundary contact, strict owned interiors, closed cell/angle
ties, exact physical units, the original centered-side invariant, and
acyclic dependencies among exclusion families.

## E. How the simplifications fit together

The methods attack different burdens and should be combined in the right order.

1. **Use stronger geometry first.** A common-point trap or a small-diameter owned triangle can remove an entire pose region without subdividing its angle. The case-2135 example also makes later ownership updates unnecessary.
2. **Retain only the required ancestry.** An owned point is useful only with a proof that the original packing owns it. Keep the initialization and the updates establishing the selected points. Do not promote archived hulls from bare occupancy.
3. **Compress the remaining finite evidence.** For retained polygon covers, use facet indices and determinant identities. For triangle membership, use vertex indices and oriented areas. These reduce redundant arithmetic data without changing the geometric claim.
4. **Use the small global interface honestly.** Exclusion, strict-improvement capture, and local isolation remain separate inputs. A very short final theorem is meaningful only when all those inputs are proved.

The triangle lemma suggests a reusable search rule: for a target square, take points strictly owned by other squares; exclude their open half-unit disks and every triangle whose three sides are shorter than one. Larger finite sets of diameter below one need no new primitive in the plane: every point of their convex hull lies in the hull of at most three vertices. This could be added to a certificate search, with exact checks deciding which triangles genuinely help. Only the concrete case-2135 application is measured here.

The strongest prior local argument and the conditional finite two-balance lower bound are also distinct. The local argument allows independent small rotations and proves isolation in a quantified box. The finite two-balance argument handles a broader structural class but requires common-frame projection orders. Neither supplies global capture automatically.

## F. What remains before a small complete optimality proof

| Remaining task | Why it matters |
|---|---|
| Finish the public T03 family assembly | Individual case audits must be connected to the exact returned-family theorem. |
| Discharge the other admitted global obligations | T03 does not establish the baseline/prior-support families or case-438 capture by itself. |
| Integrate the dual-free local proof | Its exact finite calculations and generic Lean lemmas must be connected through the analytic remainder, feature, and center-propagation bridges. |
| Integrate the final G003 bar proof | Retain the four actual ownership lemmas and formalize the full geometric and arithmetic implication. |
| Apply new barriers to more T03 states | The successful case-2135 replacement does not imply that every returned case has the same obstruction. |
| Measure a regenerated, deduplicated source closure | Whole-proof line, byte, object-size, memory, and timing claims require the actual resulting proof. |

The most promising further mathematical target is **support propagation around a small cage of owners**. The large case-1311 examples suggest that only a few final support values may matter despite a long history of polygon inflation. A proved cycle of directional inequalities might replace that history. This report presents that as a research direction, not a simplification already achieved.

## G. Reproduction and source packet

The companion ZIP contains:

* This report and the complete prior-round inventory.
* `t03-simplification/geometry/`: exact case-2135 certificate, source-bound replay, independent polygon reconstruction, Lean geometry/cover/state modules, and the diagram.
* `t03-simplification/compression/`: determinant soundness, all six concrete step batches, the generator, and its exact audit.
* `t03-simplification/audit/`: theorem/admission inventory and gross/net source-closure counts.
* `t03-simplification/review/`: named-target compiler receipts, source/object hashes, and the indexed-triangle checker.
* Additive Lean-source, selected-cell initialization, and scoped-verifier patches against the pinned T03 checkout.
* The three earlier source ZIPs, unchanged, under `previous-rounds/`.
* A SHA-256 manifest of the delivered packet files.

Large public source archives, compiler objects, dependency caches, and exploratory numerical searches are omitted. Their pinned public sources and the precise scope of measurements are documented in `source-inventory.md` and its JSON. No simulation or plot is used as proof evidence.

For the exact geometric replay, with the source packet and `11SquaresT03` as siblings in the documented layout:

```bash
python3 t03-simplification/geometry/verify_triangle_barrier.py --repo 11SquaresT03
python3 t03-simplification/geometry/independent_triangle_review.py
```

For the compact implication replay, use a separate output directory if preserving delivered source bytes:

```bash
python3 t03-simplification/compression/extract_compact_implications.py \
  --formal-repo 11SquaresT03 --output-dir /tmp/eleven-compact-replay
```

These Python checks use exact arithmetic and require assertions to be enabled; do not run them with `python -O`. The packet README gives the pinned checkout, patch application, toolchain setup, and scoped Lean compilation commands. The original global admissions are not hidden by the scoped build.

Primary public references:

* [Pinned T03 source](https://github.com/Queuingtheorydotcom/11SquaresFormalized/tree/86502c40d8c04b5ee43a805a94223ca02afd3d6c)
* [Public 151-case source release](https://github.com/Queuingtheorydotcom/11SquaresFormalized/releases/tag/t03-audited-151-20260930)
* [Public upstream returned-case archives](https://github.com/wand125/n11-optimality-lean/releases/tag/n11-certs-v1)
* [Original computer-assisted proof repository](https://github.com/Queuingtheorydotcom/11SquaresOptimal)

