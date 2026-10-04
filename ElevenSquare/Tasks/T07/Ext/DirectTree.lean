import ElevenSquare.Tasks.T07.Ext.DirectSupport

/-! Optional direct-support certificates for the original T07 pruning step.

The small certificates identify source facets. Their exact arithmetic checks
prove the same half-plane containment used by the original checker, without
reconstructing long rational weight vectors. All angular checks, core checks,
partner covers, strict collision conditions, and closed split branches are
unchanged. Literal support and tree fallbacks retain all original certificates.

This prototype is not imported by the active proof. A checked step concludes
exactly `ExtStep s (replaceRows s i rs)`; no packing definition is weakened.
-/
namespace ElevenSquare.Tasks.T07.Ext
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07
noncomputable section

/-! The triangle proof is the original barycentric argument; only its three
half-plane containment certificates use direct support checks. -/
structure DirectTri where
  k : List QPoint
  v : List QPoint
  lam : List (ℚ × ℚ × ℚ)
  mus : List DirectSupport.Support

def directTriW (T : DirectTri) : List QPoint := (T.k.zip T.v).map fun kv => (kv.1.1 - kv.2.1, kv.1.2 - kv.2.2)

def DirectTri.check (T : DirectTri) (owned core : List QPoint) (P : Polygon) : Bool :=
  (T.k.length == 3) && (T.v.length == 3) && (T.lam.length == 3) && (T.mus.length == 3) &&
  (T.k.all owned.contains) && (T.v.all core.contains) &&
  (let L := fun m => T.lam.getD m (0, 0, 0)
   let W := fun m => (directTriW T).getD m (0, 0)
   decide (sum3 (fun m => (L m).1) = 0 ∧ sum3 (fun m => (L m).2.1) = 0 ∧ sum3 (fun m => (L m).2.2) = 1 ∧
     sum3 (fun m => (L m).1 * (W m).1) = 1 ∧ sum3 (fun m => (L m).2.1 * (W m).1) = 0 ∧
     sum3 (fun m => (L m).2.2 * (W m).1) = 0 ∧
     sum3 (fun m => (L m).1 * (W m).2) = 0 ∧ sum3 (fun m => (L m).2.1 * (W m).2) = 1 ∧
     sum3 (fun m => (L m).2.2 * (W m).2) = 0)) &&
  ((T.lam.zip T.mus).all fun lm => DirectSupport.check P (lamHalf lm.1) lm.2)

theorem DirectTri.sound {T : DirectTri} {owned core : List QPoint} {P : Polygon} (h : T.check owned core P = true)
    {p : Point} (hp : p ∈ P.carrier) :
    p ∈ forbiddenCenters (rationalHull owned) (convexHull ℝ (corePts core)) := by
  rcases T with ⟨tk, tv, tl, tm⟩
  simp only [DirectTri.check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hk3, hv3⟩, hl3⟩, hm3⟩, hkm⟩, hvm⟩, hid⟩, hmus⟩ := h
  obtain ⟨k0, k1, k2, rfl⟩ := List.length_eq_three.mp hk3
  obtain ⟨v0, v1, v2, rfl⟩ := List.length_eq_three.mp hv3
  obtain ⟨l0, l1, l2, rfl⟩ := List.length_eq_three.mp hl3
  obtain ⟨m0, m1, m2, rfl⟩ := List.length_eq_three.mp hm3
  simp only [directTriW, sum3, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ] at hid
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := hid
  -- the barycentric coordinates are non-negative at `p`
  have hl : ∀ l ∈ [(l0, m0), (l1, m1), (l2, m2)], 0 ≤ (l.1.1 : ℝ) * p.1 + l.1.2.1 * p.2 + l.1.2.2 := by
    intro l hlm
    have := DirectSupport.check_sound (hmus l (by simpa [List.zip] using hlm)) hp
    simp only [lamHalf, Halfplane.contains] at this; push_cast at this; linarith
  set L0 : ℝ := (l0.1 : ℝ) * p.1 + l0.2.1 * p.2 + l0.2.2
  set L1 : ℝ := (l1.1 : ℝ) * p.1 + l1.2.1 * p.2 + l1.2.2
  set L2 : ℝ := (l2.1 : ℝ) * p.1 + l2.2.1 * p.2 + l2.2.2
  have h0 : 0 ≤ L0 := hl (l0, m0) (by simp)
  have h1 : 0 ≤ L1 := hl (l1, m1) (by simp)
  have h2 : 0 ≤ L2 := hl (l2, m2) (by simp)
  have q1 : ((l0.1 + l1.1 + l2.1 : ℚ) : ℝ) = 0 := by exact_mod_cast e1
  have q2 : ((l0.2.1 + l1.2.1 + l2.2.1 : ℚ) : ℝ) = 0 := by exact_mod_cast e2
  have q3 : ((l0.2.2 + l1.2.2 + l2.2.2 : ℚ) : ℝ) = 1 := by exact_mod_cast e3
  push_cast at q1 q2 q3
  have hsum : L0 + L1 + L2 = 1 := by
    simp only [L0, L1, L2]; linear_combination p.1 * q1 + p.2 * q2 + q3
  have r4 := congrArg (fun x : ℚ => (x : ℝ)) e4
  have r5 := congrArg (fun x : ℚ => (x : ℝ)) e5
  have r6 := congrArg (fun x : ℚ => (x : ℝ)) e6
  have r7 := congrArg (fun x : ℚ => (x : ℝ)) e7
  have r8 := congrArg (fun x : ℚ => (x : ℝ)) e8
  have r9 := congrArg (fun x : ℚ => (x : ℝ)) e9
  push_cast at r4 r5 r6 r7 r8 r9
  set K : Point := L0 • realPoint k0 + L1 • realPoint k1 + L2 • realPoint k2
  set V : Point := L0 • realPoint v0 + L1 • realPoint v1 + L2 • realPoint v2
  have hK : K ∈ rationalHull owned :=
    conv3 (convex_convexHull ℝ _) (subset_convexHull ℝ {p : Point | ∃ v ∈ owned, p = realPoint v} ⟨k0, hkm k0 (by simp), rfl⟩)
      (subset_convexHull ℝ {p : Point | ∃ v ∈ owned, p = realPoint v} ⟨k1, hkm k1 (by simp), rfl⟩)
      (subset_convexHull ℝ {p : Point | ∃ v ∈ owned, p = realPoint v} ⟨k2, hkm k2 (by simp), rfl⟩) h0 h1 h2 hsum
  have hV : V ∈ convexHull ℝ (corePts core) :=
    conv3 (convex_convexHull ℝ _) (subset_convexHull ℝ (corePts core) ⟨v0, hvm v0 (by simp), rfl⟩)
      (subset_convexHull ℝ (corePts core) ⟨v1, hvm v1 (by simp), rfl⟩)
      (subset_convexHull ℝ (corePts core) ⟨v2, hvm v2 (by simp), rfl⟩) h0 h1 h2 hsum
  refine ⟨K, hK, V, hV, ?_⟩
  ext
  · simp only [K, V, L0, L1, L2, realPoint, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linear_combination (-p.1) * r4 + (-p.2) * r5 - r6
  · simp only [K, V, L0, L1, L2, realPoint, Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linear_combination (-p.1) * r7 + (-p.2) * r8 - r9

/-! Cover trees reuse the original `Good` geometric conclusion. -/
inductive DTree
  /-- Fall back to the original checked tree without changing its semantics. -/
  | literal (tree : CTree)
  | empty (mu : List ℚ)
  | keep (m : ℕ) (mus : List DirectSupport.Support)
  | forbid (j : ℕ) (T : DirectTri)
  /-- Use one convex Minkowski polygon, avoiding its artificial triangulation. -/
  | forbidHull (j : ℕ) (corners : List (ℕ × ℕ)) (mus : List DirectSupport.Support)
  | collide (k : ℕ) (mus : List DirectSupport.Support)
  | split (l : Halfplane) (le ge : DTree)

def DTree.check (C : Ctx) : Polygon → DTree → Bool
  | P, .literal tree => CTree.check C P tree
  | P, .empty mu => emptyB P mu
  | P, .keep m mus => decide (m < C.rs.length) &&
      DirectSupport.subsetB P (C.rs.getD m ⟨0, 0, []⟩).centers mus &&
      decide ((C.rs.getD m ⟨0, 0, []⟩).lo ≤ C.a) && decide (C.b ≤ (C.rs.getD m ⟨0, 0, []⟩).hi)
  | P, .forbid j T => decide (j < 11) && decide (j ≠ C.i.val) && T.check (ownedOf C.s j) C.core P
  | P, .forbidHull j corners mus =>
      decide (j < 11) && decide (j ≠ C.i.val) &&
      (corners.all fun ab => decide (ab.1 < (ownedOf C.s j).length ∧ ab.2 < C.core.length)) &&
      convexF (diffs (ownedOf C.s j) C.core corners) &&
      DirectSupport.subsetB P (edgesF (diffs (ownedOf C.s j) C.core corners)) mus
  | P, .collide k mus => decide (k < C.regs.length) &&
      convexZF (C.regs.getD k ⟨0, [], []⟩).verts &&
        DirectSupport.subsetB P (edgesF ((C.regs.getD k ⟨0, [], []⟩).verts.map toQ)) mus
  | P, .split l le ge => DTree.check C (l :: P) le && DTree.check C (negH l :: P) ge

theorem DTree.sound (C : Ctx) {q : UnitSquare} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : (C.a : ℝ) ≤ t) (hb : t ≤ C.b) (hax : q.axis = chartAxis t)
    (hreg : ∀ g ∈ C.regs, q.center ∈ convexHull ℝ (vpts (g.verts.map toQ)) →
      ∃ j : Owner, C.i ≠ j ∧ ∀ r : UnitSquare, RowsContain (C.s.rows j) r →
        rationalHull (C.s.owned j) ⊆ {p | OpenSquare r p} →
        (∀ p, ClosedSquare r p → InContainer coverCap p) → ∃ p, OpenSquare q p ∧ OpenSquare r p) :
    ∀ (T : DTree) (P : Polygon), T.check C P = true → q.center ∈ P.carrier → Good C q
  | .literal tree, P, h, hp => CTree.sound C ht0 ht1 ha hb hax hreg tree P h hp
  | .empty mu, P, h, hp => absurd hp (emptyB_sound h _)
  | .keep m mus, P, h, hp => by
    simp only [DTree.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hm, hsub⟩, hlo⟩, hhi⟩ := h
    left
    refine ⟨C.rs.getD m ⟨0, 0, []⟩, ?_, DirectSupport.subsetB_sound hsub hp, t, ht0, ht1,
      le_trans (by exact_mod_cast hlo) ha, le_trans hb (by exact_mod_cast hhi), hax⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
    exact List.getElem_mem hm
  | .forbid j T, P, h, hp => by
    simp only [DTree.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hj, hji⟩, hT⟩ := h
    right; left
    refine ⟨⟨j, hj⟩, fun e => hji (by rw [e]), ?_⟩
    have := DirectTri.sound hT hp
    simpa [ownedOf, hj] using this
  | .forbidHull j corners mus, P, h, hp => by
    simp only [DTree.check, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at h
    obtain ⟨⟨⟨⟨hj, hji⟩, hcorners⟩, hconv⟩, hsub⟩ := h
    have hh := edgesF_subset_hull hconv (DirectSupport.subsetB_sound hsub hp)
    obtain ⟨a, ha', b, hb', heq⟩ := diffs_hull hcorners hh
    right; left
    refine ⟨⟨j, hj⟩, fun e => hji (by rw [e]), a, ?_, b, ?_, heq⟩
    · simpa [ownedOf, hj, rationalHull, vpts] using ha'
    · simpa [corePts, vpts] using hb'
  | .collide k mus, P, h, hp => by
    simp only [DTree.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hk, hcv⟩, hsub⟩ := h
    right; right
    have hg : C.regs.getD k ⟨0, [], []⟩ ∈ C.regs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      exact List.getElem_mem hk
    exact hreg _ hg (edgesF_subset_hull (convexZF_imp hcv) (DirectSupport.subsetB_sound hsub hp))
  | .split l le ge, P, h, hp => by
    simp only [DTree.check, Bool.and_eq_true] at h
    by_cases hl : l.contains q.center
    · exact DTree.sound C ht0 ht1 ha hb hax hreg le (l :: P) h.1 (by
        intro g hg; rcases List.mem_cons.mp hg with rfl | hg
        · exact hl
        · exact hp g hg)
    · exact DTree.sound C ht0 ht1 ha hb hax hreg ge (negH l :: P) h.2 (by
        intro g hg; rcases List.mem_cons.mp hg with rfl | hg
        · unfold Halfplane.contains at hl ⊢; simp only [negH]; push_cast; push Not at hl; linarith
        · exact hp g hg)

/-- One angular sub-row `[a, b]` of an old row. -/
structure DirectSub where
  a : ℚ
  b : ℚ
  cuts : List SelfCut
  wall : ℚ
  core : List QPoint
  ccore : List ZPoint
  regs : List CReg
  tree : DTree

def directSubPoly (r : PoseRow) (u : DirectSub) : Polygon :=
  r.centers ++ u.cuts.map SelfCut.half ++ wallHalves u.wall

def DirectSub.check (s : PoseState) (i : Owner) (rs : List PoseRow) (pcov : ℕ → List (List PartnerPiece))
    (r : PoseRow) (u : DirectSub) : Bool :=
  (u.cuts.all fun k => k.check (s.owned i) u.a u.b) && wallB u.wall u.a u.b &&
    (u.core.all (coreVB u.a u.b)) && ((u.ccore.map toQ).all (coreVB u.a u.b)) &&
    (u.regs.all (CReg.check s i u.ccore pcov)) &&
    DTree.check ⟨s, i, rs, u.core, u.a, u.b, u.regs⟩ (directSubPoly r u) u.tree

def directRowB (s : PoseState) (i : Owner) (rs : List PoseRow) (pcov : ℕ → List (List PartnerPiece))
    (r : PoseRow) (subs : List DirectSub) : Bool :=
  coversB r.hi r.lo (subs.map fun u => (u.a, u.b)) && subs.all (DirectSub.check s i rs pcov r)

def directStepB (s : PoseState) (i : Owner) (rs : List PoseRow) (pcov : ℕ → List (List PartnerPiece))
    (certs : List (List DirectSub)) : Bool :=
  (certs.length == (s.rows i).length) &&
    (((s.rows i).zip certs).all fun rc => directRowB s i rs pcov rc.1 rc.2)

theorem directRowB_sound {s : PoseState} {i : Owner} {rs : List PoseRow} {pcov : ℕ → List (List PartnerPiece)}
    {r : PoseRow} {subs : List DirectSub}
    (hpcov : ∀ j, pcov j ≠ [] → pcovB s j (pcov j) = true)
    (h : directRowB s i rs pcov r subs = true) {q : UnitSquare} (hr : r.contains q)
    (hown : rationalHull (s.owned i) ⊆ {p | OpenSquare q p})
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p) :
    RowsContain rs q ∨
      (∃ j : Owner, i ≠ j ∧ ∃ Q : Set Point,
        CoreFits Q q ∧ q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q) ∨
      (∃ j : Owner, i ≠ j ∧ ∀ r : UnitSquare, RowsContain (s.rows j) r →
        rationalHull (s.owned j) ⊆ {p | OpenSquare r p} →
        (∀ p, ClosedSquare r p → InContainer coverCap p) →
        ∃ p, OpenSquare q p ∧ OpenSquare r p) := by
  simp only [directRowB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hcov, hsubs⟩ := h
  obtain ⟨hc, t, ht0, ht1, hlo, hhi, hax⟩ := hr
  obtain ⟨uu, huu, hua, hub⟩ := coversB_sound r.hi r.lo _ hcov t hlo hhi
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp huu
  have hU := hsubs u hu
  simp only [DirectSub.check, Bool.and_eq_true, List.all_eq_true] at hU
  obtain ⟨⟨⟨⟨⟨hcuts, hwall⟩, hcore⟩, hccore⟩, hregs⟩, htree⟩ := hU
  have hQ := core_fits (List.all_eq_true.mpr hcore) hua hub hax
  have hQc := core_fits (List.all_eq_true.mpr hccore) hua hub hax
  have hP : q.center ∈ (directSubPoly r u).carrier := by
    intro l hl
    simp only [directSubPoly, List.mem_append, List.mem_map] at hl
    rcases hl with (hl | ⟨k, hk, rfl⟩) | hl
    · exact hc l hl
    · exact SelfCut.sound (hcuts k hk) hua hub hax hown
    · exact wall_sound hwall hua hub hax hcont l hl
  rcases DTree.sound ⟨s, i, rs, u.core, u.a, u.b, u.regs⟩ ht0 ht1 hua hub hax
      (fun g hg hcg => CReg.sound hpcov (hregs g hg) hcg hQc) u.tree (directSubPoly r u) htree hP with
    hkeep | ⟨j, hij, hf⟩ | hcol
  · exact Or.inl hkeep
  · exact Or.inr (Or.inl ⟨j, hij, _, hQ, hf⟩)
  · exact Or.inr (Or.inr hcol)

/-- **Soundness of a checked step.** -/
theorem directStepB_sound {s : PoseState} {i : Owner} {rs : List PoseRow} {pcov : ℕ → List (List PartnerPiece)}
    {certs : List (List DirectSub)}
    (hpcov : ∀ j, pcov j ≠ [] → pcovB s j (pcov j) = true)
    (h : directStepB s i rs pcov certs = true) : ExtStep s (replaceRows s i rs) := by
  apply ExtStep.pruneOwned
  intro q ⟨r, hr, hc⟩ hown hcont
  simp only [directStepB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hr
  have hn' : n < certs.length := hlen ▸ hn
  have hmem : ((s.rows i)[n], certs[n]) ∈ (s.rows i).zip certs := by
    rw [List.mem_iff_getElem]; exact ⟨n, by simp [hn, hn'], by simp⟩
  exact directRowB_sound hpcov (hall _ hmem) hc hown hcont

/-- A step checked row by row (to split large steps across files). -/
theorem directStepB_of_rows {s : PoseState} {i : Owner} {rs : List PoseRow}
    {pcov : ℕ → List (List PartnerPiece)} {certs : List (List DirectSub)}
    (hlen : certs.length = (s.rows i).length)
    (h : ∀ n < (s.rows i).length,
      directRowB s i rs pcov ((s.rows i).getD n ⟨0, 0, []⟩) (certs.getD n []) = true) :
    directStepB s i rs pcov certs = true := by
  simp only [directStepB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨hlen, fun rc hrc => ?_⟩
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hrc
  have hn1 : n < (s.rows i).length := by simp at hn; omega
  have hn2 : n < certs.length := by simp at hn; omega
  have := h n hn1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn1, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn2, Option.getD_some] at this
  simpa [List.getElem_zip] using this

namespace DirectChain

/-- The constructor name identifies the branch that continues down the spine. -/
inductive Cut where
  | left (plane : Halfplane) (side : DTree)
  | right (plane : Halfplane) (side : DTree)

/-- Reconstruct both closed branches consumed by the direct checker. -/
def build : List Cut → DTree → DTree
  | [], last => last
  | .left plane side :: cuts, last => .split plane (build cuts last) side
  | .right plane side :: cuts, last => .split plane side (build cuts last)

theorem build_nil (last : DTree) : build [] last = last := rfl

theorem build_left (plane : Halfplane) (side : DTree) (cuts : List Cut)
    (last : DTree) :
    build (.left plane side :: cuts) last = .split plane (build cuts last) side := rfl

theorem build_right (plane : Halfplane) (side : DTree) (cuts : List Cut)
    (last : DTree) :
    build (.right plane side :: cuts) last = .split plane side (build cuts last) := rfl

end DirectChain

def directRowBlockB (s : PoseState) (i : Owner) (rs : List PoseRow)
    (pcov : ℕ → List (List PartnerPiece)) (certs : List (List DirectSub))
    (start width : ℕ) : Bool :=
  (List.range width).all fun k =>
    if start + k < (s.rows i).length then
      directRowB s i rs pcov ((s.rows i).getD (start + k) ⟨0, 0, []⟩)
        (certs.getD (start + k) [])
    else true

theorem directStepB_of_row_blocks {s : PoseState} {i : Owner} {rs : List PoseRow}
    {pcov : ℕ → List (List PartnerPiece)} {certs : List (List DirectSub)}
    {width blocks : ℕ} (hwidth : 0 < width)
    (hlen : certs.length = (s.rows i).length)
    (hcover : (s.rows i).length ≤ blocks * width)
    (hblocks : ∀ b < blocks, directRowBlockB s i rs pcov certs (b * width) width = true) :
    directStepB s i rs pcov certs = true := by
  apply directStepB_of_rows hlen
  intro n hn
  have hb : n / width < blocks :=
    (Nat.div_lt_iff_lt_mul hwidth).mpr (lt_of_lt_of_le hn hcover)
  have h := hblocks (n / width) hb
  rw [directRowBlockB, List.all_eq_true] at h
  have hrem := h (n % width) (List.mem_range.mpr (Nat.mod_lt n hwidth))
  have he : n / width * width + n % width = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n width
  simpa only [he, hn, ↓reduceIte] using hrem

end
end ElevenSquare.Tasks.T07.Ext

#print axioms ElevenSquare.Tasks.T07.Ext.DirectTri.sound
#print axioms ElevenSquare.Tasks.T07.Ext.DTree.sound
#print axioms ElevenSquare.Tasks.T07.Ext.directStepB_sound

#print axioms ElevenSquare.Tasks.T07.Ext.directStepB_of_row_blocks
