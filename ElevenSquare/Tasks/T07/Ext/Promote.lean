import ElevenSquare.Tasks.T07.Ext.Check

/-! A checker for the promotion that ends an archived step.

After the rows of owner `i` are replaced, the archive promotes *kernel points*
`κ` that lie in the open square of every remaining pose, and then replaces the
owned list of `i` by points `v`, each a convex combination of old owned points
and kernel points.  This is `VerifiedStep.promoteOwned`.

For a row `m` (angle interval `[lo, hi]`, centres inside the hull of `cv`) and a
core `Q` valid on `[lo, hi]`, a kernel point `κ` lies in every square of the row
when `κ - c` satisfies every edge of `Q` for every centre vertex `c`
(`κ - c ∈ hull Q`, then `CoreFits`). -/
namespace ElevenSquare.Tasks.T07.Ext
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07
noncomputable section

/-- The certificate of one row: its core, its centre vertices, and a Farkas
certificate that the row centres lie in the hull of the centre vertices. -/
structure PRow where
  core : List QPoint
  cv : List QPoint
  mus : List (List ℚ)

def PRow.check (r : PoseRow) (kern : List QPoint) (pr : PRow) : Bool :=
  (pr.core.all (coreVB r.lo r.hi)) && convexF pr.core && convexF pr.cv &&
    subsetB r.centers (edgesF pr.cv) pr.mus &&
    (kern.all fun κ => (edgesF pr.core).all fun e =>
      decide (e.a * κ.1 + e.b * κ.2 + supp pr.cv (-e.a) (-e.b) ≤ e.c))

/-- A new owned point as a convex combination of three points of `pts`. -/
structure Comb where
  v : QPoint
  w : List (QPoint × ℚ)

def Comb.check (pts : List QPoint) (c : Comb) : Bool :=
  (c.w.length == 3) && (c.w.all fun pw => pts.contains pw.1 && decide (0 ≤ pw.2)) &&
    decide ((c.w.map Prod.snd).sum = 1) &&
    decide ((c.w.map fun pw => pw.2 * pw.1.1).sum = c.v.1) &&
    decide ((c.w.map fun pw => pw.2 * pw.1.2).sum = c.v.2)

def promoteB (s : PoseState) (i : Owner) (kern : List QPoint) (prs : List PRow)
    (combs : List Comb) : Bool :=
  (prs.length == (s.rows i).length) &&
    (((s.rows i).zip prs).all fun rp => rp.2.check rp.1 kern) &&
    (combs.all (Comb.check (s.owned i ++ kern)))

lemma openSquare_convex (q : UnitSquare) : Convex ℝ {p : Point | OpenSquare q p} := by
  intro x hx y hy s t hs ht hst
  have hx' : OpenSquare q (q.center + (x - q.center)) := by simpa using hx
  have hy' : OpenSquare q (q.center + (y - q.center)) := by simpa using hy
  have := openSquare_shift_convex q hx' hy' hs ht hst
  simp only [Set.mem_ofPred_eq] at this ⊢
  have h1 : s • q.center + t • q.center = q.center := by rw [← add_smul, hst, one_smul]
  have e : q.center + (s • (x - q.center) + t • (y - q.center)) = s • x + t • y := by
    calc q.center + (s • (x - q.center) + t • (y - q.center))
        = s • x + t • y + (q.center - (s • q.center + t • q.center)) := by simp only [smul_sub]; abel
      _ = s • x + t • y := by rw [h1, sub_self, add_zero]
  rwa [e] at this

/-- A kernel point lies in every square of a checked row. -/
theorem PRow.sound {r : PoseRow} {kern : List QPoint} {pr : PRow} (h : pr.check r kern = true)
    {κ : QPoint} (hκ : κ ∈ kern) {q : UnitSquare} (hq : r.contains q) :
    OpenSquare q (realPoint κ) := by
  simp only [PRow.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hcore, hcq⟩, hcv⟩, hsub⟩, hk⟩ := h
  obtain ⟨hc, t, ht0, ht1, hlo, hhi, hax⟩ := hq
  have hQ := core_fits (List.all_eq_true.mpr hcore) hlo hhi hax
  have hcen : q.center ∈ convexHull ℝ (vpts pr.cv) := edgesF_subset_hull hcv (subsetB_sound hsub hc)
  have hz : realPoint κ - q.center ∈ (edgesF pr.core).carrier := by
    intro e he
    have h1 := hull_contains (g := ⟨-e.a, -e.b, supp pr.cv (-e.a) (-e.b)⟩)
      (fun v hv => by simp only [Halfplane.contains, realPoint]; exact_mod_cast le_supp hv) hcen
    have h2 : ((e.a * κ.1 + e.b * κ.2 + supp pr.cv (-e.a) (-e.b) : ℚ) : ℝ) ≤ e.c := by
      exact_mod_cast hk κ hκ e he
    simp only [Halfplane.contains] at h1 ⊢
    simp only [realPoint, Prod.fst_sub, Prod.snd_sub]
    push_cast at h1 h2
    linarith
  have := hQ _ (edgesF_subset_hull hcq hz)
  simpa using this

/-- **Soundness of a checked promotion.** -/
theorem promoteB_sound {s : PoseState} {i : Owner} {kern : List QPoint} {prs : List PRow}
    {combs : List Comb} (h : promoteB s i kern prs combs = true) :
    VerifiedStep s (replaceHull s i (combs.map Comb.v)) := by
  simp only [promoteB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hlen, hrows⟩, hcombs⟩ := h
  apply VerifiedStep.promoteOwned
  intro q ⟨r, hr, hc⟩ hown v hv
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hr
  have hn' : n < prs.length := hlen ▸ hn
  have hmem : ((s.rows i)[n], prs[n]) ∈ (s.rows i).zip prs := by
    rw [List.mem_iff_getElem]; exact ⟨n, by simp [hn, hn'], by simp⟩
  have hpr := hrows _ hmem
  -- every point of `owned i ++ kern` lies in the open square
  have hpts : ∀ p ∈ s.owned i ++ kern, OpenSquare q (realPoint p) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hown (subset_convexHull ℝ _ ⟨p, hp, rfl⟩)
    · exact PRow.sound hpr hp hc
  obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hv
  have hC := hcombs c hcm
  simp only [Comb.check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem,
    decide_eq_true_eq] at hC
  obtain ⟨⟨⟨⟨hl3, hw⟩, hsum⟩, hx⟩, hy⟩ := hC
  obtain ⟨p0, p1, p2, hw3⟩ := List.length_eq_three.mp hl3
  rw [hw3] at hw hsum hx hy
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum hx hy
  have m0 := hw p0 (by simp); have m1 := hw p1 (by simp); have m2 := hw p2 (by simp)
  have hconv := openSquare_convex q
  have hmem3 := conv3 (a := (p0.2 : ℝ)) (b := (p1.2 : ℝ)) (c := (p2.2 : ℝ)) hconv
    (hpts _ m0.1) (hpts _ m1.1) (hpts _ m2.1)
    (by exact_mod_cast m0.2) (by exact_mod_cast m1.2) (by exact_mod_cast m2.2)
    (by rw [add_assoc]; exact_mod_cast hsum)
  have e : realPoint c.v = (p0.2 : ℝ) • realPoint p0.1 + (p1.2 : ℝ) • realPoint p1.1
      + (p2.2 : ℝ) • realPoint p2.1 := by
    ext
    · simp only [realPoint, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; rw [← hx]; push_cast; ring
    · simp only [realPoint, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; rw [← hy]; push_cast; ring
  rw [e]; exact hmem3

end
end ElevenSquare.Tasks.T07.Ext
