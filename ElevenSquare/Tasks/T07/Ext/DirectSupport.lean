import ElevenSquare.Tasks.T07.Ext.Check

/-! Division-free planar implication certificates.

The certificate selects at most two input halfplanes. The checker tests the
signs of the determinants and one scaled bound directly; it never constructs
the rational Farkas weights. All tests use exact rational arithmetic, and the
soundness proof applies to arbitrary halfplanes, including degenerate inputs.
The literal fallback retains the original checker for other certificates.
-/
namespace ElevenSquare.Tasks.T07.Ext.DirectSupport
open ElevenSquare ElevenSquare.Pending

inductive Support where
  | zero
  | one (facet : Nat)
  | two (first second : Nat)
  | literal (weights : List ℚ)

private theorem scaled_pair_sound {h z g : Halfplane} {u v d : ℚ}
    (hd : 0 < d) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : u * h.a + v * z.a = d * g.a)
    (hb : u * h.b + v * z.b = d * g.b)
    (hc : u * h.c + v * z.c ≤ d * g.c)
    {p : Point} (hh : h.contains p) (hz : z.contains p) : g.contains p := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hu' : (0 : ℝ) ≤ u := by exact_mod_cast hu
  have hv' : (0 : ℝ) ≤ v := by exact_mod_cast hv
  have ha' : (u : ℝ) * h.a + v * z.a = d * g.a := by exact_mod_cast ha
  have hb' : (u : ℝ) * h.b + v * z.b = d * g.b := by exact_mod_cast hb
  have hc' : (u : ℝ) * h.c + v * z.c ≤ d * g.c := by exact_mod_cast hc
  unfold Halfplane.contains at hh hz ⊢
  have he : (d : ℝ) * ((g.a : ℝ) * p.1 + (g.b : ℝ) * p.2) =
      (u : ℝ) * ((h.a : ℝ) * p.1 + (h.b : ℝ) * p.2) +
        (v : ℝ) * ((z.a : ℝ) * p.1 + (z.b : ℝ) * p.2) := by
    calc
      _ = ((u : ℝ) * h.a + v * z.a) * p.1 +
          ((u : ℝ) * h.b + v * z.b) * p.2 := by rw [ha', hb']; ring
      _ = _ := by ring
  apply le_of_mul_le_mul_left (a := (d : ℝ)) _ hd'
  rw [he]
  exact le_trans (add_le_add (mul_le_mul_of_nonneg_left hh hu')
    (mul_le_mul_of_nonneg_left hz hv')) hc'

/-- The positive-determinant orientation of a two-facet certificate. -/
def pairForwardB (h z g : Halfplane) : Bool :=
  let d := h.a * z.b - h.b * z.a
  let u := g.a * z.b - g.b * z.a
  let v := h.a * g.b - h.b * g.a
  decide (0 < d ∧ 0 ≤ u ∧ 0 ≤ v ∧ u * h.c + v * z.c ≤ d * g.c)

theorem pairForwardB_sound {h z g : Halfplane} (hc : pairForwardB h z g = true)
    {p : Point} (hh : h.contains p) (hz : z.contains p) : g.contains p := by
  obtain ⟨hd, hu, hv, hbound⟩ := of_decide_eq_true hc
  apply scaled_pair_sound hd hu hv (by ring) (by ring) hbound hh hz

/-- Either orientation is allowed. A zero determinant is rejected. -/
def pairB (h z g : Halfplane) : Bool :=
  pairForwardB h z g || pairForwardB z h g

theorem pairB_sound {h z g : Halfplane} (hc : pairB h z g = true)
    {p : Point} (hh : h.contains p) (hz : z.contains p) : g.contains p := by
  simp only [pairB, Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · exact pairForwardB_sound hc hh hz
  · exact pairForwardB_sound hc hz hh

/-- One scaled input inequality, with no division. -/
def rayB (h g : Halfplane) (d u : ℚ) : Bool :=
  decide (0 < d ∧ 0 ≤ u ∧ u * h.a = d * g.a ∧
    u * h.b = d * g.b ∧ u * h.c ≤ d * g.c)

theorem rayB_sound {h g : Halfplane} {d u : ℚ} (hc : rayB h g d u = true)
    {p : Point} (hh : h.contains p) : g.contains p := by
  obtain ⟨hd, hu, ha, hb, hbound⟩ := of_decide_eq_true hc
  apply scaled_pair_sound (z := ⟨0, 0, 0⟩) (v := 0) hd hu (le_refl 0)
    (by simpa using ha) (by simpa using hb) (by simpa using hbound) hh
  simp [Halfplane.contains]

/-- Choose a nonzero coefficient and orient its scaling positively. -/
def oneB (h g : Halfplane) : Bool :=
  let d := if h.a = 0 then h.b else h.a
  let u := if h.a = 0 then g.b else g.a
  if d < 0 then rayB h g (-d) (-u) else rayB h g d u

theorem oneB_sound {h g : Halfplane} (hc : oneB h g = true)
    {p : Point} (hh : h.contains p) : g.contains p := by
  by_cases ha : h.a = 0
  · simp only [oneB, ha, ↓reduceIte] at hc
    split at hc <;> exact rayB_sound hc hh
  · simp only [oneB, ha, ↓reduceIte] at hc
    split at hc <;> exact rayB_sound hc hh

/-- A support is untrusted data: bounds and all geometric inequalities are checked. -/
def check (P : Polygon) (g : Halfplane) : Support → Bool
  | .zero => decide (g.a = 0 ∧ g.b = 0 ∧ 0 ≤ g.c)
  | .one k => if hk : k < P.length then oneB P[k] g else false
  | .two k l =>
      if hk : k < P.length then
        if hl : l < P.length then pairB P[k] P[l] g else false
      else false
  | .literal weights => impliesB P weights g

theorem check_sound {P : Polygon} {g : Halfplane} {support : Support}
    (hc : check P g support = true) {p : Point} (hp : p ∈ P.carrier) :
    g.contains p := by
  cases support with
  | zero =>
    obtain ⟨ha, hb, hg⟩ := of_decide_eq_true hc
    have hg' : (0 : ℝ) ≤ g.c := by exact_mod_cast hg
    simpa [Halfplane.contains, ha, hb] using hg'
  | one k =>
    simp only [check] at hc
    split at hc
    · exact oneB_sound hc (hp _ (List.getElem_mem _))
    · contradiction
  | two k l =>
    simp only [check] at hc
    split at hc
    · split at hc
      · exact pairB_sound hc (hp _ (List.getElem_mem _)) (hp _ (List.getElem_mem _))
      · contradiction
    · contradiction
  | literal weights => exact impliesB_sound hc hp

/-- Check each target halfplane using one sparse support certificate. -/
def subsetB (P K : Polygon) (supports : List Support) : Bool :=
  (supports.length == K.length) && ((K.zip supports).all fun gs => check P gs.1 gs.2)

theorem subsetB_sound {P K : Polygon} {supports : List Support}
    (hc : subsetB P K supports = true) : P.carrier ⊆ K.carrier := by
  intro p hp g hg
  simp only [subsetB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨hlen, hall⟩ := hc
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hg
  have hn' : n < supports.length := hlen ▸ hn
  have hcheck := hall (K[n], supports[n]) (by
    rw [List.mem_iff_getElem]; exact ⟨n, by simp [hn, hn'], by simp⟩)
  exact check_sound hcheck hp

end ElevenSquare.Tasks.T07.Ext.DirectSupport

#print axioms ElevenSquare.Tasks.T07.Ext.DirectSupport.pairB_sound
#print axioms ElevenSquare.Tasks.T07.Ext.DirectSupport.check_sound
#print axioms ElevenSquare.Tasks.T07.Ext.DirectSupport.subsetB_sound
