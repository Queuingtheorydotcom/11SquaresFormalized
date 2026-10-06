import Sqpack.S11Opt.Simplified.PolyhedralPoint

/-! Three active halfplanes can exclude a planar cell even when no individual
cell halfplane excludes its rectangular enclosure. The certificate stores only
the three facet indices; its nonnegative Farkas weights are determinants. -/
namespace SquarePacking.S11Opt.Simplified.PolyhedralEmpty
open FieldTree PolyhedralPoint

def tripleCheck (u v w : Plane) : Bool :=
  decide (0 ≤ det v w ∧ 0 ≤ det w u ∧ 0 ≤ det u v ∧
    det v w * u.2.2 + det w u * v.2.2 + det u v * w.2.2 < 0)

theorem tripleCheck_sound {Q : ℕ} (u v w : Plane)
    (h : tripleCheck u v w = true) (c : ℝ × ℝ)
    (hu : InHP Q u c) (hv : InHP Q v c) (hw : InHP Q w c) : False := by
  obtain ⟨ha, hb, hc, hd⟩ := of_decide_eq_true h
  have ha' : (0 : ℝ) ≤ (det v w : ℝ) := by exact_mod_cast ha
  have hb' : (0 : ℝ) ≤ (det w u : ℝ) := by exact_mod_cast hb
  have hc' : (0 : ℝ) ≤ (det u v : ℝ) := by exact_mod_cast hc
  have hd' : (det v w : ℝ) * (u.2.2 : ℝ) +
      (det w u : ℝ) * (v.2.2 : ℝ) + (det u v : ℝ) * (w.2.2 : ℝ) < 0 := by
    exact_mod_cast hd
  have hua := mul_le_mul_of_nonneg_left hu ha'
  have hvb := mul_le_mul_of_nonneg_left hv hb'
  have hwc := mul_le_mul_of_nonneg_left hw hc'
  have hid : (det v w : ℝ) * ((u.1 : ℝ) * (Q * c.1) + (u.2.1 : ℝ) * (Q * c.2)) +
      (det w u : ℝ) * ((v.1 : ℝ) * (Q * c.1) + (v.2.1 : ℝ) * (Q * c.2)) +
      (det u v : ℝ) * ((w.1 : ℝ) * (Q * c.1) + (w.2.1 : ℝ) * (Q * c.2)) = 0 := by
    simp only [det, Int.cast_sub, Int.cast_mul]
    ring
  have hs := add_le_add (add_le_add hua hvb) hwc
  try dsimp only [InHP] at hs
  rw [hid] at hs
  exact (not_lt_of_ge hs) hd'

def check (hs : List Plane) (ijk : ℕ × ℕ × ℕ) : Bool :=
  match hs[ijk.1]?, hs[ijk.2.1]?, hs[ijk.2.2]? with
  | some u, some v, some w => tripleCheck u v w
  | _, _, _ => false

theorem check_sound {Q : ℕ} (hs : List Plane) (ijk : ℕ × ℕ × ℕ)
    (h : check hs ijk = true) (c : ℝ × ℝ)
    (hc : ∀ p ∈ hs, InHP Q p c) : False := by
  unfold check at h
  cases hu : hs[ijk.1]? with
  | none => simp [hu] at h
  | some u =>
    cases hv : hs[ijk.2.1]? with
    | none => simp [hu, hv] at h
    | some v =>
      cases hw : hs[ijk.2.2]? with
      | none => simp [hu, hv, hw] at h
      | some w =>
        exact tripleCheck_sound u v w (by simpa [hu, hv, hw] using h) c
          (hc u (List.mem_of_getElem? hu)) (hc v (List.mem_of_getElem? hv))
          (hc w (List.mem_of_getElem? hw))

#print axioms check_sound
end SquarePacking.S11Opt.Simplified.PolyhedralEmpty
