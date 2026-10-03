import Sqpack.S11Opt.FieldTree

/-!
A square-capture test that keeps the exact sloping cell halfplanes.
Each Bernstein containment inequality is certified by two source facets.
The certificate stores facet indices, not arbitrary linear multipliers.
All comparisons are closed, including angle endpoints and split boundaries.
-/
namespace SquarePacking.S11Opt.Simplified.PolyhedralPoint
open SquarePacking BoxTree FieldTree

abbrev Plane := ℤ × ℤ × ℤ

def det (u v : Plane) : ℤ := u.1 * v.2.1 - u.2.1 * v.1

def pairCheck (u v t : Plane) : Bool :=
  decide (0 < det u v ∧ 0 ≤ det t v ∧ 0 ≤ det u t ∧
    det t v * u.2.2 + det u t * v.2.2 ≤ det u v * t.2.2)

theorem pairCheck_sound {Q : ℕ} (u v t : Plane)
    (h : pairCheck u v t = true) (c : ℝ × ℝ)
    (hu : InHP Q u c) (hv : InHP Q v c) : InHP Q t c := by
  obtain ⟨hd, ha, hb, hc⟩ := of_decide_eq_true h
  have hd' : (0 : ℝ) < (det u v : ℝ) := by exact_mod_cast hd
  have ha' : (0 : ℝ) ≤ (det t v : ℝ) := by exact_mod_cast ha
  have hb' : (0 : ℝ) ≤ (det u t : ℝ) := by exact_mod_cast hb
  have hc' : (det t v : ℝ) * (u.2.2 : ℝ) + (det u t : ℝ) * (v.2.2 : ℝ) ≤
      (det u v : ℝ) * (t.2.2 : ℝ) := by exact_mod_cast hc
  have hua := mul_le_mul_of_nonneg_left hu ha'
  have hvb := mul_le_mul_of_nonneg_left hv hb'
  apply le_of_mul_le_mul_left (a := (det u v : ℝ)) (a0 := hd')
  try dsimp [InHP] at hua hvb ⊢
  calc
    (det u v : ℝ) * ((t.1 : ℝ) * (Q * c.1) + (t.2.1 : ℝ) * (Q * c.2)) =
      (det t v : ℝ) * ((u.1 : ℝ) * (Q * c.1) + (u.2.1 : ℝ) * (Q * c.2)) +
      (det u t : ℝ) * ((v.1 : ℝ) * (Q * c.1) + (v.2.1 : ℝ) * (Q * c.2)) := by
        simp only [det, Int.cast_sub, Int.cast_mul]
        ring
    _ ≤ (det t v : ℝ) * (u.2.2 : ℝ) + (det u t : ℝ) * (v.2.2 : ℝ) := add_le_add hua hvb
    _ ≤ (det u v : ℝ) * (t.2.2 : ℝ) := hc'

def facetCheck (hs : List Plane) (t : Plane) (ij : ℕ × ℕ) : Bool :=
  match hs[ij.1]?, hs[ij.2]? with
  | some u, some v => pairCheck u v t
  | _, _ => false

theorem facetCheck_sound {Q : ℕ} (hs : List Plane) (t : Plane) (ij : ℕ × ℕ)
    (h : facetCheck hs t ij = true) (c : ℝ × ℝ)
    (hc : ∀ h ∈ hs, InHP Q h c) : InHP Q t c := by
  unfold facetCheck at h
  cases hu : hs[ij.1]? with
  | none => simp [hu] at h
  | some u =>
    cases hv : hs[ij.2]? with
    | none => simp [hu, hv] at h
    | some v =>
      exact pairCheck_sound u v t (by simpa [hu, hv] using h) c
        (hc u (List.mem_of_getElem? hu)) (hc v (List.mem_of_getElem? hv))

def listCheck (hs : List Plane) : List Plane → List (ℕ × ℕ) → Bool
  | [], [] => true
  | t :: ts, ij :: ijs => facetCheck hs t ij && listCheck hs ts ijs
  | _, _ => false

theorem listCheck_sound {Q : ℕ} (hs ts : List Plane) (ijs : List (ℕ × ℕ))
    (h : listCheck hs ts ijs = true) (c : ℝ × ℝ) (hc : ∀ h ∈ hs, InHP Q h c) :
    ∀ t ∈ ts, InHP Q t c := by
  induction ts generalizing ijs with
  | nil => simp
  | cons t ts ih =>
    cases ijs with
    | nil => simp [listCheck] at h
    | cons ij ijs =>
      simp only [listCheck, Bool.and_eq_true] at h
      intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact facetCheck_sound hs _ ij h.1 c hc
      · exact ih ijs h.2 t' ht'

/-- Four linear containment constraints for a Bernstein direction triple. -/
def planes (Q : ℕ) (A B C : ℤ) (p : ℕ × ℕ) : List Plane :=
  [(-A, -B, C * Q - A * p.1 - B * p.2),
   (A, B, C * Q + A * p.1 + B * p.2),
   (B, -A, C * Q + B * p.1 - A * p.2),
   (-B, A, C * Q - B * p.1 + A * p.2)]

def bounds (Q A B C X Y cx cy : ℝ) : Prop :=
  A * (X - Q * cx) + B * (Y - Q * cy) ≤ C * Q ∧
  A * (Q * cx - X) + B * (Q * cy - Y) ≤ C * Q ∧
  A * (Y - Q * cy) + B * (Q * cx - X) ≤ C * Q ∧
  A * (Q * cy - Y) + B * (X - Q * cx) ≤ C * Q

theorem planes_bounds {Q : ℕ} (A B C : ℤ) (p : ℕ × ℕ) (c : ℝ × ℝ)
    (h : ∀ t ∈ planes Q A B C p, InHP Q t c) :
    bounds Q A B C p.1 p.2 c.1 c.2 := by
  have h0 := h (-A, -B, C * Q - A * p.1 - B * p.2) (by simp [planes])
  have h1 := h (A, B, C * Q + A * p.1 + B * p.2) (by simp [planes])
  have h2 := h (B, -A, C * Q + B * p.1 - A * p.2) (by simp [planes])
  have h3 := h (-B, A, C * Q - B * p.1 + A * p.2) (by simp [planes])
  simp only [InHP] at h0 h1 h2 h3
  push_cast at h0 h1 h2 h3
  dsimp [bounds]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Twelve halfplanes are the degree-two Bernstein certificate for a point. -/
def targets (Q R a b : ℕ) (p : ℕ × ℕ) : List Plane :=
  planes Q (2 * ((R : ℤ) * R - (a : ℤ) * a)) (4 * (R : ℤ) * a)
      ((R : ℤ) * R + (a : ℤ) * a) p ++
  planes Q (2 * ((R : ℤ) * R - (b : ℤ) * b)) (4 * (R : ℤ) * b)
      ((R : ℤ) * R + (b : ℤ) * b) p ++
  planes Q (2 * ((R : ℤ) * R - (a : ℤ) * b)) (2 * (R : ℤ) * (a + b))
      ((R : ℤ) * R + (a : ℤ) * b) p

theorem targets_mem {Q R a b : ℕ} (hQ : 0 < Q) (hR : 0 < R) (hb : b ≤ R)
    (p : ℕ × ℕ) (c : ℝ × ℝ) (u : ℝ)
    (hu0 : (a : ℝ) / R ≤ u) (hu1 : u ≤ (b : ℝ) / R)
    (ht : ∀ t ∈ targets Q R a b p, InHP Q t c) :
    ((p.1 : ℝ) / Q, (p.2 : ℝ) / Q) ∈ sq c (2 * Real.arctan u) 1 := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hu0' : 0 ≤ u := le_trans (div_nonneg (Nat.cast_nonneg _) hRr.le) hu0
  have hu1' : u ≤ 1 := le_trans hu1 ((div_le_one hRr).mpr (by exact_mod_cast hb))
  have hv0 : (a : ℝ) ≤ u * R := (div_le_iff₀ hRr).mp hu0
  have hv1 : u * R ≤ (b : ℝ) := (le_div_iff₀ hRr).mp hu1
  have T0 := planes_bounds (Q := Q) (2 * ((R : ℤ) * R - (a : ℤ) * a))
    (4 * (R : ℤ) * a) ((R : ℤ) * R + (a : ℤ) * a) p c
    (fun t ht' => ht t (by simp only [targets, List.mem_append]; tauto))
  have T1 := planes_bounds (Q := Q) (2 * ((R : ℤ) * R - (b : ℤ) * b))
    (4 * (R : ℤ) * b) ((R : ℤ) * R + (b : ℤ) * b) p c
    (fun t ht' => ht t (by simp only [targets, List.mem_append]; tauto))
  have Tm := planes_bounds (Q := Q) (2 * ((R : ℤ) * R - (a : ℤ) * b))
    (2 * (R : ℤ) * (a + b)) ((R : ℤ) * R + (a : ℤ) * b) p c
    (fun t ht' => ht t (by simp only [targets, List.mem_append]; tauto))
  dsimp [bounds] at T0 T1 Tm
  push_cast at T0 T1 Tm
  have L := fun {x y : ℝ}
      (h0 : 2 * ((R : ℝ) ^ 2 - a * a) * x + 4 * R * a * y ≤ (R ^ 2 + a * a) * Q)
      (h1 : 2 * ((R : ℝ) ^ 2 - b * b) * x + 4 * R * b * y ≤ (R ^ 2 + b * b) * Q)
      (hm : 2 * ((R : ℝ) ^ 2 - a * b) * x + 2 * R * (a + b) * y ≤ (R ^ 2 + a * b) * Q) =>
    lin3 (Q := (Q : ℝ)) (R := (R : ℝ)) (v := u * R) hv0 hv1
      (by rw [pow_two]; linarith) (by rw [pow_two]; linarith) hm
  have eX : ((p.1 : ℝ) / Q - c.1) * Q = p.1 - Q * c.1 := by field_simp
  have eY : ((p.2 : ℝ) / Q - c.2) * Q = p.2 - Q * c.2 := by field_simp
  rw [mem_sq_iff_gval]
  intro k
  fin_cases k
  · exact gval0_le hQr hRr hu0' hu1' (le_of_eq eX) (le_of_eq eY)
      (L (by nlinarith [T0.1]) (by nlinarith [T1.1]) (by nlinarith [Tm.1]))
  · change gval 1 _ _ _ ≤ 0
    rw [gval_one]
    exact gval0_le hQr hRr hu0' hu1'
      (by rw [neg_mul, eX]) (by rw [neg_mul, eY])
      (L (by nlinarith [T0.2.1]) (by nlinarith [T1.2.1]) (by nlinarith [Tm.2.1]))
  · change gval 2 _ _ _ ≤ 0
    rw [gval_two]
    exact gval0_le hQr hRr hu0' hu1' (le_of_eq eY)
      (by rw [neg_mul, eX])
      (L (by nlinarith [T0.2.2.1]) (by nlinarith [T1.2.2.1]) (by nlinarith [Tm.2.2.1]))
  · change gval 3 _ _ _ ≤ 0
    rw [gval_three]
    exact gval0_le hQr hRr hu0' hu1'
      (by rw [neg_mul, eY]) (le_of_eq eX)
      (L (by nlinarith [T0.2.2.2]) (by nlinarith [T1.2.2.2]) (by nlinarith [Tm.2.2.2]))

theorem checked_point_mem {Q R a b : ℕ} (hQ : 0 < Q) (hR : 0 < R) (hb : b ≤ R)
    (hs : List Plane) (p : ℕ × ℕ) (ijs : List (ℕ × ℕ))
    (h : listCheck hs (targets Q R a b p) ijs = true) (c : ℝ × ℝ) (u : ℝ)
    (hc : ∀ h ∈ hs, InHP Q h c) (hu0 : (a : ℝ) / R ≤ u) (hu1 : u ≤ (b : ℝ) / R) :
    ((p.1 : ℝ) / Q, (p.2 : ℝ) / Q) ∈ sq c (2 * Real.arctan u) 1 :=
  targets_mem hQ hR hb p c u hu0 hu1 (listCheck_sound hs _ ijs h c hc)

#print axioms pairCheck_sound
#print axioms checked_point_mem
end SquarePacking.S11Opt.Simplified.PolyhedralPoint
