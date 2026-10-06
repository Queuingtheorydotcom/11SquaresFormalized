import Sqpack.S11Opt.Simplified.CorrelatedSupport
import Sqpack.S11Opt.FieldTree

/-! Exact wall/angle correlation. A container wall is retained as a quadratic
bound with positive denominator, rather than replaced by an interval minimum. -/
namespace SquarePacking.S11Opt.Simplified.CorrelatedWall
open SquarePacking BoxTree FieldTree CorrelatedSupport

abbrev Plane := ℤ × ℤ × ℤ

def denom (R : ℕ) : Quad := ⟨(R : ℚ)^2, 0, 1⟩
def lowerWall (Q R : ℕ) : Quad := ⟨-(Q : ℚ)*R^2, -2*Q*R, Q⟩
def upperWall (Q M R : ℕ) : Quad :=
  ⟨(2*(M : ℚ)-Q)*R^2, -2*Q*R, 2*M+Q⟩

@[simp] theorem denom_eval (R : ℕ) (t : ℝ) :
    (denom R).eval t = (R : ℝ)^2+t^2 := by
  simp [denom, Quad.eval]

theorem denom_pos {R : ℕ} (hR : 0 < R) (t : ℝ) : 0 < (denom R).eval t := by
  have : (0 : ℝ) < R := by exact_mod_cast hR
  rw [denom_eval]
  positivity

@[simp] theorem lowerWall_eval (Q R : ℕ) (t : ℝ) :
    (lowerWall Q R).eval t = -(Q : ℝ)*((R : ℝ)^2+2*R*t-t^2) := by
  simp only [lowerWall, Quad.eval]
  push_cast
  ring

@[simp] theorem upperWall_eval (Q M R : ℕ) (t : ℝ) :
    (upperWall Q M R).eval t =
      2*(M : ℝ)*((R : ℝ)^2+t^2)-(Q : ℝ)*((R : ℝ)^2+2*R*t-t^2) := by
  simp only [upperWall, Quad.eval]
  push_cast
  ring

def fixedSource (R : ℕ) (h : Plane) : Source :=
  ⟨h.1, h.2.1, (denom R).scale (2*(h.2.2 : ℚ))⟩

def rectPlanes (x0 x1 y0 y1 : ℕ) : List Plane :=
  [(-1, 0, -(x0 : ℤ)), (1, 0, x1), (0, -1, -(y0 : ℤ)), (0, 1, y1)]

def walls (Q M R : ℕ) : List Source :=
  [⟨-1, 0, lowerWall Q R⟩, ⟨1, 0, upperWall Q M R⟩,
   ⟨0, -1, lowerWall Q R⟩, ⟨0, 1, upperWall Q M R⟩]

def domain (Q M R : ℕ) (hs : List Plane) (x0 x1 y0 y1 : ℕ) : List Source :=
  (hs ++ rectPlanes x0 x1 y0 y1).map (fixedSource R) ++ walls Q M R

theorem fixedSource_holds {Q R : ℕ} (hR : 0 < R) (h : Plane)
    (c : ℝ × ℝ) (t : ℝ) (hh : InHP Q h c) :
    Holds (denom R) (fixedSource R h) t (Q*c.1) (Q*c.2) := by
  have hD := denom_pos hR t
  have hp := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ 2*(denom R).eval t by positivity)
  dsimp [Holds, fixedSource]
  rw [eval_scale]
  push_cast
  try dsimp [InHP] at hp
  nlinarith only [hp]

theorem wall_width_identity (Q R : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    2*(denom R).eval (u*R)*(Q*(wid (2*Real.arctan u)/2)) =
      -(lowerWall Q R).eval (u*R) := by
  rw [denom_eval, lowerWall_eval, wid_two_arctan hu0 hu1, widU]
  have hd : 1+u^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  <;> ring

theorem domain_holds {Q M R x0 x1 y0 y1 : ℕ} {hs : List Plane}
    (hQ : 0 < Q) (hR : 0 < R) (c : ℝ × ℝ) (u : ℝ)
    (hx0 : (x0 : ℝ)/Q ≤ c.1) (hx1 : c.1 ≤ (x1 : ℝ)/Q)
    (hy0 : (y0 : ℝ)/Q ≤ c.2) (hy1 : c.2 ≤ (y1 : ℝ)/Q)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hsub : sq c (2*Real.arctan u) 1 ⊆ box ((M : ℝ)/Q))
    (hin : ∀ h ∈ hs, InHP Q h c) :
    ∀ s ∈ domain Q M R hs x0 x1 y0 y1,
      Holds (denom R) s (u*R) (Q*c.1) (Q*c.2) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hD : 0 < (denom R).eval (u*R) := denom_pos hR _
  have cx0 := (div_le_iff₀ hQr).mp hx0
  have cx1 := (le_div_iff₀ hQr).mp hx1
  have cy0 := (div_le_iff₀ hQr).mp hy0
  have cy1 := (le_div_iff₀ hQr).mp hy1
  have hfixed : ∀ h ∈ hs ++ rectPlanes x0 x1 y0 y1, InHP Q h c := by
    intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hin h hh
    · simp only [rectPlanes, List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl <;>
        simp only [InHP, Int.cast_neg, Int.cast_natCast, Int.cast_one, Int.cast_zero,
          neg_mul, one_mul, zero_mul, zero_add, add_zero] <;> nlinarith
  obtain ⟨a1, a2, a3, a4⟩ := (sq_subset_box_iff _ c _).mp hsub
  have hw := wall_width_identity Q R u hu0 hu1
  have he : (upperWall Q M R).eval (u*R) =
      2*(denom R).eval (u*R)*M+(lowerWall Q R).eval (u*R) := by
    rw [upperWall_eval, lowerWall_eval, denom_eval]
    ring
  have low : ∀ z : ℝ, wid (2*Real.arctan u)/2 ≤ z →
      2*(denom R).eval (u*R)*(-(Q*z)) ≤ (lowerWall Q R).eval (u*R) := by
    intro z hz
    have hp := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2*(denom R).eval (u*R)*Q by positivity)
    nlinarith only [hp, hw]
  have high : ∀ z : ℝ, z ≤ (M : ℝ)/Q-wid (2*Real.arctan u)/2 →
      2*(denom R).eval (u*R)*(Q*z) ≤ (upperWall Q M R).eval (u*R) := by
    intro z hz
    have hp := mul_le_mul_of_nonneg_left hz hQr.le
    have hMQ : (Q : ℝ)*((M : ℝ)/Q) = M := by field_simp
    have hq : Q*z ≤ M-Q*(wid (2*Real.arctan u)/2) := by nlinarith only [hp, hMQ]
    have ht := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2*(denom R).eval (u*R) by positivity)
    nlinarith only [ht, hw, he]
  intro s hs'
  rcases List.mem_append.mp hs' with hs' | hs'
  · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hs'
    exact fixedSource_holds hR h c (u*R) (hfixed h hh)
  · simp only [walls, List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl | rfl | rfl <;>
      simp only [Holds, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
        neg_mul, one_mul, zero_mul, zero_add, add_zero]
    · exact low c.1 a1
    · exact high c.1 a2
    · exact low c.2 a3
    · exact high c.2 a4

def target0 (Q R : ℕ) (p : ℕ × ℕ) : Target :=
  ⟨⟨-2*(R : ℚ)^2, 0, 2⟩, ⟨0, -4*R, 0⟩,
   ⟨(R : ℚ)^2*(Q-2*p.1), -4*R*p.2, Q+2*p.1⟩⟩
def target1 (Q R : ℕ) (p : ℕ × ℕ) : Target :=
  ⟨⟨2*(R : ℚ)^2, 0, -2⟩, ⟨0, 4*R, 0⟩,
   ⟨(R : ℚ)^2*(Q+2*p.1), 4*R*p.2, Q-2*p.1⟩⟩
def target2 (Q R : ℕ) (p : ℕ × ℕ) : Target :=
  ⟨⟨0, 4*R, 0⟩, ⟨-2*(R : ℚ)^2, 0, 2⟩,
   ⟨(R : ℚ)^2*(Q-2*p.2), 4*R*p.1, Q+2*p.2⟩⟩
def target3 (Q R : ℕ) (p : ℕ × ℕ) : Target :=
  ⟨⟨0, -4*R, 0⟩, ⟨2*(R : ℚ)^2, 0, -2⟩,
   ⟨(R : ℚ)^2*(Q+2*p.2), -4*R*p.1, Q-2*p.2⟩⟩

def targets (Q R : ℕ) (p : ℕ × ℕ) : List Target :=
  [target0 Q R p, target1 Q R p, target2 Q R p, target3 Q R p]

theorem targets_mem {Q R : ℕ} (hQ : 0 < Q) (hR : 0 < R)
    (p : ℕ × ℕ) (c : ℝ × ℝ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (ht : ∀ z ∈ targets Q R p, Satisfies z (u*R) (Q*c.1) (Q*c.2)) :
    ((p.1 : ℝ)/Q, (p.2 : ℝ)/Q) ∈ sq c (2*Real.arctan u) 1 := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have h0 := ht (target0 Q R p) (by simp [targets])
  have h1 := ht (target1 Q R p) (by simp [targets])
  have h2 := ht (target2 Q R p) (by simp [targets])
  have h3 := ht (target3 Q R p) (by simp [targets])
  simp only [Satisfies, target0, target1, target2, target3, Quad.eval] at h0 h1 h2 h3
  push_cast at h0 h1 h2 h3
  have eX : ((p.1 : ℝ)/Q-c.1)*Q = p.1-Q*c.1 := by field_simp
  have eY : ((p.2 : ℝ)/Q-c.2)*Q = p.2-Q*c.2 := by field_simp
  rw [mem_sq_iff_gval]
  intro k
  fin_cases k
  · exact gval0_le hQr hRr hu0 hu1 (le_of_eq eX) (le_of_eq eY) (by nlinarith only [h0])
  · change gval 1 _ _ _ ≤ 0
    rw [gval_one]
    exact gval0_le hQr hRr hu0 hu1 (by rw [neg_mul, eX]) (by rw [neg_mul, eY])
      (by nlinarith only [h1])
  · change gval 2 _ _ _ ≤ 0
    rw [gval_two]
    exact gval0_le hQr hRr hu0 hu1 (le_of_eq eY) (by rw [neg_mul, eX])
      (by nlinarith only [h2])
  · change gval 3 _ _ _ ≤ 0
    rw [gval_three]
    exact gval0_le hQr hRr hu0 hu1 (by rw [neg_mul, eY]) (le_of_eq eX)
      (by nlinarith only [h3])

#print axioms domain_holds
#print axioms targets_mem
end SquarePacking.S11Opt.Simplified.CorrelatedWall
