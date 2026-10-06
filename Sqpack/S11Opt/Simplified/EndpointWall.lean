import Sqpack.BoxTree

/-! Exact endpoint wall bounds. The half-width's superlevel inequality is a
concave quadratic, so checking both closed angle endpoints suffices. -/
namespace SquarePacking.S11Opt.Simplified
open SquarePacking BoxTree

theorem concave_quadratic_nonneg (c0 c1 c2 a b u : ℝ)
    (hc2 : c2 ≤ 0) (ha : a ≤ u) (hb : u ≤ b)
    (hA : 0 ≤ c0 + c1*a + c2*a*a)
    (hB : 0 ≤ c0 + c1*b + c2*b*b) :
    0 ≤ c0 + c1*u + c2*u*u := by
  rcases eq_or_lt_of_le (le_trans ha hb) with hab | hab
  · have hu : u = a := le_antisymm (hab ▸ hb) ha
    simpa [hu] using hA
  · have hchord : 0 ≤ (b-u)*(c0+c1*a+c2*a*a) +
        (u-a)*(c0+c1*b+c2*b*b) :=
      add_nonneg (mul_nonneg (sub_nonneg.mpr hb) hA)
        (mul_nonneg (sub_nonneg.mpr ha) hB)
    have hcorrection : 0 ≤ (-c2)*((u-a)*(b-u))*(b-a) :=
      mul_nonneg
        (mul_nonneg (neg_nonneg.mpr hc2)
          (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)))
        (sub_nonneg.mpr hab.le)
    have identity : (c0+c1*u+c2*u*u)*(b-a) =
        (b-u)*(c0+c1*a+c2*a*a) + (u-a)*(c0+c1*b+c2*b*b) +
          (-c2)*((u-a)*(b-u))*(b-a) := by ring
    have hproduct : 0 ≤ (c0+c1*u+c2*u*u)*(b-a) := by
      rw [identity]
      exact add_nonneg hchord hcorrection
    exact nonneg_of_mul_nonneg_left hproduct (sub_pos.mpr hab)

theorem widU_lower_of_endpoints {a b u w : ℝ}
    (hw : 0 ≤ w) (ha : a ≤ u) (hb : u ≤ b)
    (hA : w ≤ widU a / 2) (hB : w ≤ widU b / 2) :
    w ≤ widU u / 2 := by
  rw [widU, div_div] at hA hB ⊢
  have hA' := (le_div_iff₀ (by positivity : 0 < (1+a^2)*2)).mp hA
  have hB' := (le_div_iff₀ (by positivity : 0 < (1+b^2)*2)).mp hB
  apply (le_div_iff₀ (by positivity : 0 < (1+u^2)*2)).mpr
  have h := concave_quadratic_nonneg (1-2*w) 2 (-1-2*w) a b u
    (by linarith) ha hb (by nlinarith only [hA']) (by nlinarith only [hB'])
  nlinarith only [h]

/-- The minimum of the two exact endpoint floors, in the existing grid units. -/
def wloStrong (Q R a b : ℕ) : ℕ :=
  min (BoxTree.wlo Q R a a) (BoxTree.wlo Q R b b)

theorem wloStrong_le {Q R a b : ℕ} (hQ : 0 < Q) (hR : 0 < R)
    (hb : b ≤ R) {u : ℝ} (ha : (a : ℝ)/R ≤ u) (hu : u ≤ (b : ℝ)/R) :
    (wloStrong Q R a b : ℝ)/Q ≤ wid (2*Real.arctan u)/2 := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have ha0 : (0 : ℝ) ≤ (a : ℝ)/R := div_nonneg (Nat.cast_nonneg _) hRr.le
  have hb0 : (0 : ℝ) ≤ (b : ℝ)/R := div_nonneg (Nat.cast_nonneg _) hRr.le
  have hb1 : (b : ℝ)/R ≤ 1 := (div_le_one hRr).mpr (by exact_mod_cast hb)
  have ha1 : (a : ℝ)/R ≤ 1 := ha.trans (hu.trans hb1)
  have haR : a ≤ R := by exact_mod_cast (div_le_one hRr).mp ha1
  have hleft := BoxTree.wlo_le (Q := Q) (R := R) (U0 := a) (U1 := a)
    hQ hR haR (u := (a : ℝ)/R) le_rfl le_rfl
  have hright := BoxTree.wlo_le (Q := Q) (R := R) (U0 := b) (U1 := b)
    hQ hR hb (u := (b : ℝ)/R) le_rfl le_rfl
  have wA : wloStrong Q R a b ≤ BoxTree.wlo Q R a a := min_le_left _ _
  have wB : wloStrong Q R a b ≤ BoxTree.wlo Q R b b := min_le_right _ _
  have wA' : (wloStrong Q R a b : ℝ)/Q ≤ (BoxTree.wlo Q R a a : ℝ)/Q :=
    div_le_div_of_nonneg_right (by exact_mod_cast wA) hQr.le
  have wB' : (wloStrong Q R a b : ℝ)/Q ≤ (BoxTree.wlo Q R b b : ℝ)/Q :=
    div_le_div_of_nonneg_right (by exact_mod_cast wB) hQr.le
  rw [wid_two_arctan (ha0.trans ha) (hu.trans hb1)]
  apply widU_lower_of_endpoints (by positivity) ha hu
  · rw [← wid_two_arctan ha0 ha1]
    exact wA'.trans hleft
  · rw [← wid_two_arctan hb0 hb1]
    exact wB'.trans hright

#print axioms concave_quadratic_nonneg
#print axioms wloStrong_le
end SquarePacking.S11Opt.Simplified
