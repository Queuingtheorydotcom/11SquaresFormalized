import ElevenSquare.Pending.S08_Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Elementary radial Taylor estimates for the trigonometric affine terms in
the center-angle chart. The bounds use only rational coefficient arithmetic
and absolute values; they require no square-root enclosure. -/

namespace ElevenSquare.Pending.T06
noncomputable section

def trigAffine (a b c d w t : ℝ) : ℝ :=
  (a + b*t)*Real.cos (w*t) + (c + d*t)*Real.sin (w*t)

def trigAffineDerivative (a b c d w t : ℝ) : ℝ :=
  trigAffine (b + w*c) (w*d) (d - w*a) (-w*b) w t

def trigAffineSecond (a b c d w t : ℝ) : ℝ :=
  trigAffine (2*w*d - w^2*a) (-w^2*b) (-2*w*b - w^2*c) (-w^2*d) w t

def trigAffineCurvature (a b c d w : ℝ) : ℝ :=
  |2*w*d - w^2*a| + |-w^2*b| + |-2*w*b - w^2*c| + |-w^2*d|

theorem trigAffine_hasDerivAt (a b c d w t : ℝ) :
    HasDerivAt (trigAffine a b c d w)
      (trigAffineDerivative a b c d w t) t := by
  have hx := (hasDerivAt_id t).const_mul w
  have hab := ((hasDerivAt_id t).const_mul b).const_add a
  have hcd := ((hasDerivAt_id t).const_mul d).const_add c
  convert (hab.fun_mul hx.cos).fun_add (hcd.fun_mul hx.sin) using 1
  · rfl
  · try dsimp [trigAffine, trigAffineDerivative]
    ring

theorem trigAffineDerivative_hasDerivAt (a b c d w t : ℝ) :
    HasDerivAt (trigAffineDerivative a b c d w)
      (trigAffineSecond a b c d w t) t := by
  convert trigAffine_hasDerivAt (b + w*c) (w*d) (d - w*a) (-w*b) w t using 1
  · rfl
  · try dsimp [trigAffineDerivative, trigAffineSecond, trigAffine]
    ring

theorem abs_affine_le (a b t : ℝ) (ht : |t| ≤ 1) :
    |a + b*t| ≤ |a| + |b| := by
  calc
    |a + b*t| ≤ |a| + |b*t| := abs_add_le _ _
    _ = |a| + |b| * |t| := by rw [abs_mul]
    _ ≤ |a| + |b| * 1 := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left ht (abs_nonneg _))
    _ = |a| + |b| := by ring

theorem trigAffine_abs_le (a b c d w t : ℝ) (ht : |t| ≤ 1) :
    |trigAffine a b c d w t| ≤ |a| + |b| + |c| + |d| := by
  have hc : |(a+b*t)*Real.cos (w*t)| ≤ |a+b*t| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (w*t))
      (abs_nonneg (a+b*t))
  have hs : |(c+d*t)*Real.sin (w*t)| ≤ |c+d*t| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (w*t))
      (abs_nonneg (c+d*t))
  unfold trigAffine
  calc
    |(a+b*t)*Real.cos (w*t) + (c+d*t)*Real.sin (w*t)| ≤
        |(a+b*t)*Real.cos (w*t)| + |(c+d*t)*Real.sin (w*t)| := abs_add_le _ _
    _ ≤ |a+b*t| + |c+d*t| := add_le_add hc hs
    _ ≤ (|a| + |b|) + (|c| + |d|) :=
      add_le_add (abs_affine_le a b t ht) (abs_affine_le c d t ht)
    _ = |a| + |b| + |c| + |d| := by ring

theorem trigAffineCurvature_nonneg (a b c d w : ℝ) :
    0 ≤ trigAffineCurvature a b c d w := by
  unfold trigAffineCurvature
  positivity

theorem trigAffineSecond_abs_le (a b c d w t : ℝ) (ht : |t| ≤ 1) :
    |trigAffineSecond a b c d w t| ≤ trigAffineCurvature a b c d w := by
  exact trigAffine_abs_le _ _ _ _ _ _ ht

theorem trigAffine_radial_taylor (a b c d w τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    |trigAffine a b c d w τ - a - τ*(b+w*c)| ≤
      τ^2*trigAffineCurvature a b c d w/2 := by
  have hb := radial_taylor_bound (trigAffine a b c d w)
    (trigAffineDerivative a b c d w) (trigAffineSecond a b c d w)
    τ (trigAffineCurvature a b c d w) hτ.1
    (trigAffineCurvature_nonneg a b c d w)
    (fun t _ => trigAffine_hasDerivAt a b c d w t)
    (fun t _ => trigAffineDerivative_hasDerivAt a b c d w t)
    (fun t ht => trigAffineSecond_abs_le a b c d w t (by
      rw [abs_of_nonneg ht.1]
      exact ht.2.trans hτ.2))
  simpa [trigAffine, trigAffineDerivative] using hb

theorem taylor_bound_add (f g : ℝ → ℝ) (a b K L τ : ℝ)
    (hf : |f τ-f 0-τ*a| ≤ τ^2*K/2)
    (hg : |g τ-g 0-τ*b| ≤ τ^2*L/2) :
    |(f τ+g τ)-(f 0+g 0)-τ*(a+b)| ≤ τ^2*(K+L)/2 := by
  calc
    |(f τ+g τ)-(f 0+g 0)-τ*(a+b)| =
        |(f τ-f 0-τ*a)+(g τ-g 0-τ*b)| := by congr 1 <;> ring
    _ ≤ |f τ-f 0-τ*a| + |g τ-g 0-τ*b| := abs_add_le _ _
    _ ≤ τ^2*K/2 + τ^2*L/2 := add_le_add hf hg
    _ = τ^2*(K+L)/2 := by ring

theorem square_le_square_of_abs_le (x X : ℝ) (hx : |x| ≤ X) : x^2 ≤ X^2 := by
  have hX : 0 ≤ X := (abs_nonneg _).trans hx
  have hp := mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hX (abs_nonneg x))
  nlinarith [sq_abs x]

theorem trigAffineCurvature_le (a b c d w A B W : ℝ)
    (ha : |a| + |c| ≤ A) (hb : |b| + |d| ≤ B) (hw : |w| ≤ W) :
    trigAffineCurvature a b c d w ≤ (A+B)*W^2+2*B*W := by
  have h1 := abs_sub (2*w*d) (w^2*a)
  have h2 := abs_sub (-2*w*b) (w^2*c)
  have hraw : trigAffineCurvature a b c d w ≤
      (|a| + |b| + |c| + |d|)*w^2+2*(|b| + |d|)* |w| := by
    unfold trigAffineCurvature
    norm_num only [abs_mul, abs_neg, abs_pow, sq_abs] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    linarith
  have hA : 0 ≤ A := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans ha
  have hB : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hb
  have hcoeff : |a| + |b| + |c| + |d| ≤ A+B := by linarith
  have hsq := square_le_square_of_abs_le w W hw
  have hfirst := (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg w)).trans
    (mul_le_mul_of_nonneg_left hsq (add_nonneg hA hB))
  have hsecond := (mul_le_mul_of_nonneg_right hb (abs_nonneg w)).trans
    (mul_le_mul_of_nonneg_left hw hB)
  linarith

end
end ElevenSquare.Pending.T06
