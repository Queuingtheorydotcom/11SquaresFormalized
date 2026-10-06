import ElevenSquare.Pending.S08_GapFunctions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Radial Taylor bounds derived from derivative bounds, including closed endpoints. -/

namespace ElevenSquare.Pending
noncomputable section

-- One-variable Taylor along a radial segment; derivatives at closed endpoints are included.
theorem radial_taylor_bound (f f' f'' : ℝ → ℝ) (τ K : ℝ)
    (hτ : 0 ≤ τ) (hK : 0 ≤ K)
    (hd : ∀ t ∈ Set.Icc 0 τ, HasDerivAt f (f' t) t)
    (hdd : ∀ t ∈ Set.Icc 0 τ, HasDerivAt f' (f'' t) t)
    (hbound : ∀ t ∈ Set.Icc 0 τ, |f'' t| ≤ K) :
    |f τ-f 0-τ*f' 0| ≤ τ^2*K/2 := by
  have upper (g g' g'' : ℝ → ℝ)
      (hg : ∀ t ∈ Set.Icc 0 τ, HasDerivAt g (g' t) t)
      (hg' : ∀ t ∈ Set.Icc 0 τ, HasDerivAt g' (g'' t) t)
      (hgb : ∀ t ∈ Set.Icc 0 τ, |g'' t| ≤ K) :
      g τ-g 0-τ*g' 0 ≤ τ^2*K/2 := by
    have first (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : g' t-g' 0 ≤ K*t := by
      have hb := norm_image_sub_le_of_norm_deriv_le_segment'
        (fun x hx => (hg' x hx).hasDerivWithinAt)
        (fun x hx => (show ‖g'' x‖ ≤ K by
          simpa only [Real.norm_eq_abs] using hgb x ⟨hx.1, hx.2.le⟩)) t ht
      have hab : |g' t-g' 0| ≤ K*t := by simpa using hb
      exact (le_abs_self _).trans hab
    let F : ℝ → ℝ := fun t => g t-g 0-t*g' 0-t^2*K/2
    have hF (t : ℝ) (ht : t ∈ Set.Icc 0 τ) :
        HasDerivAt F (g' t-g' 0-K*t) t := by
      convert ((hg t ht).sub_const (g 0) |>.fun_sub
        ((hasDerivAt_id t).mul_const (g' 0))).fun_sub
        ((((hasDerivAt_id t).pow 2).mul_const K).div_const 2) using 1 <;> dsimp [F] <;> ring
    have hanti : AntitoneOn F (Set.Icc 0 τ) :=
      antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
        (fun t ht => (hF t (interior_subset ht)).differentiableAt.differentiableWithinAt)
        (fun t ht => by
          rw [(hF t (interior_subset ht)).deriv]
          linarith [first t (interior_subset ht)])
    have he := hanti ⟨le_rfl, hτ⟩ ⟨hτ, le_rfl⟩ hτ
    dsimp [F] at he
    nlinarith
  have hi := upper f f' f'' hd hdd hbound
  have hlo := upper (fun t => -f t) (fun t => -f' t) (fun t => -f'' t)
    (fun t ht => (hd t ht).fun_neg) (fun t ht => (hdd t ht).fun_neg)
    (fun t ht => by simpa only [abs_neg] using hbound t ht)
  exact abs_le.mpr ⟨by linarith, hi⟩

-- Elementary negative-feature test used for the 88 unavailable separation features.
theorem negative_gap_on_rectangle (f : Displacement → ℝ) (a r : Fin 33 → ℝ) (K : ℝ)
    (herror : ∀ h, InRectangle r h → |f h-f 0-LinearForm a h| ≤ K/2)
    (hmargin : f 0 + (∑ j, |a j| * r j) + K/2 < 0) :
    ∀ h, InRectangle r h → f h < 0 := by
  intro h hrect
  have herr := (abs_le.mp (herror h hrect)).2
  have hlinear : LinearForm a h ≤ ∑ j, |a j| * r j := by
    apply Finset.sum_le_sum
    intro j hj
    calc
      a j*h j ≤ |a j*h j| := le_abs_self _
      _ = |a j| * |h j| := abs_mul _ _
      _ ≤ |a j| * r j := mul_le_mul_of_nonneg_left (hrect j) (abs_nonneg _)
  linarith

-- Feasible, initially tied rows yield the required lower linear estimate.
theorem tied_gap_linear_lower (f : Displacement → ℝ) (a h : Fin 33 → ℝ) (τ K : ℝ)
    (hzero : f 0 = 0) (hfeasible : 0 ≤ f h)
    (herror : |f h-f 0-LinearForm a h| ≤ τ^2*K/2) :
    -(τ^2*K/2) ≤ LinearForm a h := by
  have he := (abs_le.mp herror).2
  rw [hzero] at he
  linarith


end
end ElevenSquare.Pending
