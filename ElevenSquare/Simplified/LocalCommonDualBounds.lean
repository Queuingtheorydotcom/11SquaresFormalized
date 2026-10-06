import ElevenSquare.Simplified.LocalCommonChecks
import ElevenSquare.Tasks.T06.GradientErrorBounds
import ElevenSquare.Tasks.T06.Radii
import Mathlib.Tactic.Positivity

/-! Exact dual estimates for the common forty-row cone. The residual is
weighted by each coordinate's own radius, rather than by the largest radius.
The sixty-six integer certificates imply the required strict real margins. -/
namespace ElevenSquare.Simplified.LocalCommon
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06 ElevenSquare.Tasks.T06
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem radii_eq_focused (k : Fin 33) :
    (radiusQ k : ℝ) = focusedRadii k := by
  fin_cases k <;> norm_num [radiusQ, radiusNumerators, focusedRadii]

theorem radii_positive (k : Fin 33) : 0 < (radiusQ k : ℝ) := by
  rw [radii_eq_focused]
  exact (focusedRadii_bounds k).1

theorem curvature_nonneg (i : Fin 40) : 0 ≤ (curvatureQ i : ℝ) := by
  unfold curvatureQ
  positivity

theorem weight_nonneg (j : Fin 33) (s : Fin 2) (i : Fin 40) :
    0 ≤ (weight j s i : ℝ) := by
  unfold weight
  positivity

theorem cast_signInteger (s : Fin 2) : ((signInteger s : ℚ) : ℝ) = sign s := by
  fin_cases s <;> norm_num [signInteger, sign]

theorem cast_residual (j : Fin 33) (s : Fin 2) :
    (residualQ j s : ℝ) =
      ∑ k, (radiusQ k : ℝ) *
        (|(∑ i, (weight j s i : ℝ)*(matrixQ i k : ℝ)) -
            (if k=j then sign s else 0)| +
          ((1/1000000000000 : ℚ) : ℝ)*(∑ i, (weight j s i : ℝ))) := by
  simp only [residualQ, Rat.cast_sum, Rat.cast_mul, Rat.cast_add,
    Rat.cast_abs, Rat.cast_sub, apply_ite, Rat.cast_zero, cast_signInteger]

theorem residual_bound (j : Fin 33) (s : Fin 2) :
    (∑ k, (radiusQ k : ℝ) *
      |(∑ i, (weight j s i : ℝ)*polynomialGradient (rowIndex i) k) -
        (if k=j then sign s else 0)|) ≤ (residualQ j s : ℝ) := by
  rw [cast_residual]
  apply weighted_rounding
    (fun i k => polynomialGradient (rowIndex i) k)
    (fun i k => (matrixQ i k : ℝ))
    (fun i => (weight j s i : ℝ))
    (fun k => (radiusQ k : ℝ))
    (fun k => if k=j then sign s else 0)
    ((1/1000000000000 : ℚ) : ℝ)
    (weight_nonneg j s) (fun k => (radii_positive k).le)
  intro i k
  exact polynomialGradient_error_rational (rowIndex i) k

theorem strict_margin (j : Fin 33) (s : Fin 2) :
    (residualQ j s : ℝ) +
      (∑ i, (weight j s i : ℝ)*(curvatureQ i : ℝ))/2 < (radiusQ j : ℝ) := by
  have h : residualQ j s + (∑ i, weight j s i * curvatureQ i)/2 < radiusQ j := by
    exact rational_margin_of_integer (dualNumerator j s) matrixInteger
      radiusNumerators curvatureNumerator j (signInteger s) (all_integer_checks j s)
  exact_mod_cast h

end
end ElevenSquare.Simplified.LocalCommon

#print axioms ElevenSquare.Simplified.LocalCommon.radii_eq_focused
#print axioms ElevenSquare.Simplified.LocalCommon.residual_bound
#print axioms ElevenSquare.Simplified.LocalCommon.strict_margin
