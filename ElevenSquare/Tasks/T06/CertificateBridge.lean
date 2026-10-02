import ElevenSquare.Tasks.T06.Residual
import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateChecks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ElevenSquare.Tasks.T06

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open ElevenSquare ElevenSquare.Pending

theorem rowCurvatures_eq_scaled_numerators (i : Fin 56) :
    rowCurvatures i = (curvatureNumerators i : ℚ) / 1000000000000 := by
  fin_cases i <;> norm_num [rowCurvatures, curvatureNumerators]

theorem coordinateRadiiQ_eq_scaled_numerators (j : Fin 33) :
    coordinateRadiiQ j = (radiusNumerators j : ℚ) / 10000000000 := by
  fin_cases j <;> norm_num [coordinateRadiiQ, radiusNumerators]

theorem rational_residual_of_integer
    (b : Fin 128) (j : Fin 33) (s : Fin 2) (nums : Fin 42 → ℕ)
    (hcheck : integerResidualCheck b j s nums) :
    certificateResidualCheck b j s nums
      ((residualNumerators b j s : ℚ) / 1000000000000000000000000) := by
  have hsign : (((![-1, 1] : Fin 2 → ℤ) s : ℤ) : ℚ) =
      (![-1, 1] : Fin 2 → ℚ) s := by
    fin_cases s <;> norm_num
  have h := rational_residual_check_of_integer_check
    (fun i => (nums i : ℤ))
    (fun i k => roundedGradients (branchRows b i) k)
    (fun k => if k = j then (![-1, 1] : Fin 2 → ℤ) s else 0)
    1000000000000 (residualNumerators b j s : ℤ) (by norm_num) (by
      simpa only [integerResidualCheck, show (1000000000000 : ℤ) ^ 2 =
        1000000000000000000000000 by norm_num, mul_ite, mul_zero, zero_mul, mul_comm] using hcheck)
  simpa only [certificateResidualCheck, certificateWeight, certificateMatrix,
    Int.cast_natCast, Int.cast_ofNat, apply_ite, Int.cast_zero, hsign,
    show (1000000000000 : ℚ) ^ 2 = 1000000000000000000000000 by norm_num] using h

theorem rational_mass_of_integer
    (b : Fin 128) (j : Fin 33) (s : Fin 2) (nums : Fin 42 → ℕ)
    (hcheck : integerMassCheck b j s nums) :
    certificateMassCheck b j nums
      ((residualNumerators b j s : ℚ) / 1000000000000000000000000) := by
  unfold integerMassCheck at hcheck
  have hcheck' :
      (∑ i, (nums i : ℚ) * (curvatureNumerators (branchRows b i) : ℚ)) * 10000000000 +
        2 * (residualNumerators b j s : ℚ) * 67647473 <
      2 * (radiusNumerators j : ℚ) * 1000000000000000000000000 := by
    exact_mod_cast hcheck
  unfold certificateMassCheck certificateWeight
  simp_rw [rowCurvatures_eq_scaled_numerators]
  rw [coordinateRadiiQ_eq_scaled_numerators]
  have hsum :
      (∑ i, ((nums i : ℚ) / 1000000000000) *
        ((curvatureNumerators (branchRows b i) : ℚ) / 1000000000000)) =
      (∑ i, (nums i : ℚ) * (curvatureNumerators (branchRows b i) : ℚ)) /
        1000000000000000000000000 := by
    simp only [div_mul_div_comm]
    rw [← Finset.sum_div]
    norm_num
  rw [hsum]
  unfold maxRadiusQ
  linarith

end ElevenSquare.Tasks.T06
