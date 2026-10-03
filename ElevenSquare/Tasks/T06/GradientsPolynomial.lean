import ElevenSquare.ConstructionData
import ElevenSquare.Tasks.T06.DataGradients
import Mathlib.Tactic.Ring

namespace ElevenSquare.Pending.T06
noncomputable section

theorem polyEval_expand (c : Fin 8 → ℚ) (x : ℝ) :
    polyEval c x = (c 0 : ℝ) + (c 1 : ℝ)*x + (c 2 : ℝ)*x^2 +
      (c 3 : ℝ)*x^3 + (c 4 : ℝ)*x^4 + (c 5 : ℝ)*x^5 +
      (c 6 : ℝ)*x^6 + (c 7 : ℝ)*x^7 := by
  simp [polyEval, Fin.sum_univ_succ, Fin.succ]
  ring

theorem polyEval_vec (a b c d e f g h : ℚ) (x : ℝ) :
    polyEval ![a, b, c, d, e, f, g, h] x =
      (a : ℝ) + (b : ℝ)*x + (c : ℝ)*x^2 + (d : ℝ)*x^3 +
      (e : ℝ)*x^4 + (f : ℝ)*x^5 + (g : ℝ)*x^6 + (h : ℝ)*x^7 :=
  polyEval_expand ![a, b, c, d, e, f, g, h] x

/-- Reduce any construction identity modulo the same endpoint polynomial.
The supplied multiple is a checked algebraic certificate, not an extra premise. -/
theorem construction_eq_of_polynomial_multiple {x y : ℝ} (q : ℝ)
    (h : x - y = q * endpointPolynomial u) : x = y := by
  apply sub_eq_zero.mp
  rw [h, u_polynomial, mul_zero]

end
end ElevenSquare.Pending.T06
