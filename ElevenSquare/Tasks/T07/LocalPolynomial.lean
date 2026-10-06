import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! A small interval evaluator for witness-coordinate polynomials. Every
endpoint sum has only rational arithmetic when the interval endpoints are
rational, while the argument may be the algebraic root `u`. -/

namespace ElevenSquare.Tasks.T07
noncomputable section

def polynomialAt {n : ℕ} (c : Fin n → ℚ) (x : ℝ) : ℝ :=
  ∑ i, (c i : ℝ) * x ^ i.val

def polynomialLower {n : ℕ} (c : Fin n → ℚ) (lo hi : ℝ) : ℝ :=
  ∑ i, if 0 ≤ c i then (c i : ℝ) * lo ^ i.val else (c i : ℝ) * hi ^ i.val

def polynomialUpper {n : ℕ} (c : Fin n → ℚ) (lo hi : ℝ) : ℝ :=
  ∑ i, if 0 ≤ c i then (c i : ℝ) * hi ^ i.val else (c i : ℝ) * lo ^ i.val

theorem polynomial_interval {n : ℕ} (c : Fin n → ℚ) {lo x hi : ℝ}
    (hlo : 0 ≤ lo) (hlx : lo ≤ x) (hxh : x ≤ hi) :
    polynomialLower c lo hi ≤ polynomialAt c x ∧
      polynomialAt c x ≤ polynomialUpper c lo hi := by
  have hx : 0 ≤ x := hlo.trans hlx
  have hxl (i : Fin n) : lo ^ i.val ≤ x ^ i.val :=
    pow_le_pow_left₀ hlo hlx i.val
  have hxu (i : Fin n) : x ^ i.val ≤ hi ^ i.val :=
    pow_le_pow_left₀ hx hxh i.val
  constructor
  · unfold polynomialLower polynomialAt
    apply Finset.sum_le_sum
    intro i _
    by_cases hc : 0 ≤ c i
    · simp only [if_pos hc]
      exact mul_le_mul_of_nonneg_left (hxl i) (by exact_mod_cast hc)
    · simp only [if_neg hc]
      have hc' : (c i : ℝ) ≤ 0 := by exact_mod_cast le_of_lt (lt_of_not_ge hc)
      exact mul_le_mul_of_nonpos_left (hxu i) hc'
  · unfold polynomialAt polynomialUpper
    apply Finset.sum_le_sum
    intro i _
    by_cases hc : 0 ≤ c i
    · simp only [if_pos hc]
      exact mul_le_mul_of_nonneg_left (hxu i) (by exact_mod_cast hc)
    · simp only [if_neg hc]
      have hc' : (c i : ℝ) ≤ 0 := by exact_mod_cast le_of_lt (lt_of_not_ge hc)
      exact mul_le_mul_of_nonpos_left (hxl i) hc'

end
end ElevenSquare.Tasks.T07
