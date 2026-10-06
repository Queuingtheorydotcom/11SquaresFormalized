import ElevenSquare.Endpoint
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace ElevenSquare.Pending.T06
noncomputable section

def polyLower (c : Fin 8 → ℚ) (a b : ℚ) : ℚ :=
  ∑ k, if 0 ≤ c k then c k * a ^ k.val else c k * b ^ k.val

def polyUpper (c : Fin 8 → ℚ) (a b : ℚ) : ℚ :=
  ∑ k, if 0 ≤ c k then c k * b ^ k.val else c k * a ^ k.val

def polyEval (c : Fin 8 → ℚ) (x : ℝ) : ℝ :=
  ∑ k, (c k : ℝ) * x ^ k.val

theorem poly_enclosure (c : Fin 8 → ℚ) (a b : ℚ) (x : ℝ)
    (ha : 0 ≤ a) (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ)) :
    (polyLower c a b : ℝ) ≤ polyEval c x ∧
      polyEval c x ≤ (polyUpper c a b : ℝ) := by
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hx : 0 ≤ x := haR.trans hax
  constructor
  · unfold polyLower polyEval
    push_cast
    apply Finset.sum_le_sum
    intro k _
    by_cases hc : 0 ≤ c k
    · simp only [hc, if_true]
      push_cast
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ haR hax _) (show (0 : ℝ) ≤ (c k : ℝ) by exact_mod_cast hc)
    · simp only [hc, if_false]
      push_cast
      exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hx hxb _)
        (show (c k : ℝ) ≤ 0 by exact_mod_cast (le_of_not_ge hc))
  · unfold polyUpper polyEval
    push_cast
    apply Finset.sum_le_sum
    intro k _
    by_cases hc : 0 ≤ c k
    · simp only [hc, if_true]
      push_cast
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxb _) (show (0 : ℝ) ≤ (c k : ℝ) by exact_mod_cast hc)
    · simp only [hc, if_false]
      push_cast
      exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ haR hax _)
        (show (c k : ℝ) ≤ 0 by exact_mod_cast (le_of_not_ge hc))

theorem poly_rounding_error (c : Fin 8 → ℚ) (a b v e : ℚ) (x : ℝ)
    (ha : 0 ≤ a) (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (hlo : v-e ≤ polyLower c a b) (hhi : polyUpper c a b ≤ v+e) :
    |polyEval c x - (v : ℝ)| ≤ (e : ℝ) := by
  obtain ⟨hl, hu⟩ := poly_enclosure c a b x ha hax hxb
  have hlR : (v : ℝ)-(e : ℝ) ≤ (polyLower c a b : ℝ) := by exact_mod_cast hlo
  have huR : (polyUpper c a b : ℝ) ≤ (v : ℝ)+(e : ℝ) := by exact_mod_cast hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end ElevenSquare.Pending.T06
