import ElevenSquare.Simplified.LocalCommonCore
import ElevenSquare.Tasks.T06.RecursiveCertificate
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! The common forty-row cone needs only 66 small rational duals.
This module checks their integer numerators and transports the result to the
radius-weighted real residual norm. Every transformation is dimension-generic.
-/
namespace ElevenSquare.Simplified.LocalCommon
open scoped BigOperators

/-- Integer form of the weighted residual and curvature margin. -/
def IntegerCheck {m n : ℕ} (a : Fin m → ℕ) (M : Fin m → Fin n → ℤ)
    (r : Fin n → ℕ) (K : Fin m → ℕ) (j : Fin n) (σ : ℤ) : Prop :=
  2 * (∑ k, (r k : ℤ) *
    (|(∑ i, (a i : ℤ)*M i k) - (if k=j then σ*1000000000000000 else 0)| +
      ∑ i, (a i : ℤ))) +
    10000000000 * (∑ i, (a i : ℤ)*(K i : ℤ)) <
    2 * 1000000000000000 * (r j : ℤ)

instance {m n : ℕ} (a : Fin m → ℕ) (M : Fin m → Fin n → ℤ)
    (r : Fin n → ℕ) (K : Fin m → ℕ) (j : Fin n) (σ : ℤ) :
    Decidable (IntegerCheck a M r K j σ) := by
  unfold IntegerCheck
  infer_instance

/-- Clearing fixed positive denominators turns the kernel's integer check into
exact rational residual and curvature bounds. -/
theorem rational_margin_of_integer {m n : ℕ}
    (a : Fin m → ℕ) (M : Fin m → Fin n → ℤ)
    (r : Fin n → ℕ) (K : Fin m → ℕ) (j : Fin n) (σ : ℤ)
    (h : IntegerCheck a M r K j σ) :
    (∑ k, ((r k : ℚ)/10000000000) *
      (|(∑ i, ((a i : ℚ)/1000)*((M i k : ℚ)/1000000000000)) -
        (if k=j then (σ : ℚ) else 0)| +
        (1/1000000000000)*(∑ i, (a i : ℚ)/1000))) +
    (∑ i, ((a i : ℚ)/1000)*((K i : ℚ)/1000000000000))/2 <
      (r j : ℚ)/10000000000 := by
  unfold IntegerCheck at h
  have hq :
      2 * (∑ k, (r k : ℚ) *
        (|(∑ i, (a i : ℚ)*(M i k : ℚ)) -
          (if k=j then (σ : ℚ)*1000000000000000 else 0)| +
          ∑ i, (a i : ℚ))) +
        10000000000 * (∑ i, (a i : ℚ)*(K i : ℚ)) <
      2 * 1000000000000000 * (r j : ℚ) := by
    exact_mod_cast h
  have row (k : Fin n) :
      (∑ i, ((a i : ℚ)/1000)*((M i k : ℚ)/1000000000000)) -
        (if k=j then (σ : ℚ) else 0) =
      ((∑ i, (a i : ℚ)*(M i k : ℚ)) -
        (if k=j then (σ : ℚ)*1000000000000000 else 0))/1000000000000000 := by
    simp only [div_mul_div_comm, ← Finset.sum_div]
    by_cases hk : k=j <;> simp only [hk, if_true, if_false] <;> ring
  have error : (1/1000000000000 : ℚ)*(∑ i, (a i : ℚ)/1000) =
      (∑ i, (a i : ℚ))/1000000000000000 := by
    rw [← Finset.sum_div]
    ring
  have mass : (∑ i, ((a i : ℚ)/1000)*((K i : ℚ)/1000000000000))/2 =
      (∑ i, (a i : ℚ)*(K i : ℚ))/2000000000000000 := by
    simp only [div_mul_div_comm, ← Finset.sum_div]
    ring
  have radius_error :
      (∑ k, ((r k : ℚ)/10000000000) *
        (|(∑ i, ((a i : ℚ)/1000)*((M i k : ℚ)/1000000000000)) -
          (if k=j then (σ : ℚ) else 0)| +
          (1/1000000000000)*(∑ i, (a i : ℚ)/1000))) =
      (∑ k, (r k : ℚ) *
        (|(∑ i, (a i : ℚ)*(M i k : ℚ)) -
          (if k=j then (σ : ℚ)*1000000000000000 else 0)| +
          ∑ i, (a i : ℚ)))/10000000000000000000000000 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [row, error, abs_div]
    norm_num <;> ring
  rw [radius_error, mass]
  linarith

/-- Rounding every gradient entry by at most δ bounds a rectangle-weighted
residual. This is independent of the number of rows or coordinates. -/
theorem weighted_rounding {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) (w : Fin m → ℝ)
    (r v : Fin n → ℝ) (δ : ℝ)
    (hw : ∀ i, 0≤w i) (hr : ∀ k, 0≤r k)
    (hA : ∀ i k, |A i k-B i k|≤δ) :
    (∑ k, r k * |(∑ i, w i*A i k)-v k|) ≤
    ∑ k, r k * (|(∑ i, w i*B i k)-v k| + δ*(∑ i, w i)) := by
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (hr k)
  have herr : |∑ i, w i*(A i k-B i k)| ≤ δ*(∑ i, w i) := by
    calc
      _ ≤ ∑ i, |w i*(A i k-B i k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, w i*δ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (hA i k) (hw i)
      _ = δ*(∑ i, w i) := by rw [← Finset.sum_mul]; ring
  calc
    _ = |(∑ i, w i*(A i k-B i k)) + ((∑ i, w i*B i k)-v k)| := by
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    _ ≤ |∑ i, w i*(A i k-B i k)| + |(∑ i, w i*B i k)-v k| := abs_add_le _ _
    _ ≤ δ*(∑ i, w i)+|(∑ i, w i*B i k)-v k| := add_le_add herr le_rfl
    _ = _ := add_comm _ _

end ElevenSquare.Simplified.LocalCommon

#print axioms ElevenSquare.Simplified.LocalCommon.rational_margin_of_integer
#print axioms ElevenSquare.Simplified.LocalCommon.weighted_rounding
