import ElevenSquare.Pending.S08_Packet
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Soundness of the rational residual checks.  The rounding error is charged
against every actual matrix entry before the signed-coordinate residual is
bounded.  The numerical certificate alone does not discharge that hypothesis. -/

namespace ElevenSquare.Tasks.T06

open ElevenSquare ElevenSquare.Pending

noncomputable section

def dualSignQ (s : Fin 2) : ℚ := ![-1, 1] s

theorem cast_dualSignQ (s : Fin 2) : (dualSignQ s : ℝ) = dualSign s := by
  fin_cases s <;> simp [dualSignQ, dualSign]

/-- A per-entry perturbation bound for a nonnegative weighted matrix row sum. -/
theorem weighted_residual_error_bound
    (A B D : Fin 42 → Fin 33 → ℝ) (w : Fin 42 → ℝ)
    (v : Fin 33 → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hA : ∀ i k, |A i k - B i k| ≤ D i k) :
    (∑ k, |(∑ i, w i * A i k) - v k|) ≤
      ∑ k, (|(∑ i, w i * B i k) - v k| + ∑ i, w i * D i k) := by
  apply Finset.sum_le_sum
  intro k _
  have herr : |∑ i, w i * (A i k - B i k)| ≤ ∑ i, w i * D i k := by
    calc
      |∑ i, w i * (A i k - B i k)| ≤
          ∑ i, |w i * (A i k - B i k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, w i * D i k := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (hA i k) (hw i)
  calc
    |(∑ i, w i * A i k) - v k| =
        |(∑ i, w i * (A i k - B i k)) + ((∑ i, w i * B i k) - v k)| := by
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    _ ≤ |∑ i, w i * (A i k - B i k)| + |(∑ i, w i * B i k) - v k| :=
      abs_add_le _ _
    _ ≤ (∑ i, w i * D i k) + |(∑ i, w i * B i k) - v k| :=
      add_le_add herr le_rfl
    _ = |(∑ i, w i * B i k) - v k| + ∑ i, w i * D i k := add_comm _ _

/-- Exact rational arithmetic plus proved entry enclosures implies the real
residual estimate.  Entry errors may be different at every position. -/
theorem residual_le_of_rational_entry_bounds
    (A : Fin 42 → Fin 33 → ℝ) (B D : Fin 42 → Fin 33 → ℚ)
    (w : Fin 42 → ℚ) (v : Fin 33 → ℚ) (ε : ℚ)
    (hw : ∀ i, 0 ≤ w i)
    (hA : ∀ i k, |A i k - (B i k : ℝ)| ≤ (D i k : ℝ))
    (hcheck : (∑ k, (|(∑ i, w i * B i k) - v k| + ∑ i, w i * D i k)) ≤ ε) :
    (∑ k, |(∑ i, (w i : ℝ) * A i k) - (v k : ℝ)|) ≤ (ε : ℝ) := by
  have hw' : ∀ i, 0 ≤ (w i : ℝ) := by
    intro i
    exact_mod_cast hw i
  have hcheck' :
      (∑ k, (|(∑ i, (w i : ℝ) * (B i k : ℝ)) - (v k : ℝ)| +
        ∑ i, (w i : ℝ) * (D i k : ℝ))) ≤ (ε : ℝ) := by
    exact_mod_cast hcheck
  exact (weighted_residual_error_bound A (fun i k => (B i k : ℝ))
    (fun i k => (D i k : ℝ)) (fun i => (w i : ℝ))
    (fun k => (v k : ℝ)) hw' hA).trans hcheck'

/-- The uniform error form used by the 33-coordinate certificate shards. -/
theorem residual_le_of_rational_uniform_bound
    (A : Fin 42 → Fin 33 → ℝ) (B : Fin 42 → Fin 33 → ℚ)
    (w : Fin 42 → ℚ) (v : Fin 33 → ℚ) (δ ε : ℚ)
    (hw : ∀ i, 0 ≤ w i)
    (hA : ∀ i k, |A i k - (B i k : ℝ)| ≤ (δ : ℝ))
    (hcheck : (∑ k, |(∑ i, w i * B i k) - v k|) +
      33 * δ * (∑ i, w i) ≤ ε) :
    (∑ k, |(∑ i, (w i : ℝ) * A i k) - (v k : ℝ)|) ≤ (ε : ℝ) := by
  apply residual_le_of_rational_entry_bounds A B (fun _ _ => δ) w v ε hw hA
  calc
    (∑ k, (|(∑ i, w i * B i k) - v k| + ∑ i, w i * δ)) =
        (∑ k, |(∑ i, w i * B i k) - v k|) + 33 * δ * (∑ i, w i) := by
      rw [Finset.sum_add_distrib]
      simp only [← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ ε := hcheck

/-- The residual clause in `DualBounds`, with the frozen sign convention. -/
theorem dual_residual_le_of_rational_uniform_bound
    (A : Fin 42 → Fin 33 → ℝ) (B : Fin 42 → Fin 33 → ℚ)
    (w : Fin 42 → ℚ) (j : Fin 33) (s : Fin 2) (δ ε : ℚ)
    (hw : ∀ i, 0 ≤ w i)
    (hA : ∀ i k, |A i k - (B i k : ℝ)| ≤ (δ : ℝ))
    (hcheck : (∑ k, |(∑ i, w i * B i k) - (if k = j then dualSignQ s else 0)|) +
      33 * δ * (∑ i, w i) ≤ ε) :
    (∑ k, |(∑ i, (w i : ℝ) * A i k) -
      (if k = j then dualSign s else 0)|) ≤ (ε : ℝ) := by
  simpa only [apply_ite, Rat.cast_zero, cast_dualSignQ] using
    residual_le_of_rational_uniform_bound A B w
      (fun k => if k = j then dualSignQ s else 0) δ ε hw hA hcheck

/-- The other arithmetic clause in `DualBounds` is preserved by the rational
embedding.  This lemma is separate from the matrix residual verification. -/
theorem dual_mass_lt_of_rational
    (w c : Fin 42 → ℚ) (r ε R : ℚ)
    (hcheck : (∑ i, w i * c i) < 2 * (r - ε * R)) :
    (∑ i, (w i : ℝ) * (c i : ℝ)) <
      2 * ((r : ℝ) - (ε : ℝ) * (R : ℝ)) := by
  exact_mod_cast hcheck

/-- Integer numerator checks can certify the rational uniform-error predicate
without evaluating intermediate rational products in the finite checker. -/
theorem rational_residual_check_of_integer_check
    (n : Fin 42 → ℤ) (M : Fin 42 → Fin 33 → ℤ) (v : Fin 33 → ℤ)
    (d E : ℤ) (hd : 0 < d)
    (hcheck : (∑ k, |(∑ i, n i * M i k) - d ^ 2 * v k|) +
      33 * (∑ i, n i) ≤ E) :
    (∑ k, |(∑ i, ((n i : ℚ) / (d : ℚ)) * ((M i k : ℚ) / (d : ℚ))) -
      (v k : ℚ)|) + 33 * (1 / (d : ℚ)) * (∑ i, (n i : ℚ) / (d : ℚ)) ≤
      (E : ℚ) / (d : ℚ) ^ 2 := by
  have hd' : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hd0 : (d : ℚ) ≠ 0 := ne_of_gt hd'
  have hd2 : (0 : ℚ) < (d : ℚ) ^ 2 := sq_pos_of_pos hd'
  have hcheck' : (∑ k, |(∑ i, (n i : ℚ) * (M i k : ℚ)) -
      (d : ℚ) ^ 2 * (v k : ℚ)|) + 33 * (∑ i, (n i : ℚ)) ≤ (E : ℚ) := by
    exact_mod_cast hcheck
  have hcoord (k : Fin 33) :
      (∑ i, ((n i : ℚ) / (d : ℚ)) * ((M i k : ℚ) / (d : ℚ))) - (v k : ℚ) =
      ((∑ i, (n i : ℚ) * (M i k : ℚ)) - (d : ℚ) ^ 2 * (v k : ℚ)) /
        (d : ℚ) ^ 2 := by
    simp only [div_mul_div_comm]
    rw [← Finset.sum_div]
    field_simp [hd0] <;> ring
  have herror :
      33 * (1 / (d : ℚ)) * (∑ i, (n i : ℚ) / (d : ℚ)) =
      (33 * ∑ i, (n i : ℚ)) / (d : ℚ) ^ 2 := by
    rw [← Finset.sum_div]
    field_simp [hd0] <;> ring <;> simp
  calc
    _ = ((∑ k, |(∑ i, (n i : ℚ) * (M i k : ℚ)) -
        (d : ℚ) ^ 2 * (v k : ℚ)|) + 33 * (∑ i, (n i : ℚ))) / (d : ℚ) ^ 2 := by
      simp_rw [hcoord, abs_div, abs_of_pos hd2]
      rw [← Finset.sum_div, herror, ← add_div]
    _ ≤ (E : ℚ) / (d : ℚ) ^ 2 :=
      div_le_div_of_nonneg_right hcheck' (le_of_lt hd2)

/-- Assembly of the frozen packet contract from rational scalar checks and
entry enclosures for the actual algebraic gradients. -/
theorem dualBounds_of_rational_checks
    (S : ℝ) (q₀ : Owner → UnitSquare) (p : LocalPacket)
    (r : Fin 33 → ℚ) (m δ : ℚ) (B : Fin 128 → Fin 42 → Fin 33 → ℚ)
    (hr : ∀ j, p.radii j = (r j : ℝ)) (hm : p.maxRadius = (m : ℝ))
    (hradius : ∀ j, 0 < r j ∧ r j ≤ m ∧ r j ≤ 1 / 64)
    (hmax : 0 ≤ m)
    (hcurvature : ∀ b i, 0 ≤ p.curvature b i)
    (hweight : ∀ b j s i, 0 ≤ p.dual b j s i)
    (hresidual : ∀ b j s, 0 ≤ p.residual b j s)
    (hA : ∀ b i k,
      |gapGradient S q₀ (p.representative b i) k - (B b i k : ℝ)| ≤ (δ : ℝ))
    (hcheck : ∀ b j s,
      (∑ k, |(∑ i, p.dual b j s i * B b i k) -
        (if k = j then dualSignQ s else 0)|) +
        33 * δ * (∑ i, p.dual b j s i) ≤ p.residual b j s)
    (hmass : ∀ b j s, (∑ i, p.dual b j s i * p.curvature b i) <
      2 * (r j - p.residual b j s * m)) :
    DualBounds S q₀ p := by
  refine ⟨?_, ?_, hcurvature, hweight, hresidual, ?_, ?_⟩
  · intro j
    rw [hr j, hm]
    refine ⟨?_, ?_, ?_⟩
    · exact_mod_cast (hradius j).1
    · exact_mod_cast (hradius j).2.1
    · have h : (r j : ℝ) ≤ ((1 / 64 : ℚ) : ℝ) := by
        exact_mod_cast (hradius j).2.2
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  · rw [hm]
    exact_mod_cast hmax
  · intro b j s
    exact dual_residual_le_of_rational_uniform_bound
      (fun i k => gapGradient S q₀ (p.representative b i) k)
      (B b) (p.dual b j s) j s δ (p.residual b j s)
      (hweight b j s) (hA b) (hcheck b j s)
  · intro b j s
    rw [hr j, hm]
    exact dual_mass_lt_of_rational (p.dual b j s) (p.curvature b)
      (r j) (p.residual b j s) m (hmass b j s)

end
end ElevenSquare.Tasks.T06
