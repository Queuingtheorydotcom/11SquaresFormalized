import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
A dimension-independent replacement for the analytic core of the local packet.
It requires only one-sided quadratic row bounds and measures dual residuals in
the exact dual norm of the coordinate rectangle. No packing-specific facts or
certificate data are assumed by this module.
-/

namespace ElevenSquare.Simplified.LocalCommon

noncomputable section
open scoped BigOperators

def dot {n : ℕ} (a h : Fin n → ℝ) : ℝ := ∑ k, a k * h k

def sign (s : Fin 2) : ℝ := if s = 0 then -1 else 1

/-- The old unweighted residual check implies the sharper rectangle check.
Thus existing certificates can use the new interface without recomputation. -/
theorem weighted_residual_le_uniform {n : ℕ} (r e : Fin n → ℝ) (R ε : ℝ)
    (hr : ∀ k, r k ≤ R) (hR : 0 ≤ R) (he : (∑ k, |e k|) ≤ ε) :
    (∑ k, r k * |e k|) ≤ R * ε := by
  calc
    _ ≤ ∑ k, R * |e k| := Finset.sum_le_sum
      (fun k _ => mul_le_mul_of_nonneg_right (hr k) (abs_nonneg _))
    _ = R * (∑ k, |e k|) := (Finset.mul_sum ..).symm
    _ ≤ R * ε := mul_le_mul_of_nonneg_left he hR

/-- A nonnegative combination of necessary rows bounds a signed coordinate.
The residual is weighted by the actual coordinate radii, with no enclosing
uniform radius and no separate nonnegativity assumption on the error bound. -/
theorem weighted_dual_bound {n m : ℕ}
    (A : Fin m → Fin n → ℝ) (w K : Fin m → ℝ)
    (r h : Fin n → ℝ) (j : Fin n) (σ E τ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hτ : 0 ≤ τ)
    (hbox : ∀ k, |h k| ≤ τ * r k)
    (hrows : ∀ i, -(τ ^ 2 * K i / 2) ≤ dot (A i) h)
    (hres : (∑ k, r k * |(∑ i, w i * A i k) -
      (if k = j then σ else 0)|) ≤ E) :
    -(σ * h j) ≤ τ * E + τ ^ 2 * (∑ i, w i * K i) / 2 := by
  let B : Fin n → ℝ := fun k => ∑ i, w i * A i k
  let e : Fin n → ℝ := fun k => B k - (if k = j then σ else 0)
  have weighted : (∑ i, w i * dot (A i) h) = dot B h := by
    simp only [dot, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [B]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have lower : -(τ ^ 2 * (∑ i, w i * K i) / 2) ≤ dot B h := by
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_left (hrows i) (hw i))
    have heq : (∑ i, w i * (-(τ ^ 2 * K i / 2))) =
        -(τ ^ 2 * (∑ i, w i * K i) / 2) := by
      calc
        _ = ∑ i, (-τ ^ 2 / 2) * (w i * K i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (-τ ^ 2 / 2) * (∑ i, w i * K i) := (Finset.mul_sum ..).symm
        _ = _ := by ring
    rw [heq, weighted] at hs
    exact hs
  have error : dot e h ≤ τ * E := by
    calc
      _ ≤ ∑ k, τ * (r k * |e k|) := by
        apply Finset.sum_le_sum
        intro k hk
        calc
          e k * h k ≤ |e k * h k| := le_abs_self _
          _ = |e k| * |h k| := abs_mul _ _
          _ ≤ |e k| * (τ * r k) :=
            mul_le_mul_of_nonneg_left (hbox k) (abs_nonneg _)
          _ = τ * (r k * |e k|) := by ring
      _ = τ * (∑ k, r k * |e k|) := (Finset.mul_sum ..).symm
      _ ≤ τ * E := mul_le_mul_of_nonneg_left hres hτ
  have identity : dot e h = dot B h - σ * h j := by
    simp [dot, e, sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [identity] at error
  linarith

/-- Finite branch systems are isolated whenever their nonnegative duals
dominate their one-sided quadratic errors in the rectangle norm.

`hrows` is the complete interface to geometry and calculus: a feasible point
must select some branch, and its rows have the stated quadratic lower bounds.
In a Taylor application only the upper error `g(h) ≤ A*h + τ²*K/2` is needed.
The branch may depend on the point. Closed rectangle boundaries are included.
-/
theorem branchwise_isolation {n m branches : ℕ}
    (feasible : (Fin (n + 1) → ℝ) → Prop)
    (r : Fin (n + 1) → ℝ)
    (A : Fin branches → Fin m → Fin (n + 1) → ℝ)
    (K : Fin branches → Fin m → ℝ)
    (w : Fin branches → Fin (n + 1) → Fin 2 → Fin m → ℝ)
    (E : Fin branches → Fin (n + 1) → Fin 2 → ℝ)
    (hr : ∀ k, 0 < r k) (hK : ∀ b i, 0 ≤ K b i)
    (hw : ∀ b j s i, 0 ≤ w b j s i)
    (hres : ∀ b j s, (∑ k, r k * |(∑ i, w b j s i * A b i k) -
      (if k = j then sign s else 0)|) ≤ E b j s)
    (hmargin : ∀ b j s, E b j s + (∑ i, w b j s i * K b i) / 2 < r j)
    (hrows : ∀ h, feasible h → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      (∀ k, |h k| ≤ τ * r k) →
      ∃ b, ∀ i, -(τ ^ 2 * K b i / 2) ≤ dot (A b i) h) :
    ∀ h, (∀ k, |h k| ≤ r k) → feasible h → h = 0 := by
  intro h hrect hfeasible
  by_contra hn
  obtain ⟨j, hj⟩ := Finite.exists_max (fun k : Fin (n + 1) => |h k| / r k)
  let τ := |h j| / r j
  have hτle : τ ≤ 1 := (div_le_one (hr j)).mpr (hrect j)
  have hτpos : 0 < τ := by
    by_contra hnot
    apply hn
    funext k
    have hk : |h k| / r k ≤ 0 := (hj k).trans (le_of_not_gt hnot)
    have hk' : |h k| ≤ 0 := by
      simpa using (div_le_iff₀ (hr k)).mp hk
    exact abs_eq_zero.mp (le_antisymm hk' (abs_nonneg _))
  have hbox : ∀ k, |h k| ≤ τ * r k :=
    fun k => (div_le_iff₀ (hr k)).mp (hj k)
  have hsat : |h j| = τ * r j :=
    (div_mul_cancel₀ (|h j|) (ne_of_gt (hr j))).symm
  obtain ⟨b, hb⟩ := hrows h hfeasible τ hτpos hτle hbox
  have hsign : ∃ s : Fin 2, -(sign s * h j) = |h j| := by
    by_cases hjpos : 0 ≤ h j
    · exact ⟨0, by simp [sign, abs_of_nonneg hjpos]⟩
    · exact ⟨1, by simp [sign, abs_of_neg (lt_of_not_ge hjpos)]⟩
  obtain ⟨s, hs⟩ := hsign
  have hbound := weighted_dual_bound (A b) (w b j s) (K b)
    r h j (sign s) (E b j s) τ (hw b j s) hτpos.le hbox hb (hres b j s)
  rw [hs, hsat] at hbound
  let M : ℝ := ∑ i, w b j s i * K b i
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => mul_nonneg (hw b j s i) (hK b i))
  have hquad : τ ^ 2 * M ≤ τ * M := by
    nlinarith [mul_nonneg (mul_nonneg hτpos.le (sub_nonneg.mpr hτle)) hM]
  have hstrict := mul_lt_mul_of_pos_left (hmargin b j s) hτpos
  change τ * r j ≤ τ * E b j s + τ ^ 2 * M / 2 at hbound
  change τ * (E b j s + M / 2) < τ * r j at hstrict
  nlinarith

end
end ElevenSquare.Simplified.LocalCommon

#print axioms ElevenSquare.Simplified.LocalCommon.weighted_residual_le_uniform
#print axioms ElevenSquare.Simplified.LocalCommon.weighted_dual_bound
#print axioms ElevenSquare.Simplified.LocalCommon.branchwise_isolation
