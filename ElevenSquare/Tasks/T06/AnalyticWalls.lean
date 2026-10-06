import ElevenSquare.Tasks.T06.Analytic
import Mathlib.Tactic.FinCases

namespace ElevenSquare.Pending.T06
noncomputable section

def cornerOffset (q₀ : Owner → UnitSquare) (i : Owner) (v : Fin 4) : Point :=
  ((cornerSigns v).1/2) • (q₀ i).axis +
    ((cornerSigns v).2/2) • perp (q₀ i).axis

def wallConstant (S : ℝ) (q₀ : Owner → UnitSquare) (i : Owner) : Fin 4 → ℝ :=
  ![(q₀ i).center.1, S-(q₀ i).center.1, (q₀ i).center.2, S-(q₀ i).center.2]

def wallVelocity (h : Displacement) (i : Owner) : Fin 4 → ℝ :=
  ![h (coordinate i 0), -h (coordinate i 0),
    h (coordinate i 1), -h (coordinate i 1)]

def wallCosCoefficient (q₀ : Owner → UnitSquare) (i : Owner) (v : Fin 4) :
    Fin 4 → ℝ :=
  ![(cornerOffset q₀ i v).1, -(cornerOffset q₀ i v).1,
    (cornerOffset q₀ i v).2, -(cornerOffset q₀ i v).2]

def wallSinCoefficient (q₀ : Owner → UnitSquare) (i : Owner) (v : Fin 4) :
    Fin 4 → ℝ :=
  ![-(cornerOffset q₀ i v).2, (cornerOffset q₀ i v).2,
    (cornerOffset q₀ i v).1, -(cornerOffset q₀ i v).1]

theorem perturbedCorner_radial_x (q₀ : Owner → UnitSquare) (h : Displacement)
    (i : Owner) (v : Fin 4) (t : ℝ) :
    (perturbedCorner q₀ (t • h) i v).1 =
      (q₀ i).center.1 + t*h (coordinate i 0) +
      (cornerOffset q₀ i v).1 * Real.cos (h (coordinate i 2)*t) -
      (cornerOffset q₀ i v).2 * Real.sin (h (coordinate i 2)*t) := by
  simp only [perturbedCorner, perturbedCenter, perturbedAxis, cornerOffset, perp,
    Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.smul_apply,
    smul_eq_mul, mul_comm t (h (coordinate i 2))]
  ring

theorem perturbedCorner_radial_y (q₀ : Owner → UnitSquare) (h : Displacement)
    (i : Owner) (v : Fin 4) (t : ℝ) :
    (perturbedCorner q₀ (t • h) i v).2 =
      (q₀ i).center.2 + t*h (coordinate i 1) +
      (cornerOffset q₀ i v).2 * Real.cos (h (coordinate i 2)*t) +
      (cornerOffset q₀ i v).1 * Real.sin (h (coordinate i 2)*t) := by
  simp only [perturbedCorner, perturbedCenter, perturbedAxis, cornerOffset, perp,
    Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.smul_apply,
    smul_eq_mul, mul_comm t (h (coordinate i 2))]
  ring

theorem wall_gap_radial (S : ℝ) (q₀ : Owner → UnitSquare) (h : Displacement)
    (i : Owner) (v w : Fin 4) (t : ℝ) :
    gapValue S q₀ (.wall i v w) (t • h) =
      wallConstant S q₀ i w + wallVelocity h i w*t +
        trigAffine (wallCosCoefficient q₀ i v w) 0
          (wallSinCoefficient q₀ i v w) 0 (h (coordinate i 2)) t := by
  fin_cases w <;>
    simp [gapValue, wallConstant, wallVelocity, wallCosCoefficient,
      wallSinCoefficient, trigAffine, perturbedCorner_radial_x,
      perturbedCorner_radial_y] <;> ring

theorem wall_gap_radial_hasDerivAt (S : ℝ) (q₀ : Owner → UnitSquare)
    (h : Displacement) (i : Owner) (v w : Fin 4) (t : ℝ) :
    HasDerivAt (fun t : ℝ => gapValue S q₀ (.wall i v w) (t • h))
      (wallVelocity h i w +
        trigAffineDerivative (wallCosCoefficient q₀ i v w) 0
          (wallSinCoefficient q₀ i v w) 0 (h (coordinate i 2)) t) t := by
  have ha := ((hasDerivAt_id t).const_mul (wallVelocity h i w)).const_add
    (wallConstant S q₀ i w)
  have hb := trigAffine_hasDerivAt (wallCosCoefficient q₀ i v w) 0
    (wallSinCoefficient q₀ i v w) 0 (h (coordinate i 2)) t
  convert ha.fun_add hb using 1 <;> try simp only [mul_one]
  funext z
  exact wall_gap_radial S q₀ h i v w z

theorem wall_gap_radial_taylor (S : ℝ) (q₀ : Owner → UnitSquare)
    (h : Displacement) (i : Owner) (v w : Fin 4) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    |gapValue S q₀ (.wall i v w) (τ • h) - gapValue S q₀ (.wall i v w) 0 -
      τ*(wallVelocity h i w +
        h (coordinate i 2)*wallSinCoefficient q₀ i v w)| ≤
      τ^2*trigAffineCurvature (wallCosCoefficient q₀ i v w) 0
        (wallSinCoefficient q₀ i v w) 0 (h (coordinate i 2))/2 := by
  have hb := trigAffine_radial_taylor (wallCosCoefficient q₀ i v w) 0
    (wallSinCoefficient q₀ i v w) 0 (h (coordinate i 2)) τ hτ
  have hzero := wall_gap_radial S q₀ h i v w 0
  simp only [zero_smul] at hzero
  rw [wall_gap_radial, hzero]
  simp only [trigAffine, mul_zero, add_zero, Real.cos_zero, Real.sin_zero,
    mul_one] at hb ⊢
  convert hb using 1 <;> congr 1 <;> ring

def basisDisplacement (j : Fin 33) : Displacement :=
  fun k => if k = j then 1 else 0

theorem smul_basisDisplacement (j : Fin 33) (t : ℝ) :
    t • basisDisplacement j = Function.update (fun _ => 0) j t := by
  funext k
  by_cases hk : k = j
  · subst k
    simp [basisDisplacement, Function.update_apply]
  · simp [basisDisplacement, Function.update_apply, hk]

theorem wall_gapGradient (S : ℝ) (q₀ : Owner → UnitSquare)
    (i : Owner) (v w : Fin 4) (j : Fin 33) :
    gapGradient S q₀ (.wall i v w) j =
      wallVelocity (basisDisplacement j) i w +
        basisDisplacement j (coordinate i 2)*wallSinCoefficient q₀ i v w := by
  have hd := wall_gap_radial_hasDerivAt S q₀ (basisDisplacement j) i v w 0
  have he : (fun t : ℝ => gapValue S q₀ (.wall i v w) (t • basisDisplacement j)) =
      (fun t : ℝ => gapValue S q₀ (.wall i v w) (Function.update (fun _ => 0) j t)) := by
    funext t
    rw [smul_basisDisplacement]
  rw [he] at hd
  simpa [gapGradient, trigAffineDerivative, trigAffine] using hd.deriv

theorem wall_gradient_linearForm (S : ℝ) (q₀ : Owner → UnitSquare)
    (h : Displacement) (i : Owner) (v w : Fin 4) :
    LinearForm (gapGradient S q₀ (.wall i v w)) h =
      wallVelocity h i w +
        h (coordinate i 2)*wallSinCoefficient q₀ i v w := by
  unfold LinearForm
  simp_rw [wall_gapGradient, add_mul]
  rw [Finset.sum_add_distrib]
  have hv : (∑ j : Fin 33, wallVelocity (basisDisplacement j) i w*h j) =
      wallVelocity h i w := by
    fin_cases w <;> simp [wallVelocity, basisDisplacement, ite_mul]
  rw [hv]
  congr 1
  simp [basisDisplacement, ite_mul, mul_comm]

theorem wall_gap_taylor_with_gradient (S : ℝ) (q₀ : Owner → UnitSquare)
    (h : Displacement) (i : Owner) (v w : Fin 4) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    |gapValue S q₀ (.wall i v w) (τ • h) - gapValue S q₀ (.wall i v w) 0 -
      τ*LinearForm (gapGradient S q₀ (.wall i v w)) h| ≤
      τ^2*trigAffineCurvature (wallCosCoefficient q₀ i v w) 0
        (wallSinCoefficient q₀ i v w) 0 (h (coordinate i 2))/2 := by
  rw [wall_gradient_linearForm]
  exact wall_gap_radial_taylor S q₀ h i v w τ hτ

theorem trigAffineCurvature_pure (a c w : ℝ) :
    trigAffineCurvature a 0 c 0 w = (|a| + |c|)*w^2 := by
  simp [trigAffineCurvature, abs_mul, abs_of_nonneg (sq_nonneg w)]
  ring

theorem wall_coefficient_abs_sum (q₀ : Owner → UnitSquare) (i : Owner)
    (v w : Fin 4) :
    |wallCosCoefficient q₀ i v w| + |wallSinCoefficient q₀ i v w| =
      |(cornerOffset q₀ i v).1| + |(cornerOffset q₀ i v).2| := by
  fin_cases w <;> simp [wallCosCoefficient, wallSinCoefficient, add_comm]

def wallRectangleCurvature (q₀ : Owner → UnitSquare) (r : Fin 33 → ℝ)
    (i : Owner) (v : Fin 4) : ℝ :=
  (|(cornerOffset q₀ i v).1| + |(cornerOffset q₀ i v).2|) * (r (coordinate i 2))^2

theorem wall_gap_taylor_on_rectangle (S : ℝ) (q₀ : Owner → UnitSquare)
    (r : Fin 33 → ℝ) (h : Displacement) (hr : InRectangle r h)
    (i : Owner) (v w : Fin 4) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    |gapValue S q₀ (.wall i v w) (τ • h) - gapValue S q₀ (.wall i v w) 0 -
      τ*LinearForm (gapGradient S q₀ (.wall i v w)) h| ≤
      τ^2*wallRectangleCurvature q₀ r i v/2 := by
  have hh := hr (coordinate i 2)
  have hr0 : 0 ≤ r (coordinate i 2) := (abs_nonneg _).trans hh
  have hs := mul_nonneg (sub_nonneg.mpr hh)
    (add_nonneg hr0 (abs_nonneg (h (coordinate i 2))))
  have hsq : (h (coordinate i 2))^2 ≤ (r (coordinate i 2))^2 := by
    nlinarith [sq_abs (h (coordinate i 2))]
  have hK : trigAffineCurvature (wallCosCoefficient q₀ i v w) 0
      (wallSinCoefficient q₀ i v w) 0 (h (coordinate i 2)) ≤
      wallRectangleCurvature q₀ r i v := by
    rw [trigAffineCurvature_pure, wall_coefficient_abs_sum]
    exact mul_le_mul_of_nonneg_left hsq (add_nonneg (abs_nonneg _) (abs_nonneg _))
  exact (wall_gap_taylor_with_gradient S q₀ h i v w τ hτ).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hK (sq_nonneg τ)) (by norm_num))

end
end ElevenSquare.Pending.T06
