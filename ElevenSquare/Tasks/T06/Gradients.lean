import ElevenSquare.Pending.S08_GapGradient
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-! Exact, symbolic coordinate gradients for the frozen center-angle chart.
These formulas keep every corner and feature flag, including aliases whose
linear terms agree but whose nonlinear gap functions do not. -/

namespace ElevenSquare.Pending.T06
noncomputable section

def coordinateDelta (j k : Fin 33) : ℝ := if k = j then 1 else 0

def coordinateLine (j : Fin 33) (t : ℝ) : Displacement :=
  Function.update (fun _ => 0) j t

@[simp] theorem coordinateLine_apply (j k : Fin 33) (t : ℝ) :
    coordinateLine j t k = t * coordinateDelta j k := by
  by_cases h : k = j <;> simp [coordinateLine, coordinateDelta,
    Function.update_apply, h]

@[simp] theorem coordinateLine_zero (j : Fin 33) : coordinateLine j 0 = 0 := by
  ext k
  simp

theorem coordinate_injective : Function.Injective (fun p : Owner × Fin 3 =>
    coordinate p.1 p.2) := by
  intro p q h
  have hv := congrArg Fin.val h
  dsimp [coordinate] at hv
  have hp := p.2.isLt
  have hq := q.2.isLt
  have hi : p.1.val = q.1.val := by omega
  have hk : p.2.val = q.2.val := by omega
  exact Prod.ext (Fin.ext hi) (Fin.ext hk)

@[simp] theorem coordinate_eq_iff (i l : Owner) (k m : Fin 3) :
    coordinate i k = coordinate l m ↔ i = l ∧ k = m := by
  constructor
  · intro h
    have hp : (i, k) = (l, m) := coordinate_injective h
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

def centerVelocity (i : Owner) (j : Fin 33) : Point :=
  (coordinateDelta j (coordinate i 0), coordinateDelta j (coordinate i 1))

def axisVelocity (q₀ : Owner → UnitSquare) (i : Owner) (j : Fin 33) : Point :=
  (-(q₀ i).axis.2 * coordinateDelta j (coordinate i 2),
    (q₀ i).axis.1 * coordinateDelta j (coordinate i 2))

def baseCorner (q₀ : Owner → UnitSquare) (i : Owner) (v : Fin 4) : Point :=
  (q₀ i).center + ((cornerSigns v).1/2) • (q₀ i).axis +
    ((cornerSigns v).2/2) • perp (q₀ i).axis

def cornerVelocity (q₀ : Owner → UnitSquare) (i : Owner) (v : Fin 4)
    (j : Fin 33) : Point :=
  centerVelocity i j + ((cornerSigns v).1/2) • axisVelocity q₀ i j +
    ((cornerSigns v).2/2) • perp (axisVelocity q₀ i j)

def baseNormal (q₀ : Owner → UnitSquare) (f : SeparationFeature) : Point :=
  if f.perpendicular then perp (q₀ f.owner).axis else (q₀ f.owner).axis

def normalVelocity (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (j : Fin 33) : Point :=
  if f.perpendicular then perp (axisVelocity q₀ f.owner j)
  else axisVelocity q₀ f.owner j

def featureSign (f : SeparationFeature) : ℝ := if f.reverse then -1 else 1

@[simp] theorem perturbedCenter_zero (q₀ : Owner → UnitSquare) (i : Owner) :
    perturbedCenter q₀ 0 i = (q₀ i).center := by
  simp [perturbedCenter]

@[simp] theorem perturbedAxis_zero (q₀ : Owner → UnitSquare) (i : Owner) :
    perturbedAxis q₀ 0 i = (q₀ i).axis := by
  simp [perturbedAxis]

@[simp] theorem perturbedCorner_zero (q₀ : Owner → UnitSquare) (i : Owner)
    (v : Fin 4) : perturbedCorner q₀ 0 i v = baseCorner q₀ i v := by
  simp [perturbedCorner, baseCorner]

theorem center_fst_hasDerivAt (q₀ : Owner → UnitSquare) (i : Owner) (j : Fin 33) :
    HasDerivAt (fun t => (perturbedCenter q₀ (coordinateLine j t) i).1)
      (centerVelocity i j).1 0 := by
  simpa [perturbedCenter, centerVelocity] using
    ((hasDerivAt_id (0 : ℝ)).mul_const (coordinateDelta j (coordinate i 0))).const_add
      (q₀ i).center.1

theorem center_snd_hasDerivAt (q₀ : Owner → UnitSquare) (i : Owner) (j : Fin 33) :
    HasDerivAt (fun t => (perturbedCenter q₀ (coordinateLine j t) i).2)
      (centerVelocity i j).2 0 := by
  simpa [perturbedCenter, centerVelocity] using
    ((hasDerivAt_id (0 : ℝ)).mul_const (coordinateDelta j (coordinate i 1))).const_add
      (q₀ i).center.2

theorem axis_fst_hasDerivAt (q₀ : Owner → UnitSquare) (i : Owner) (j : Fin 33) :
    HasDerivAt (fun t => (perturbedAxis q₀ (coordinateLine j t) i).1)
      (axisVelocity q₀ i j).1 0 := by
  have ht := (hasDerivAt_id (0 : ℝ)).mul_const (coordinateDelta j (coordinate i 2))
  simpa [perturbedAxis, axisVelocity, mul_comm] using
    (ht.cos.mul_const (q₀ i).axis.1).fun_sub (ht.sin.mul_const (q₀ i).axis.2)

theorem axis_snd_hasDerivAt (q₀ : Owner → UnitSquare) (i : Owner) (j : Fin 33) :
    HasDerivAt (fun t => (perturbedAxis q₀ (coordinateLine j t) i).2)
      (axisVelocity q₀ i j).2 0 := by
  have ht := (hasDerivAt_id (0 : ℝ)).mul_const (coordinateDelta j (coordinate i 2))
  simpa [perturbedAxis, axisVelocity, mul_comm] using
    (ht.sin.mul_const (q₀ i).axis.1).fun_add (ht.cos.mul_const (q₀ i).axis.2)

theorem corner_fst_hasDerivAt (q₀ : Owner → UnitSquare) (i : Owner) (v : Fin 4)
    (j : Fin 33) :
    HasDerivAt (fun t => (perturbedCorner q₀ (coordinateLine j t) i v).1)
      (cornerVelocity q₀ i v j).1 0 := by
  simpa [perturbedCorner, cornerVelocity, perp] using
    ((center_fst_hasDerivAt q₀ i j).fun_add
      ((axis_fst_hasDerivAt q₀ i j).const_mul ((cornerSigns v).1/2))).fun_add
        ((axis_snd_hasDerivAt q₀ i j).fun_neg.const_mul ((cornerSigns v).2/2))

theorem corner_snd_hasDerivAt (q₀ : Owner → UnitSquare) (i : Owner) (v : Fin 4)
    (j : Fin 33) :
    HasDerivAt (fun t => (perturbedCorner q₀ (coordinateLine j t) i v).2)
      (cornerVelocity q₀ i v j).2 0 := by
  simpa [perturbedCorner, cornerVelocity, perp] using
    ((center_snd_hasDerivAt q₀ i j).fun_add
      ((axis_snd_hasDerivAt q₀ i j).const_mul ((cornerSigns v).1/2))).fun_add
        ((axis_fst_hasDerivAt q₀ i j).const_mul ((cornerSigns v).2/2))

theorem normal_fst_hasDerivAt (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (j : Fin 33) :
    HasDerivAt (fun t => (if f.perpendicular then
      perp (perturbedAxis q₀ (coordinateLine j t) f.owner)
      else perturbedAxis q₀ (coordinateLine j t) f.owner).1)
      (normalVelocity q₀ f j).1 0 := by
  cases h : f.perpendicular
  · simpa [h, normalVelocity] using axis_fst_hasDerivAt q₀ f.owner j
  · simpa [h, normalVelocity, perp] using (axis_snd_hasDerivAt q₀ f.owner j).fun_neg

theorem normal_snd_hasDerivAt (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (j : Fin 33) :
    HasDerivAt (fun t => (if f.perpendicular then
      perp (perturbedAxis q₀ (coordinateLine j t) f.owner)
      else perturbedAxis q₀ (coordinateLine j t) f.owner).2)
      (normalVelocity q₀ f j).2 0 := by
  cases h : f.perpendicular
  · simpa [h, normalVelocity] using axis_snd_hasDerivAt q₀ f.owner j
  · simpa [h, normalVelocity, perp] using axis_fst_hasDerivAt q₀ f.owner j

def pairGradientFormula (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (v : Fin 4) (j : Fin 33) : ℝ :=
  featureSign f *
    (dot (cornerVelocity q₀ f.other v j - centerVelocity f.owner j) (baseNormal q₀ f) +
      dot (baseCorner q₀ f.other v - (q₀ f.owner).center) (normalVelocity q₀ f j))

def wallGradientFormula (q₀ : Owner → UnitSquare) (i : Owner) (v w : Fin 4)
    (j : Fin 33) : ℝ :=
  let d := cornerVelocity q₀ i v j
  (![d.1, -d.1, d.2, -d.2] : Fin 4 → ℝ) w

theorem featureGap_hasDerivAt (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (v : Fin 4) (j : Fin 33) :
    HasDerivAt (fun t => featureGap q₀ f v (coordinateLine j t))
      (pairGradientFormula q₀ f v j) 0 := by
  have hx := (corner_fst_hasDerivAt q₀ f.other v j).fun_sub
    (center_fst_hasDerivAt q₀ f.owner j)
  have hy := (corner_snd_hasDerivAt q₀ f.other v j).fun_sub
    (center_snd_hasDerivAt q₀ f.owner j)
  have hn₁ := normal_fst_hasDerivAt q₀ f j
  have hn₂ := normal_snd_hasDerivAt q₀ f j
  convert (((hx.fun_mul hn₁).fun_add (hy.fun_mul hn₂)).const_mul (featureSign f)).sub_const
    ((1 : ℝ)/2) using 1
  · rfl
  · simp only [coordinateLine_zero, perturbedCenter_zero, perturbedAxis_zero,
      perturbedCorner_zero, pairGradientFormula, baseNormal, dot, Prod.fst_sub,
      Prod.snd_sub]
    ring

theorem gapGradient_pair (S : ℝ) (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (v : Fin 4) (j : Fin 33) :
    gapGradient S q₀ (.pair f v) j = pairGradientFormula q₀ f v j := by
  exact (featureGap_hasDerivAt q₀ f v j).deriv

theorem gapGradient_wall (S : ℝ) (q₀ : Owner → UnitSquare) (i : Owner)
    (v w : Fin 4) (j : Fin 33) :
    gapGradient S q₀ (.wall i v w) j = wallGradientFormula q₀ i v w j := by
  fin_cases w
  · exact (corner_fst_hasDerivAt q₀ i v j).deriv
  · exact ((corner_fst_hasDerivAt q₀ i v j).const_sub S).deriv
  · exact (corner_snd_hasDerivAt q₀ i v j).deriv
  · exact ((corner_snd_hasDerivAt q₀ i v j).const_sub S).deriv

end
end ElevenSquare.Pending.T06
