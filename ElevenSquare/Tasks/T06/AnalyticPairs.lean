import ElevenSquare.Tasks.T06.AnalyticWalls

namespace ElevenSquare.Pending.T06
noncomputable section

def rotatePoint (θ : ℝ) (p : Point) : Point :=
  (Real.cos θ*p.1-Real.sin θ*p.2, Real.sin θ*p.1+Real.cos θ*p.2)

def radialCenterVelocity (h : Displacement) (i : Owner) : Point :=
  (h (coordinate i 0), h (coordinate i 1))

def featureNormal (q₀ : Owner → UnitSquare) (f : SeparationFeature) : Point :=
  if f.perpendicular then perp (q₀ f.owner).axis else (q₀ f.owner).axis

def radialFeatureSign (f : SeparationFeature) : ℝ := if f.reverse then -1 else 1

def featureCenterDifference (q₀ : Owner → UnitSquare) (f : SeparationFeature) : Point :=
  (q₀ f.other).center - (q₀ f.owner).center

def featureCenterVelocity (h : Displacement) (f : SeparationFeature) : Point :=
  radialCenterVelocity h f.other - radialCenterVelocity h f.owner

def featureFirstProfile (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (h : Displacement) (t : ℝ) : ℝ :=
  trigAffine (dot (featureCenterDifference q₀ f) (featureNormal q₀ f))
    (dot (featureCenterVelocity h f) (featureNormal q₀ f))
    (dot (featureCenterDifference q₀ f) (perp (featureNormal q₀ f)))
    (dot (featureCenterVelocity h f) (perp (featureNormal q₀ f)))
    (h (coordinate f.owner 2)) t

def featureSecondProfile (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (v : Fin 4) (h : Displacement) (t : ℝ) : ℝ :=
  trigAffine (dot (cornerOffset q₀ f.other v) (featureNormal q₀ f)) 0
    (dot (perp (cornerOffset q₀ f.other v)) (featureNormal q₀ f)) 0
    (h (coordinate f.other 2)-h (coordinate f.owner 2)) t

theorem dot_add_left (p q n : Point) : dot (p+q) n = dot p n + dot q n := by
  dsimp [dot]
  ring

theorem perp_rotatePoint (θ : ℝ) (p : Point) :
    perp (rotatePoint θ p) = rotatePoint θ (perp p) := by
  ext <;> dsimp [perp, rotatePoint] <;> ring

theorem dot_affine_rotatePoint (D H n : Point) (w t : ℝ) :
    dot (D+t • H) (rotatePoint (w*t) n) =
      trigAffine (dot D n) (dot H n) (dot D (perp n)) (dot H (perp n)) w t := by
  dsimp [dot, rotatePoint, trigAffine, perp]
  ring

theorem dot_rotatePoint_rotatePoint (p n : Point) (a b : ℝ) :
    dot (rotatePoint b p) (rotatePoint a n) =
      dot p n*Real.cos (b-a) + dot (perp p) n*Real.sin (b-a) := by
  rw [Real.cos_sub, Real.sin_sub]
  dsimp [dot, rotatePoint, perp]
  ring

theorem perturbedAxis_radial_rotatePoint (q₀ : Owner → UnitSquare)
    (h : Displacement) (i : Owner) (t : ℝ) :
    perturbedAxis q₀ (t • h) i = rotatePoint (h (coordinate i 2)*t) (q₀ i).axis := by
  simp [perturbedAxis, rotatePoint, mul_comm t (h (coordinate i 2))]

theorem perturbedCorner_radial_rotatePoint (q₀ : Owner → UnitSquare)
    (h : Displacement) (i : Owner) (v : Fin 4) (t : ℝ) :
    perturbedCorner q₀ (t • h) i v =
      (q₀ i).center + t • radialCenterVelocity h i +
        rotatePoint (h (coordinate i 2)*t) (cornerOffset q₀ i v) := by
  apply Prod.ext
  · simpa [rotatePoint, radialCenterVelocity, sub_eq_add_neg, add_assoc,
      add_comm, add_left_comm, mul_comm] using
      perturbedCorner_radial_x q₀ h i v t
  · simpa [rotatePoint, radialCenterVelocity, add_assoc, add_comm, add_left_comm,
      mul_comm] using
      perturbedCorner_radial_y q₀ h i v t

theorem perturbed_featureNormal_radial (q₀ : Owner → UnitSquare)
    (f : SeparationFeature) (h : Displacement) (t : ℝ) :
    (if f.perpendicular then perp (perturbedAxis q₀ (t • h) f.owner)
      else perturbedAxis q₀ (t • h) f.owner) =
      rotatePoint (h (coordinate f.owner 2)*t) (featureNormal q₀ f) := by
  rw [perturbedAxis_radial_rotatePoint]
  cases hp : f.perpendicular <;> simp [featureNormal, hp, perp_rotatePoint]

theorem feature_gap_radial (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (v : Fin 4) (h : Displacement) (t : ℝ) :
    featureGap q₀ f v (t • h) =
      radialFeatureSign f*(featureFirstProfile q₀ f h t + featureSecondProfile q₀ f v h t)-1/2 := by
  dsimp only [featureGap]
  rw [perturbed_featureNormal_radial, perturbedCorner_radial_rotatePoint]
  have hp : (q₀ f.other).center + t • radialCenterVelocity h f.other +
      rotatePoint (h (coordinate f.other 2)*t) (cornerOffset q₀ f.other v) -
        perturbedCenter q₀ (t • h) f.owner =
      (featureCenterDifference q₀ f + t • featureCenterVelocity h f) +
        rotatePoint (h (coordinate f.other 2)*t) (cornerOffset q₀ f.other v) := by
    ext <;> dsimp [perturbedCenter, radialCenterVelocity, featureCenterDifference,
      featureCenterVelocity] <;> ring
  rw [hp, dot_add_left, dot_affine_rotatePoint, dot_rotatePoint_rotatePoint]
  dsimp [featureFirstProfile, featureSecondProfile, radialFeatureSign, trigAffine]
  rw [show h (coordinate f.other 2)*t-h (coordinate f.owner 2)*t =
    (h (coordinate f.other 2)-h (coordinate f.owner 2))*t by ring]
  ring

def featureRadialLinear (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (v : Fin 4) (h : Displacement) : ℝ :=
  radialFeatureSign f *
    (dot (featureCenterVelocity h f) (featureNormal q₀ f) +
      h (coordinate f.owner 2)*dot (featureCenterDifference q₀ f) (perp (featureNormal q₀ f)) +
      (h (coordinate f.other 2)-h (coordinate f.owner 2))*
        dot (perp (cornerOffset q₀ f.other v)) (featureNormal q₀ f))

def featureRadialCurvature (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (v : Fin 4) (h : Displacement) : ℝ :=
  trigAffineCurvature (dot (featureCenterDifference q₀ f) (featureNormal q₀ f))
    (dot (featureCenterVelocity h f) (featureNormal q₀ f))
    (dot (featureCenterDifference q₀ f) (perp (featureNormal q₀ f)))
    (dot (featureCenterVelocity h f) (perp (featureNormal q₀ f)))
    (h (coordinate f.owner 2)) +
  trigAffineCurvature (dot (cornerOffset q₀ f.other v) (featureNormal q₀ f)) 0
    (dot (perp (cornerOffset q₀ f.other v)) (featureNormal q₀ f)) 0
    (h (coordinate f.other 2)-h (coordinate f.owner 2))

theorem abs_radialFeatureSign (f : SeparationFeature) : |radialFeatureSign f| = 1 := by
  cases hp : f.reverse <;> simp [radialFeatureSign, hp]

theorem feature_gap_radial_taylor (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (v : Fin 4) (h : Displacement) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    |featureGap q₀ f v (τ • h)-featureGap q₀ f v 0-τ*featureRadialLinear q₀ f v h| ≤
      τ^2*featureRadialCurvature q₀ f v h/2 := by
  have hf := trigAffine_radial_taylor
    (dot (featureCenterDifference q₀ f) (featureNormal q₀ f))
    (dot (featureCenterVelocity h f) (featureNormal q₀ f))
    (dot (featureCenterDifference q₀ f) (perp (featureNormal q₀ f)))
    (dot (featureCenterVelocity h f) (perp (featureNormal q₀ f)))
    (h (coordinate f.owner 2)) τ hτ
  have hg := trigAffine_radial_taylor
    (dot (cornerOffset q₀ f.other v) (featureNormal q₀ f)) 0
    (dot (perp (cornerOffset q₀ f.other v)) (featureNormal q₀ f)) 0
    (h (coordinate f.other 2)-h (coordinate f.owner 2)) τ hτ
  have hsum := add_le_add hf hg
  have htri := abs_add_le
    (featureFirstProfile q₀ f h τ - featureFirstProfile q₀ f h 0 -
      τ*(dot (featureCenterVelocity h f) (featureNormal q₀ f) +
        h (coordinate f.owner 2)*dot (featureCenterDifference q₀ f) (perp (featureNormal q₀ f))))
    (featureSecondProfile q₀ f v h τ - featureSecondProfile q₀ f v h 0 -
      τ*((h (coordinate f.other 2)-h (coordinate f.owner 2))*
        dot (perp (cornerOffset q₀ f.other v)) (featureNormal q₀ f)))
  have hzero := feature_gap_radial q₀ f v h 0
  simp only [zero_smul] at hzero
  rw [feature_gap_radial, hzero]
  have he : radialFeatureSign f*(featureFirstProfile q₀ f h τ+featureSecondProfile q₀ f v h τ)-1/2 -
      (radialFeatureSign f*(featureFirstProfile q₀ f h 0+featureSecondProfile q₀ f v h 0)-1/2) -
        τ*featureRadialLinear q₀ f v h = radialFeatureSign f *
      ((featureFirstProfile q₀ f h τ-featureFirstProfile q₀ f h 0-
        τ*(dot (featureCenterVelocity h f) (featureNormal q₀ f)+
          h (coordinate f.owner 2)*dot (featureCenterDifference q₀ f) (perp (featureNormal q₀ f))))+
       (featureSecondProfile q₀ f v h τ-featureSecondProfile q₀ f v h 0-
         τ*((h (coordinate f.other 2)-h (coordinate f.owner 2))*
           dot (perp (cornerOffset q₀ f.other v)) (featureNormal q₀ f)))) := by
    unfold featureRadialLinear
    ring
  rw [he, abs_mul, abs_radialFeatureSign, one_mul]
  apply htri.trans
  dsimp [featureFirstProfile, featureSecondProfile, featureRadialCurvature] at *
  simp only [trigAffine, mul_zero, zero_mul, add_zero, zero_add,
    Real.cos_zero, Real.sin_zero, mul_one] at *
  linarith

theorem feature_gap_radial_hasDerivAt_zero (q₀ : Owner → UnitSquare)
    (f : SeparationFeature) (v : Fin 4) (h : Displacement) :
    HasDerivAt (fun t : ℝ => featureGap q₀ f v (t • h))
      (featureRadialLinear q₀ f v h) 0 := by
  have hf := trigAffine_hasDerivAt
    (dot (featureCenterDifference q₀ f) (featureNormal q₀ f))
    (dot (featureCenterVelocity h f) (featureNormal q₀ f))
    (dot (featureCenterDifference q₀ f) (perp (featureNormal q₀ f)))
    (dot (featureCenterVelocity h f) (perp (featureNormal q₀ f)))
    (h (coordinate f.owner 2)) 0
  have hg := trigAffine_hasDerivAt
    (dot (cornerOffset q₀ f.other v) (featureNormal q₀ f)) 0
    (dot (perp (cornerOffset q₀ f.other v)) (featureNormal q₀ f)) 0
    (h (coordinate f.other 2)-h (coordinate f.owner 2)) 0
  convert ((hf.fun_add hg).const_mul (radialFeatureSign f)).sub_const (1/2) using 1
  · funext t
    exact feature_gap_radial q₀ f v h t
  · simp [trigAffineDerivative, trigAffine, featureRadialLinear] <;> ring

theorem feature_gapGradient (S : ℝ) (q₀ : Owner → UnitSquare)
    (f : SeparationFeature) (v : Fin 4) (j : Fin 33) :
    gapGradient S q₀ (.pair f v) j =
      featureRadialLinear q₀ f v (basisDisplacement j) := by
  have hd := feature_gap_radial_hasDerivAt_zero q₀ f v (basisDisplacement j)
  have he : (fun t : ℝ => featureGap q₀ f v (t • basisDisplacement j)) =
      (fun t : ℝ => featureGap q₀ f v (Function.update (fun _ => 0) j t)) := by
    funext t
    rw [smul_basisDisplacement]
  rw [he] at hd
  simpa [gapGradient, gapValue] using hd.deriv

theorem feature_gradient_linearForm (S : ℝ) (q₀ : Owner → UnitSquare)
    (f : SeparationFeature) (v : Fin 4) (h : Displacement) :
    LinearForm (gapGradient S q₀ (.pair f v)) h = featureRadialLinear q₀ f v h := by
  unfold LinearForm
  simp_rw [feature_gapGradient]
  simp [featureRadialLinear, featureCenterVelocity, radialCenterVelocity, dot, perp,
    basisDisplacement, mul_add, mul_sub, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, ite_mul]
  ring

theorem feature_gap_taylor_with_gradient (S : ℝ) (q₀ : Owner → UnitSquare)
    (f : SeparationFeature) (v : Fin 4) (h : Displacement) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    |gapValue S q₀ (.pair f v) (τ • h)-gapValue S q₀ (.pair f v) 0-
      τ*LinearForm (gapGradient S q₀ (.pair f v)) h| ≤
      τ^2*featureRadialCurvature q₀ f v h/2 := by
  rw [feature_gradient_linearForm]
  exact feature_gap_radial_taylor q₀ f v h τ hτ

theorem abs_dot_add_abs_dot_perp_le (p n : Point) :
    |dot p n| + |dot p (perp n)| ≤ (|p.1| + |p.2|)*(|n.1| + |n.2|) := by
  have h1 := abs_add_le (p.1*n.1) (p.2*n.2)
  have h2 := abs_add_le (p.1*(-n.2)) (p.2*n.1)
  simp only [abs_mul, abs_neg] at h1 h2
  dsimp [dot, perp]
  nlinarith

def featureTranslationRadius (r : Fin 33 → ℝ) (f : SeparationFeature) : ℝ :=
  r (coordinate f.other 0)+r (coordinate f.owner 0)+
    (r (coordinate f.other 1)+r (coordinate f.owner 1))

def featureVelocityBound (q₀ : Owner → UnitSquare) (r : Fin 33 → ℝ)
    (f : SeparationFeature) : ℝ :=
  (|(featureNormal q₀ f).1| + |(featureNormal q₀ f).2|)*featureTranslationRadius r f

def featureRectangleCurvature (q₀ : Owner → UnitSquare) (r : Fin 33 → ℝ)
    (f : SeparationFeature) (v : Fin 4) : ℝ :=
  (|dot (featureCenterDifference q₀ f) (featureNormal q₀ f)| +
    |dot (featureCenterDifference q₀ f) (perp (featureNormal q₀ f))| +
    featureVelocityBound q₀ r f)*(r (coordinate f.owner 2))^2 +
  2*featureVelocityBound q₀ r f*r (coordinate f.owner 2) +
  (|dot (cornerOffset q₀ f.other v) (featureNormal q₀ f)| +
    |dot (perp (cornerOffset q₀ f.other v)) (featureNormal q₀ f)|)*
      (r (coordinate f.other 2)+r (coordinate f.owner 2))^2

theorem feature_velocity_bound (q₀ : Owner → UnitSquare) (r : Fin 33 → ℝ)
    (f : SeparationFeature) (h : Displacement) (hr : InRectangle r h) :
    |dot (featureCenterVelocity h f) (featureNormal q₀ f)| +
      |dot (featureCenterVelocity h f) (perp (featureNormal q₀ f))| ≤
      featureVelocityBound q₀ r f := by
  have hx : |(featureCenterVelocity h f).1| ≤
      r (coordinate f.other 0)+r (coordinate f.owner 0) :=
    (abs_sub _ _).trans (add_le_add (hr _) (hr _))
  have hy : |(featureCenterVelocity h f).2| ≤
      r (coordinate f.other 1)+r (coordinate f.owner 1) :=
    (abs_sub _ _).trans (add_le_add (hr _) (hr _))
  have hs := mul_le_mul_of_nonneg_right (add_le_add hx hy)
    (add_nonneg (abs_nonneg (featureNormal q₀ f).1) (abs_nonneg (featureNormal q₀ f).2))
  exact (abs_dot_add_abs_dot_perp_le (featureCenterVelocity h f) (featureNormal q₀ f)).trans
    (by simpa [featureVelocityBound, featureTranslationRadius, mul_comm] using hs)

theorem feature_curvature_on_rectangle (q₀ : Owner → UnitSquare) (r : Fin 33 → ℝ)
    (f : SeparationFeature) (v : Fin 4) (h : Displacement) (hr : InRectangle r h) :
    featureRadialCurvature q₀ f v h ≤ featureRectangleCurvature q₀ r f v := by
  have hf := trigAffineCurvature_le
    (dot (featureCenterDifference q₀ f) (featureNormal q₀ f))
    (dot (featureCenterVelocity h f) (featureNormal q₀ f))
    (dot (featureCenterDifference q₀ f) (perp (featureNormal q₀ f)))
    (dot (featureCenterVelocity h f) (perp (featureNormal q₀ f)))
    (h (coordinate f.owner 2))
    (|dot (featureCenterDifference q₀ f) (featureNormal q₀ f)| +
      |dot (featureCenterDifference q₀ f) (perp (featureNormal q₀ f))|)
    (featureVelocityBound q₀ r f) (r (coordinate f.owner 2)) le_rfl
    (feature_velocity_bound q₀ r f h hr) (hr _)
  have hw : |h (coordinate f.other 2)-h (coordinate f.owner 2)| ≤
      r (coordinate f.other 2)+r (coordinate f.owner 2) :=
    (abs_sub _ _).trans (add_le_add (hr _) (hr _))
  have hs := mul_le_mul_of_nonneg_left (square_le_square_of_abs_le _ _ hw)
    (add_nonneg
      (abs_nonneg (dot (cornerOffset q₀ f.other v) (featureNormal q₀ f)))
      (abs_nonneg (dot (perp (cornerOffset q₀ f.other v)) (featureNormal q₀ f))))
  unfold featureRadialCurvature featureRectangleCurvature
  rw [trigAffineCurvature_pure]
  exact add_le_add hf hs

theorem feature_gap_taylor_on_rectangle (S : ℝ) (q₀ : Owner → UnitSquare)
    (r : Fin 33 → ℝ) (f : SeparationFeature) (v : Fin 4)
    (h : Displacement) (hr : InRectangle r h) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    |gapValue S q₀ (.pair f v) (τ • h)-gapValue S q₀ (.pair f v) 0-
      τ*LinearForm (gapGradient S q₀ (.pair f v)) h| ≤
      τ^2*featureRectangleCurvature q₀ r f v/2 := by
  exact (feature_gap_taylor_with_gradient S q₀ f v h τ hτ).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (feature_curvature_on_rectangle q₀ r f v h hr) (sq_nonneg τ)) (by norm_num))

end
end ElevenSquare.Pending.T06
