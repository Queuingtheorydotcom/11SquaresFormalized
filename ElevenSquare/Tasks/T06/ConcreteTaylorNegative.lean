import ElevenSquare.Tasks.T06.ConcreteTaylorBase

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06
noncomputable section

theorem concrete_feature_linear_bound (q : Owner → UnitSquare)
    (r : Fin 33 → ℝ) (f : SeparationFeature) (v : Fin 4)
    (L D C : ℝ) (h : Displacement) (hh : InRectangle r h)
    (hr : ∀ j, 0 ≤ r j)
    (hL : |(featureNormal q f).1| + |(featureNormal q f).2| ≤ L)
    (hD : |dot (featureCenterDifference q f) (perp (featureNormal q f))| ≤ D)
    (hC : |dot (perp (cornerOffset q f.other v)) (featureNormal q f)| ≤ C) :
    |featureRadialLinear q f v h| ≤
      L*featureTranslationRadius r f + r (coordinate f.owner 2)*D +
      (r (coordinate f.other 2)+r (coordinate f.owner 2))*C := by
  have ht : 0 ≤ featureTranslationRadius r f := by
    unfold featureTranslationRadius
    exact add_nonneg (add_nonneg (hr _) (hr _)) (add_nonneg (hr _) (hr _))
  have hv := feature_velocity_bound q r f h hh
  have hv' : |dot (featureCenterVelocity h f) (featureNormal q f)| ≤
      L*featureTranslationRadius r f := by
    have hB : featureVelocityBound q r f ≤ L*featureTranslationRadius r f :=
      mul_le_mul_of_nonneg_right hL ht
    linarith [abs_nonneg (dot (featureCenterVelocity h f) (perp (featureNormal q f)))]
  have hd := mul_le_mul (hh (coordinate f.owner 2)) hD
    (abs_nonneg (dot (featureCenterDifference q f) (perp (featureNormal q f)))) (hr _)
  have hdiff : |h (coordinate f.other 2)-h (coordinate f.owner 2)| ≤
      r (coordinate f.other 2)+r (coordinate f.owner 2) :=
    (abs_sub _ _).trans (add_le_add (hh _) (hh _))
  have hc := mul_le_mul hdiff hC
    (abs_nonneg (dot (perp (cornerOffset q f.other v)) (featureNormal q f)))
    (add_nonneg (hr _) (hr _))
  unfold featureRadialLinear
  rw [abs_mul, abs_radialFeatureSign, one_mul]
  calc
    _ ≤ |dot (featureCenterVelocity h f) (featureNormal q f)| +
        |h (coordinate f.owner 2)*dot (featureCenterDifference q f) (perp (featureNormal q f))| +
        |(h (coordinate f.other 2)-h (coordinate f.owner 2))*
          dot (perp (cornerOffset q f.other v)) (featureNormal q f)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [abs_mul]
      exact add_le_add (add_le_add hv' hd) hc

theorem concrete_feature_negative (S : ℝ) (q : Owner → UnitSquare)
    (r : Fin 33 → ℝ) (f : SeparationFeature) (v : Fin 4)
    (V L D C K : ℝ) (hr : ∀ j, 0 ≤ r j)
    (hV : gapValue S q (.pair f v) 0 ≤ V)
    (hL : |(featureNormal q f).1| + |(featureNormal q f).2| ≤ L)
    (hD : |dot (featureCenterDifference q f) (perp (featureNormal q f))| ≤ D)
    (hC : |dot (perp (cornerOffset q f.other v)) (featureNormal q f)| ≤ C)
    (hK : featureRectangleCurvature q r f v ≤ K)
    (hmargin : V+L*featureTranslationRadius r f+r (coordinate f.owner 2)*D+
      (r (coordinate f.other 2)+r (coordinate f.owner 2))*C+K/2 < 0) :
    ∀ h, InRectangle r h → gapValue S q (.pair f v) h < 0 := by
  intro h hh
  have hl := concrete_feature_linear_bound q r f v L D C h hh hr hL hD hC
  have ht := feature_gap_taylor_on_rectangle S q r f v h hh 1 (by norm_num)
  rw [feature_gradient_linearForm] at ht
  simp only [one_smul, one_pow, one_mul] at ht
  have he := le_abs_self (gapValue S q (.pair f v) h-gapValue S q (.pair f v) 0-
    featureRadialLinear q f v h)
  have he' := le_abs_self (featureRadialLinear q f v h)
  linarith

end
end ElevenSquare.Tasks.T06
