import ElevenSquare.Tasks.T06.Gradients
import ElevenSquare.Tasks.T06.GradientsPolynomial

namespace ElevenSquare.Pending.T06
noncomputable section

theorem polyEval_zero (x : ℝ) : polyEval ![0, 0, 0, 0, 0, 0, 0, 0] x = 0 := by
  rw [polyEval_vec]
  simp

theorem wallGradientFormula_zero (q₀ : Owner → UnitSquare) (i : Owner)
    (v w : Fin 4) (j : Fin 33)
    (hx : coordinate i 0 ≠ j) (hy : coordinate i 1 ≠ j)
    (hθ : coordinate i 2 ≠ j) : wallGradientFormula q₀ i v w j = 0 := by
  fin_cases w <;> simp [wallGradientFormula, cornerVelocity, centerVelocity,
    axisVelocity, coordinateDelta, hx, hy, hθ, perp]

theorem pairGradientFormula_zero (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (v : Fin 4) (j : Fin 33)
    (hox : coordinate f.owner 0 ≠ j) (hoy : coordinate f.owner 1 ≠ j)
    (hoθ : coordinate f.owner 2 ≠ j)
    (hpx : coordinate f.other 0 ≠ j) (hpy : coordinate f.other 1 ≠ j)
    (hpθ : coordinate f.other 2 ≠ j) : pairGradientFormula q₀ f v j = 0 := by
  simp [pairGradientFormula, cornerVelocity, centerVelocity, axisVelocity,
    normalVelocity, coordinateDelta, hox, hoy, hoθ, hpx, hpy, hpθ, perp, dot]

/-- Zero entries of the shared coefficient table need only one polynomial proof. -/
theorem polynomialGradient_of_zero_class {r : Fin 56} {j : Fin 33}
    (h : gradientClass r j = 1) : ElevenSquare.Tasks.T06.polynomialGradient r j = 0 := by
  change polyEval (gradientCoefficients (gradientClass r j)) u = 0
  rw [h]
  exact polyEval_zero u

/-- Coordinates outside the wall owner's support have the shared zero gradient. -/
theorem wallGradient_polynomial_zero {r : Fin 56} {j : Fin 33}
    {i : Owner} {v w : Fin 4}
    (hx : coordinate i 0 ≠ j) (hy : coordinate i 1 ≠ j)
    (hθ : coordinate i 2 ≠ j) (h : gradientClass r j = 1) :
    gapGradient T constructionSquare (.wall i v w) j =
      ElevenSquare.Tasks.T06.polynomialGradient r j := by
  rw [gapGradient_wall, wallGradientFormula_zero constructionSquare i v w j hx hy hθ,
    polynomialGradient_of_zero_class h]

/-- A pair gap depends only on its two owners' six displacement coordinates. -/
theorem pairGradient_polynomial_zero {r : Fin 56} {j : Fin 33}
    {f : SeparationFeature} {v : Fin 4}
    (hox : coordinate f.owner 0 ≠ j) (hoy : coordinate f.owner 1 ≠ j)
    (hoθ : coordinate f.owner 2 ≠ j)
    (hpx : coordinate f.other 0 ≠ j) (hpy : coordinate f.other 1 ≠ j)
    (hpθ : coordinate f.other 2 ≠ j) (h : gradientClass r j = 1) :
    gapGradient T constructionSquare (.pair f v) j =
      ElevenSquare.Tasks.T06.polynomialGradient r j := by
  rw [gapGradient_pair,
    pairGradientFormula_zero constructionSquare f v j hox hoy hoθ hpx hpy hpθ,
    polynomialGradient_of_zero_class h]

end
end ElevenSquare.Pending.T06
