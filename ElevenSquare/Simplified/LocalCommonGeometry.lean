import ElevenSquare.Simplified.LocalBranchCover
import ElevenSquare.Tasks.T06.ConcreteTaylorUnavailable
import ElevenSquare.Tasks.T06.ConcreteTaylorRows
import ElevenSquare.Tasks.T06.GradientsTies

/-! The original nonlinear geometry, exposed independently of the obsolete
8,448 dual vectors. Only feasibility, aliases, tied gradients and Taylor bounds
are part of this interface. The original public exact packet remains intact. -/
namespace ElevenSquare.Simplified.LocalCommon
open ElevenSquare ElevenSquare.Pending ElevenSquare.Pending.T06 ElevenSquare.Tasks.T06
noncomputable section

-- The old branch-cover lemma accepts a LocalPacket but reads only radii and
-- aliases. This private adapter supplies those exact source fields. Its unused
-- arithmetic fields are zero; no DualBounds proposition is asserted for it.
private def geometryAdapter : LocalPacket where
  radii := focusedRadii
  maxRadius := proposedMaxRadius
  representative b i := representatives (branchRows b i)
  aliases b i := rowAliases (branchRows b i)
  curvature b i := rowCurvatures (branchRows b i)
  dual _ _ _ _ := 0
  residual _ _ _ := 0

/-- The source branch cover, stated solely in terms of its actual nonlinear
rows. Closed contacts and all alias choices retain their original semantics. -/
theorem nonlinear_branch_cover (h : Displacement)
    (hrect : InRectangle focusedRadii h)
    (hpack : LocalFeasible T constructionSquare h) :
    ∃ b : Fin 128, ∀ i : Fin 42, ∃ g ∈ rowAliases (branchRows b i),
      0 ≤ gapValue T constructionSquare g h := by
  exact ElevenSquare.Simplified.LocalAlias.branch_cover_of_unavailable
    T constructionSquare geometryAdapter
    (fun _ _ => rfl) concrete_unavailable_negative h hrect hpack

/-- The source Taylor theorem, stated with the exact polynomial gradient so
that it contains no dependence on any branch-specific arithmetic certificate. -/
theorem nonlinear_row_taylor (r : Fin 56) (g : Gap) (hg : g ∈ rowAliases r)
    (v : Displacement) (hv : InRectangle focusedRadii v)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    |gapValue T constructionSquare g (τ • v) - gapValue T constructionSquare g 0 -
      τ * LinearForm (polynomialGradient r) v| ≤ τ^2*(rowCurvatures r : ℝ)/2 := by
  have hb := gap_rectangle_taylor T constructionSquare focusedRadii g v hv τ hτ
  rw [(row_aliases_tied r g hg).2] at hb
  exact hb.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (concrete_row_curvature r g hg) (sq_nonneg τ))
    (by norm_num))

end
end ElevenSquare.Simplified.LocalCommon

#print axioms ElevenSquare.Simplified.LocalCommon.nonlinear_branch_cover
#print axioms ElevenSquare.Simplified.LocalCommon.nonlinear_row_taylor
