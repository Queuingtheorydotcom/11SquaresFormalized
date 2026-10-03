import ElevenSquare.Simplified.LocalCommonBranchCone
import ElevenSquare.Simplified.LocalCommonDualBounds
import ElevenSquare.Simplified.LocalCommonGeometry
import ElevenSquare.Pending.S08_Taylor

/-! Local isolation of the actual eleven-square construction using a single
forty-row necessary cone and sixty-six rectangle-weighted dual certificates.
The old branch cover and Taylor estimates retain all closed contacts and ties.
The only change is that convex combinations remove the owner-choice branches
before the dual calculation. -/
namespace ElevenSquare.Simplified.LocalCommon
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T06
noncomputable section
set_option maxHeartbeats 0

/-- Every feasible displacement satisfies the same forty quadratic row bounds.
The nonlinear feature choices are discharged by the original branch cover;
convexity eliminates their owner dependence in the linearized cone. -/
theorem packing_common_rows (h : Displacement)
    (hrect : InRectangle focusedRadii h)
    (hpack : LocalFeasible T constructionSquare h)
    (τ : ℝ) (hτ : 0 < τ) (hτle : τ ≤ 1)
    (hbox : ∀ k, |h k| ≤ τ * (radiusQ k : ℝ)) :
    ∀ i : Fin 40, -(τ^2*(curvatureQ i : ℝ)/2) ≤
      dot (polynomialGradient (rowIndex i)) h := by
  let v : Displacement := fun k => h k / τ
  have hτne : τ ≠ 0 := ne_of_gt hτ
  have hv : InRectangle focusedRadii v := by
    intro k
    change |h k / τ| ≤ focusedRadii k
    rw [← radii_eq_focused k, abs_div, abs_of_pos hτ]
    apply (div_le_iff₀ hτ).mpr
    simpa only [mul_comm] using hbox k
  have hscale : τ • v = h := by
    funext k
    dsimp [v]
    field_simp <;> ring
  have linear_scale (a : Fin 33 → ℝ) :
      τ * LinearForm a v = LinearForm a h := by
    unfold LinearForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [v]
    field_simp <;> ring
  obtain ⟨b, hb⟩ := nonlinear_branch_cover h hrect hpack
  have hrows (i : Fin 42) :
      -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
        dot (polynomialGradient (branchRows b i)) h := by
    obtain ⟨g, hg, hgf⟩ := hb i
    have hzero := (row_aliases_tied (branchRows b i) g hg).1
    have herr := nonlinear_row_taylor (branchRows b i) g hg v hv τ ⟨hτ.le, hτle⟩
    rw [hscale, linear_scale] at herr
    exact tied_gap_linear_lower (gapValue T constructionSquare g)
      (polynomialGradient (branchRows b i)) h τ
      (rowCurvatures (branchRows b i) : ℝ) hzero hgf herr
  exact common_rows b τ h hrows

/-- The construction is isolated in the original closed focused rectangle.
This has precisely the geometric conclusion of the old exact-packet theorem,
while its arithmetic checks use one common cone instead of 128 cones. -/
theorem construction_locally_isolated (h : Displacement)
    (hrect : InRectangle focusedRadii h)
    (hpack : LocalFeasible T constructionSquare h) : h = 0 := by
  apply branchwise_isolation (n := 32) (m := 40) (branches := 1)
    (LocalFeasible T constructionSquare)
    (fun k => (radiusQ k : ℝ))
    (fun _ i => polynomialGradient (rowIndex i))
    (fun _ i => (curvatureQ i : ℝ))
    (fun _ j s i => (weight j s i : ℝ))
    (fun _ j s => (residualQ j s : ℝ))
    radii_positive (fun _ => curvature_nonneg)
    (fun _ => weight_nonneg) (fun _ => residual_bound)
    (fun _ => strict_margin) ?_ h ?_ hpack
  · intro v hv τ hτ hτle hbox
    have hvr : InRectangle focusedRadii v := by
      intro k
      rw [← radii_eq_focused k]
      exact (hbox k).trans (by
        simpa using mul_le_mul_of_nonneg_right hτle (radii_positive k).le)
    exact ⟨0, packing_common_rows v hvr hv τ hτ hτle hbox⟩
  · intro k
    rw [radii_eq_focused]
    exact hrect k

end
end ElevenSquare.Simplified.LocalCommon

#print axioms ElevenSquare.Simplified.LocalCommon.packing_common_rows
#print axioms ElevenSquare.Simplified.LocalCommon.construction_locally_isolated
