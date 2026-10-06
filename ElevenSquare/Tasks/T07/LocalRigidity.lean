import ElevenSquare.Tasks.T07.CoordinateBridge
import ElevenSquare.Simplified.LocalCommonIsolation
import ElevenSquare.Construction

/-! The local packet identifies an anchored packing with the exact construction.
Keeping the original centered side bound then turns this identification into a
lower bound on that side. -/

namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- Once a displacement vanishes, the transported packing contains the exact
right-wall witness while still obeying the original centered side bound. -/
theorem centered_zero_displacement_requires_T {S : ℝ} (P : Packing 11 T)
    (hsmall : CenteredPacking P S) (h : Displacement)
    (hrepresentation : ∀ i,
      (P.squares i).center = perturbedCenter constructionSquare h i ∧
      (P.squares i).axis = perturbedAxis constructionSquare h i)
    (hzero : h = 0) : T ≤ S := by
  subst h
  have hcenter : (P.squares 1).center = (constructionSquare 1).center := by
    simpa [perturbedCenter, Prod.add_def] using (hrepresentation 1).1
  have haxis : (P.squares 1).axis = (constructionSquare 1).axis := by
    simpa [perturbedAxis] using (hrepresentation 1).2
  have heq : P.squares 1 = constructionSquare 1 := unitSquare_ext hcenter haxis
  have hcorner : ClosedSquare (P.squares 1) (T, 0) := by
    rw [heq]
    exact construction_right_corner
  have hwidth := (hsmall 1 (T, 0) hcorner).1
  dsimp [InCenteredContainer] at hwidth
  rw [show T - T / 2 = T / 2 by ring, abs_of_pos (half_pos T_pos)] at hwidth
  linarith

/-- A complete focused rectangle enclosure plus the local packet rules out a
packing in a strictly smaller centered container. The local packet itself is
the exact-data upstream contract in `S08_ExactPacket`. -/
theorem focused_centered_requires_T {S : ℝ} (P : Packing 11 T)
    (hsmall : CenteredPacking P S) (h : Displacement)
    (hrect : InRectangle focusedRadii h)
    (hrepresentation : ∀ i,
      (P.squares i).center = perturbedCenter constructionSquare h i ∧
      (P.squares i).axis = perturbedAxis constructionSquare h i) : T ≤ S := by
  have hfeasible : LocalFeasible T constructionSquare h := ⟨P, hrepresentation⟩
  exact centered_zero_displacement_requires_T P hsmall h hrepresentation
    (ElevenSquare.Simplified.LocalCommon.construction_locally_isolated h hrect hfeasible)

end
end ElevenSquare.Tasks.T07
