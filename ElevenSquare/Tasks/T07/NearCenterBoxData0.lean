import ElevenSquare.Tasks.T07.NearCentersData0
import ElevenSquare.Tasks.T07.NearFieldBridge

/-! Exact endpoint tests for the field-coordinate near box at role 0. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem nearCenterBox0_numeric :
    nearCenter00Hi - focusedRadii (coordinate (0 : Owner) (0 : Fin 3)) ≤
      (nearBox0.ly : ℝ)/fieldScale-coverCap/2 ∧
    (nearBox0.hy : ℝ)/fieldScale-coverCap/2 ≤
      nearCenter00Lo + focusedRadii (coordinate (0 : Owner) (0 : Fin 3)) ∧
    nearCenter01Hi - focusedRadii (coordinate (0 : Owner) (1 : Fin 3)) ≤
      coverCap/2-(nearBox0.hx : ℝ)/fieldScale ∧
    coverCap/2-(nearBox0.lx : ℝ)/fieldScale ≤
      nearCenter01Lo + focusedRadii (coordinate (0 : Owner) (1 : Fin 3)) := by
  dsimp only [nearBox0]
  simp only [Rat.cast_divInt]
  norm_num [nearCenter00Hi, nearCenter00Lo, nearCenter01Hi,
    nearCenter01Lo, focusedRadii, coordinate, nearBox0, fieldScale, coverCap]

theorem finalNear_center_role0 (p : Point) (hp : InFinalNearCenter (0 : Fin 11) p) :
    |(fieldToLocal p).1-(constructionCenter 0).1| ≤
      focusedRadii (coordinate (0 : Owner) (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter 0).2| ≤
      focusedRadii (coordinate (0 : Owner) (1 : Fin 3)) := by
  have hbox : inRect (nearBox0.lx : ℝ) (nearBox0.hx : ℝ)
      (nearBox0.ly : ℝ) (nearBox0.hy : ℝ) p := by
    simpa [nearFieldBox] using finalNear_center_field_enclosure (0 : Fin 11) p hp
  rcases nearCenterBox0_numeric with ⟨hxl, hxr, hyl, hyr⟩
  exact ⟨field_rectangle_local_x hbox nearCenter00_bounds hxl hxr,
    field_rectangle_local_y hbox nearCenter01_bounds hyl hyr⟩

end
end ElevenSquare.Tasks.T07
