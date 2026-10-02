import ElevenSquare.Tasks.T07.NearCentersData1
import ElevenSquare.Tasks.T07.NearFieldBridge

/-! Exact endpoint tests for the field-coordinate near box at role 1. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem nearCenterBox1_numeric :
    nearCenter10Hi - focusedRadii (coordinate (1 : Owner) (0 : Fin 3)) ≤
      (nearBox1.ly : ℝ)/fieldScale-coverCap/2 ∧
    (nearBox1.hy : ℝ)/fieldScale-coverCap/2 ≤
      nearCenter10Lo + focusedRadii (coordinate (1 : Owner) (0 : Fin 3)) ∧
    nearCenter11Hi - focusedRadii (coordinate (1 : Owner) (1 : Fin 3)) ≤
      coverCap/2-(nearBox1.hx : ℝ)/fieldScale ∧
    coverCap/2-(nearBox1.lx : ℝ)/fieldScale ≤
      nearCenter11Lo + focusedRadii (coordinate (1 : Owner) (1 : Fin 3)) := by
  dsimp only [nearBox1]
  simp only [Rat.cast_divInt]
  norm_num [nearCenter10Hi, nearCenter10Lo, nearCenter11Hi,
    nearCenter11Lo, focusedRadii, coordinate, nearBox1, fieldScale, coverCap]

theorem finalNear_center_role1 (p : Point) (hp : InFinalNearCenter (1 : Fin 11) p) :
    |(fieldToLocal p).1-(constructionCenter 1).1| ≤
      focusedRadii (coordinate (1 : Owner) (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter 1).2| ≤
      focusedRadii (coordinate (1 : Owner) (1 : Fin 3)) := by
  have hbox : inRect (nearBox1.lx : ℝ) (nearBox1.hx : ℝ)
      (nearBox1.ly : ℝ) (nearBox1.hy : ℝ) p := by
    simpa [nearFieldBox] using finalNear_center_field_enclosure (1 : Fin 11) p hp
  rcases nearCenterBox1_numeric with ⟨hxl, hxr, hyl, hyr⟩
  exact ⟨field_rectangle_local_x hbox nearCenter10_bounds hxl hxr,
    field_rectangle_local_y hbox nearCenter11_bounds hyl hyr⟩

end
end ElevenSquare.Tasks.T07
