import ElevenSquare.Tasks.T07.NearCentersData7
import ElevenSquare.Tasks.T07.NearFieldBridge

/-! Exact endpoint tests for the field-coordinate near box at role 7. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem nearCenterBox7_numeric :
    nearCenter70Hi - focusedRadii (coordinate (7 : Owner) (0 : Fin 3)) ≤
      (nearBox7.ly : ℝ)/fieldScale-coverCap/2 ∧
    (nearBox7.hy : ℝ)/fieldScale-coverCap/2 ≤
      nearCenter70Lo + focusedRadii (coordinate (7 : Owner) (0 : Fin 3)) ∧
    nearCenter71Hi - focusedRadii (coordinate (7 : Owner) (1 : Fin 3)) ≤
      coverCap/2-(nearBox7.hx : ℝ)/fieldScale ∧
    coverCap/2-(nearBox7.lx : ℝ)/fieldScale ≤
      nearCenter71Lo + focusedRadii (coordinate (7 : Owner) (1 : Fin 3)) := by
  have hr0 : focusedRadii (coordinate (7 : Owner) (0 : Fin 3)) = (11182451/10000000000 : ℝ) := by rfl
  have hr1 : focusedRadii (coordinate (7 : Owner) (1 : Fin 3)) = (3232837/5000000000 : ℝ) := by rfl
  rw [hr0, hr1]
  dsimp only [nearBox7]
  simp only [Rat.cast_divInt]
  norm_num [nearCenter70Hi, nearCenter70Lo, nearCenter71Hi,
    nearCenter71Lo, nearBox7, fieldScale, coverCap]

theorem finalNear_center_role7 (p : Point) (hp : InFinalNearCenter (7 : Fin 11) p) :
    |(fieldToLocal p).1-(constructionCenter 7).1| ≤
      focusedRadii (coordinate (7 : Owner) (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter 7).2| ≤
      focusedRadii (coordinate (7 : Owner) (1 : Fin 3)) := by
  have hbox : inRect (nearBox7.lx : ℝ) (nearBox7.hx : ℝ)
      (nearBox7.ly : ℝ) (nearBox7.hy : ℝ) p := by
    simpa [nearFieldBox] using finalNear_center_field_enclosure (7 : Fin 11) p hp
  rcases nearCenterBox7_numeric with ⟨hxl, hxr, hyl, hyr⟩
  exact ⟨field_rectangle_local_x hbox nearCenter70_bounds hxl hxr,
    field_rectangle_local_y hbox nearCenter71_bounds hyl hyr⟩

end
end ElevenSquare.Tasks.T07
