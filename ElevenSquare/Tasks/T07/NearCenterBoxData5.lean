import ElevenSquare.Tasks.T07.NearCentersData5
import ElevenSquare.Tasks.T07.NearFieldBridge

/-! Exact endpoint tests for the field-coordinate near box at role 5. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem nearCenterBox5_numeric :
    nearCenter50Hi - focusedRadii (coordinate (5 : Owner) (0 : Fin 3)) ≤
      (nearBox5.ly : ℝ)/fieldScale-coverCap/2 ∧
    (nearBox5.hy : ℝ)/fieldScale-coverCap/2 ≤
      nearCenter50Lo + focusedRadii (coordinate (5 : Owner) (0 : Fin 3)) ∧
    nearCenter51Hi - focusedRadii (coordinate (5 : Owner) (1 : Fin 3)) ≤
      coverCap/2-(nearBox5.hx : ℝ)/fieldScale ∧
    coverCap/2-(nearBox5.lx : ℝ)/fieldScale ≤
      nearCenter51Lo + focusedRadii (coordinate (5 : Owner) (1 : Fin 3)) := by
  have hr0 : focusedRadii (coordinate (5 : Owner) (0 : Fin 3)) = (12900283/10000000000 : ℝ) := by rfl
  have hr1 : focusedRadii (coordinate (5 : Owner) (1 : Fin 3)) = (534153/500000000 : ℝ) := by rfl
  rw [hr0, hr1]
  dsimp only [nearBox5]
  simp only [Rat.cast_divInt]
  norm_num [nearCenter50Hi, nearCenter50Lo, nearCenter51Hi,
    nearCenter51Lo, nearBox5, fieldScale, coverCap]

theorem finalNear_center_role5 (p : Point) (hp : InFinalNearCenter (5 : Fin 11) p) :
    |(fieldToLocal p).1-(constructionCenter 5).1| ≤
      focusedRadii (coordinate (5 : Owner) (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter 5).2| ≤
      focusedRadii (coordinate (5 : Owner) (1 : Fin 3)) := by
  have hbox : inRect (nearBox5.lx : ℝ) (nearBox5.hx : ℝ)
      (nearBox5.ly : ℝ) (nearBox5.hy : ℝ) p := by
    simpa [nearFieldBox] using finalNear_center_field_enclosure (5 : Fin 11) p hp
  rcases nearCenterBox5_numeric with ⟨hxl, hxr, hyl, hyr⟩
  exact ⟨field_rectangle_local_x hbox nearCenter50_bounds hxl hxr,
    field_rectangle_local_y hbox nearCenter51_bounds hyl hyr⟩

end
end ElevenSquare.Tasks.T07
