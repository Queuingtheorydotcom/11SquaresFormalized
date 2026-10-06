import ElevenSquare.Tasks.T07.NearCentersData8
import ElevenSquare.Tasks.T07.NearFieldBridge

/-! Exact endpoint tests for the field-coordinate near box at role 8. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem nearCenterBox8_numeric :
    nearCenter80Hi - focusedRadii (coordinate (8 : Owner) (0 : Fin 3)) ≤
      (nearBox8.ly : ℝ)/fieldScale-coverCap/2 ∧
    (nearBox8.hy : ℝ)/fieldScale-coverCap/2 ≤
      nearCenter80Lo + focusedRadii (coordinate (8 : Owner) (0 : Fin 3)) ∧
    nearCenter81Hi - focusedRadii (coordinate (8 : Owner) (1 : Fin 3)) ≤
      coverCap/2-(nearBox8.hx : ℝ)/fieldScale ∧
    coverCap/2-(nearBox8.lx : ℝ)/fieldScale ≤
      nearCenter81Lo + focusedRadii (coordinate (8 : Owner) (1 : Fin 3)) := by
  have hr0 : focusedRadii (coordinate (8 : Owner) (0 : Fin 3)) = (9356857/10000000000 : ℝ) := by rfl
  have hr1 : focusedRadii (coordinate (8 : Owner) (1 : Fin 3)) = (8671199/10000000000 : ℝ) := by rfl
  rw [hr0, hr1]
  dsimp only [nearBox8]
  simp only [Rat.cast_divInt]
  norm_num [nearCenter80Hi, nearCenter80Lo, nearCenter81Hi,
    nearCenter81Lo, nearBox8, fieldScale, coverCap]

theorem finalNear_center_role8 (p : Point) (hp : InFinalNearCenter (8 : Fin 11) p) :
    |(fieldToLocal p).1-(constructionCenter 8).1| ≤
      focusedRadii (coordinate (8 : Owner) (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter 8).2| ≤
      focusedRadii (coordinate (8 : Owner) (1 : Fin 3)) := by
  have hbox : inRect (nearBox8.lx : ℝ) (nearBox8.hx : ℝ)
      (nearBox8.ly : ℝ) (nearBox8.hy : ℝ) p := by
    simpa [nearFieldBox] using finalNear_center_field_enclosure (8 : Fin 11) p hp
  rcases nearCenterBox8_numeric with ⟨hxl, hxr, hyl, hyr⟩
  exact ⟨field_rectangle_local_x hbox nearCenter80_bounds hxl hxr,
    field_rectangle_local_y hbox nearCenter81_bounds hyl hyr⟩

end
end ElevenSquare.Tasks.T07
