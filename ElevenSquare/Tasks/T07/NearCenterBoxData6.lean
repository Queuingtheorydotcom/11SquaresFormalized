import ElevenSquare.Tasks.T07.NearCentersData6
import ElevenSquare.Tasks.T07.NearFieldBridge

/-! Exact endpoint tests for the field-coordinate near box at role 6. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem nearCenterBox6_numeric :
    nearCenter60Hi - focusedRadii (coordinate (6 : Owner) (0 : Fin 3)) ≤
      (nearBox6.ly : ℝ)/fieldScale-coverCap/2 ∧
    (nearBox6.hy : ℝ)/fieldScale-coverCap/2 ≤
      nearCenter60Lo + focusedRadii (coordinate (6 : Owner) (0 : Fin 3)) ∧
    nearCenter61Hi - focusedRadii (coordinate (6 : Owner) (1 : Fin 3)) ≤
      coverCap/2-(nearBox6.hx : ℝ)/fieldScale ∧
    coverCap/2-(nearBox6.lx : ℝ)/fieldScale ≤
      nearCenter61Lo + focusedRadii (coordinate (6 : Owner) (1 : Fin 3)) := by
  have hr0 : focusedRadii (coordinate (6 : Owner) (0 : Fin 3)) = (678279/500000000 : ℝ) := by rfl
  have hr1 : focusedRadii (coordinate (6 : Owner) (1 : Fin 3)) = (4124329/5000000000 : ℝ) := by rfl
  rw [hr0, hr1]
  dsimp only [nearBox6]
  simp only [Rat.cast_divInt]
  norm_num [nearCenter60Hi, nearCenter60Lo, nearCenter61Hi,
    nearCenter61Lo, nearBox6, fieldScale, coverCap]

theorem finalNear_center_role6 (p : Point) (hp : InFinalNearCenter (6 : Fin 11) p) :
    |(fieldToLocal p).1-(constructionCenter 6).1| ≤
      focusedRadii (coordinate (6 : Owner) (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter 6).2| ≤
      focusedRadii (coordinate (6 : Owner) (1 : Fin 3)) := by
  have hbox : inRect (nearBox6.lx : ℝ) (nearBox6.hx : ℝ)
      (nearBox6.ly : ℝ) (nearBox6.hy : ℝ) p := by
    simpa [nearFieldBox] using finalNear_center_field_enclosure (6 : Fin 11) p hp
  rcases nearCenterBox6_numeric with ⟨hxl, hxr, hyl, hyr⟩
  exact ⟨field_rectangle_local_x hbox nearCenter60_bounds hxl hxr,
    field_rectangle_local_y hbox nearCenter61_bounds hyl hyr⟩

end
end ElevenSquare.Tasks.T07
