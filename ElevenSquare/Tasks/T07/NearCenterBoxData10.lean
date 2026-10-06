import ElevenSquare.Tasks.T07.NearCentersData10
import ElevenSquare.Tasks.T07.NearFieldBridge

/-! Exact endpoint tests for the field-coordinate near box at role 10. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem nearCenterBox10_numeric :
    nearCenter100Hi - focusedRadii (coordinate (10 : Owner) (0 : Fin 3)) ≤
      (nearBox10.ly : ℝ)/fieldScale-coverCap/2 ∧
    (nearBox10.hy : ℝ)/fieldScale-coverCap/2 ≤
      nearCenter100Lo + focusedRadii (coordinate (10 : Owner) (0 : Fin 3)) ∧
    nearCenter101Hi - focusedRadii (coordinate (10 : Owner) (1 : Fin 3)) ≤
      coverCap/2-(nearBox10.hx : ℝ)/fieldScale ∧
    coverCap/2-(nearBox10.lx : ℝ)/fieldScale ≤
      nearCenter101Lo + focusedRadii (coordinate (10 : Owner) (1 : Fin 3)) := by
  have hr0 : focusedRadii (coordinate (10 : Owner) (0 : Fin 3)) = (1920157/2500000000 : ℝ) := by rfl
  have hr1 : focusedRadii (coordinate (10 : Owner) (1 : Fin 3)) = (8222903/2500000000 : ℝ) := by rfl
  rw [hr0, hr1]
  dsimp only [nearBox10]
  simp only [Rat.cast_divInt]
  norm_num [nearCenter100Hi, nearCenter100Lo, nearCenter101Hi,
    nearCenter101Lo, nearBox10, fieldScale, coverCap]

theorem finalNear_center_role10 (p : Point) (hp : InFinalNearCenter (10 : Fin 11) p) :
    |(fieldToLocal p).1-(constructionCenter 10).1| ≤
      focusedRadii (coordinate (10 : Owner) (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter 10).2| ≤
      focusedRadii (coordinate (10 : Owner) (1 : Fin 3)) := by
  have hbox : inRect (nearBox10.lx : ℝ) (nearBox10.hx : ℝ)
      (nearBox10.ly : ℝ) (nearBox10.hy : ℝ) p := by
    simpa [nearFieldBox] using finalNear_center_field_enclosure (10 : Fin 11) p hp
  rcases nearCenterBox10_numeric with ⟨hxl, hxr, hyl, hyr⟩
  exact ⟨field_rectangle_local_x hbox nearCenter100_bounds hxl hxr,
    field_rectangle_local_y hbox nearCenter101_bounds hyl hyr⟩

end
end ElevenSquare.Tasks.T07
