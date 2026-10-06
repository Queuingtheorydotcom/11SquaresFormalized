import ElevenSquare.Tasks.T07.NearCentersData9
import ElevenSquare.Tasks.T07.NearFieldBridge

/-! Exact endpoint tests for the field-coordinate near box at role 9. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem nearCenterBox9_numeric :
    nearCenter90Hi - focusedRadii (coordinate (9 : Owner) (0 : Fin 3)) ≤
      (nearBox9.ly : ℝ)/fieldScale-coverCap/2 ∧
    (nearBox9.hy : ℝ)/fieldScale-coverCap/2 ≤
      nearCenter90Lo + focusedRadii (coordinate (9 : Owner) (0 : Fin 3)) ∧
    nearCenter91Hi - focusedRadii (coordinate (9 : Owner) (1 : Fin 3)) ≤
      coverCap/2-(nearBox9.hx : ℝ)/fieldScale ∧
    coverCap/2-(nearBox9.lx : ℝ)/fieldScale ≤
      nearCenter91Lo + focusedRadii (coordinate (9 : Owner) (1 : Fin 3)) := by
  have hr0 : focusedRadii (coordinate (9 : Owner) (0 : Fin 3)) = (293551/400000000 : ℝ) := by rfl
  have hr1 : focusedRadii (coordinate (9 : Owner) (1 : Fin 3)) = (10335557/10000000000 : ℝ) := by rfl
  rw [hr0, hr1]
  dsimp only [nearBox9]
  simp only [Rat.cast_divInt]
  norm_num [nearCenter90Hi, nearCenter90Lo, nearCenter91Hi,
    nearCenter91Lo, nearBox9, fieldScale, coverCap]

theorem finalNear_center_role9 (p : Point) (hp : InFinalNearCenter (9 : Fin 11) p) :
    |(fieldToLocal p).1-(constructionCenter 9).1| ≤
      focusedRadii (coordinate (9 : Owner) (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter 9).2| ≤
      focusedRadii (coordinate (9 : Owner) (1 : Fin 3)) := by
  have hbox : inRect (nearBox9.lx : ℝ) (nearBox9.hx : ℝ)
      (nearBox9.ly : ℝ) (nearBox9.hy : ℝ) p := by
    simpa [nearFieldBox] using finalNear_center_field_enclosure (9 : Fin 11) p hp
  rcases nearCenterBox9_numeric with ⟨hxl, hxr, hyl, hyr⟩
  exact ⟨field_rectangle_local_x hbox nearCenter90_bounds hxl hxr,
    field_rectangle_local_y hbox nearCenter91_bounds hyl hyr⟩

end
end ElevenSquare.Tasks.T07
