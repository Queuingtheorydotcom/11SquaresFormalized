import ElevenSquare.Tasks.T07.NearCentersData4
import ElevenSquare.Tasks.T07.NearFieldBridge

/-! Exact endpoint tests for the field-coordinate near box at role 4. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem nearCenterBox4_numeric :
    nearCenter40Hi - focusedRadii (coordinate (4 : Owner) (0 : Fin 3)) ≤
      (nearBox4.ly : ℝ)/fieldScale-coverCap/2 ∧
    (nearBox4.hy : ℝ)/fieldScale-coverCap/2 ≤
      nearCenter40Lo + focusedRadii (coordinate (4 : Owner) (0 : Fin 3)) ∧
    nearCenter41Hi - focusedRadii (coordinate (4 : Owner) (1 : Fin 3)) ≤
      coverCap/2-(nearBox4.hx : ℝ)/fieldScale ∧
    coverCap/2-(nearBox4.lx : ℝ)/fieldScale ≤
      nearCenter41Lo + focusedRadii (coordinate (4 : Owner) (1 : Fin 3)) := by
  have hr0 : focusedRadii (coordinate (4 : Owner) (0 : Fin 3)) = (4087019/2500000000 : ℝ) := by rfl
  have hr1 : focusedRadii (coordinate (4 : Owner) (1 : Fin 3)) = (13962901/10000000000 : ℝ) := by rfl
  rw [hr0, hr1]
  dsimp only [nearBox4]
  simp only [Rat.cast_divInt]
  norm_num [nearCenter40Hi, nearCenter40Lo, nearCenter41Hi,
    nearCenter41Lo, nearBox4, fieldScale, coverCap]

theorem finalNear_center_role4 (p : Point) (hp : InFinalNearCenter (4 : Fin 11) p) :
    |(fieldToLocal p).1-(constructionCenter 4).1| ≤
      focusedRadii (coordinate (4 : Owner) (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter 4).2| ≤
      focusedRadii (coordinate (4 : Owner) (1 : Fin 3)) := by
  have hbox : inRect (nearBox4.lx : ℝ) (nearBox4.hx : ℝ)
      (nearBox4.ly : ℝ) (nearBox4.hy : ℝ) p := by
    simpa [nearFieldBox] using finalNear_center_field_enclosure (4 : Fin 11) p hp
  rcases nearCenterBox4_numeric with ⟨hxl, hxr, hyl, hyr⟩
  exact ⟨field_rectangle_local_x hbox nearCenter40_bounds hxl hxr,
    field_rectangle_local_y hbox nearCenter41_bounds hyl hyr⟩

end
end ElevenSquare.Tasks.T07
