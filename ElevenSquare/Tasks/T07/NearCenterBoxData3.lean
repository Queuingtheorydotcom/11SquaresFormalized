import ElevenSquare.Tasks.T07.NearCentersData3
import ElevenSquare.Tasks.T07.NearFieldBridge

/-! Exact endpoint tests for the field-coordinate near box at role 3. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem nearCenterBox3_numeric :
    nearCenter30Hi - focusedRadii (coordinate (3 : Owner) (0 : Fin 3)) ≤
      (nearBox3.ly : ℝ)/fieldScale-coverCap/2 ∧
    (nearBox3.hy : ℝ)/fieldScale-coverCap/2 ≤
      nearCenter30Lo + focusedRadii (coordinate (3 : Owner) (0 : Fin 3)) ∧
    nearCenter31Hi - focusedRadii (coordinate (3 : Owner) (1 : Fin 3)) ≤
      coverCap/2-(nearBox3.hx : ℝ)/fieldScale ∧
    coverCap/2-(nearBox3.lx : ℝ)/fieldScale ≤
      nearCenter31Lo + focusedRadii (coordinate (3 : Owner) (1 : Fin 3)) := by
  have hr0 : focusedRadii (coordinate (3 : Owner) (0 : Fin 3)) = (1635053/1000000000 : ℝ) := by rfl
  have hr1 : focusedRadii (coordinate (3 : Owner) (1 : Fin 3)) = (10683139/10000000000 : ℝ) := by rfl
  rw [hr0, hr1]
  dsimp only [nearBox3]
  simp only [Rat.cast_divInt]
  norm_num [nearCenter30Hi, nearCenter30Lo, nearCenter31Hi,
    nearCenter31Lo, nearBox3, fieldScale, coverCap]

theorem finalNear_center_role3 (p : Point) (hp : InFinalNearCenter (3 : Fin 11) p) :
    |(fieldToLocal p).1-(constructionCenter 3).1| ≤
      focusedRadii (coordinate (3 : Owner) (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter 3).2| ≤
      focusedRadii (coordinate (3 : Owner) (1 : Fin 3)) := by
  have hbox : inRect (nearBox3.lx : ℝ) (nearBox3.hx : ℝ)
      (nearBox3.ly : ℝ) (nearBox3.hy : ℝ) p := by
    simpa [nearFieldBox] using finalNear_center_field_enclosure (3 : Fin 11) p hp
  rcases nearCenterBox3_numeric with ⟨hxl, hxr, hyl, hyr⟩
  exact ⟨field_rectangle_local_x hbox nearCenter30_bounds hxl hxr,
    field_rectangle_local_y hbox nearCenter31_bounds hyl hyr⟩

end
end ElevenSquare.Tasks.T07
