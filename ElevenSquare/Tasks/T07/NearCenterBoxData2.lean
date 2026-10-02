import ElevenSquare.Tasks.T07.NearCentersData2
import ElevenSquare.Tasks.T07.NearFieldBridge

/-! Exact endpoint tests for the field-coordinate near box at role 2. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

theorem nearCenterBox2_numeric :
    nearCenter20Hi - focusedRadii (coordinate (2 : Owner) (0 : Fin 3)) ≤
      (nearBox2.ly : ℝ)/fieldScale-coverCap/2 ∧
    (nearBox2.hy : ℝ)/fieldScale-coverCap/2 ≤
      nearCenter20Lo + focusedRadii (coordinate (2 : Owner) (0 : Fin 3)) ∧
    nearCenter21Hi - focusedRadii (coordinate (2 : Owner) (1 : Fin 3)) ≤
      coverCap/2-(nearBox2.hx : ℝ)/fieldScale ∧
    coverCap/2-(nearBox2.lx : ℝ)/fieldScale ≤
      nearCenter21Lo + focusedRadii (coordinate (2 : Owner) (1 : Fin 3)) := by
  dsimp only [nearBox2]
  simp only [Rat.cast_divInt]
  norm_num [nearCenter20Hi, nearCenter20Lo, nearCenter21Hi,
    nearCenter21Lo, focusedRadii, coordinate, nearBox2, fieldScale, coverCap]

theorem finalNear_center_role2 (p : Point) (hp : InFinalNearCenter (2 : Fin 11) p) :
    |(fieldToLocal p).1-(constructionCenter 2).1| ≤
      focusedRadii (coordinate (2 : Owner) (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter 2).2| ≤
      focusedRadii (coordinate (2 : Owner) (1 : Fin 3)) := by
  have hbox : inRect (nearBox2.lx : ℝ) (nearBox2.hx : ℝ)
      (nearBox2.ly : ℝ) (nearBox2.hy : ℝ) p := by
    simpa [nearFieldBox] using finalNear_center_field_enclosure (2 : Fin 11) p hp
  rcases nearCenterBox2_numeric with ⟨hxl, hxr, hyl, hyr⟩
  exact ⟨field_rectangle_local_x hbox nearCenter20_bounds hxl hxr,
    field_rectangle_local_y hbox nearCenter21_bounds hyl hyr⟩

end
end ElevenSquare.Tasks.T07
