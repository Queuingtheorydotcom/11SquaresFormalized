import ElevenSquare.Tasks.T07.CoordinateBridge

/-! The exact closed decision tree. The first cut is in centered physical
unit coordinates, not normalized coordinates and not scaled field coordinates. -/
namespace ElevenSquare.Tasks.T07
noncomputable section

def Far15 (y15 : ℝ) : Prop := y15 ≤ 5/4

def Far13 (y15 t13 : ℝ) : Prop := 5/4 ≤ y15 ∧ t13 ≤ 147/512

def Far2 (y15 t13 t2 : ℝ) : Prop :=
  5/4 ≤ y15 ∧ 147/512 ≤ t13 ∧ t2 ≤ 183/512

def Near (y15 t13 t2 : ℝ) : Prop :=
  5/4 ≤ y15 ∧ 147/512 ≤ t13 ∧ 183/512 ≤ t2

theorem capture_closed_partition (y15 t13 t2 : ℝ) :
    Far15 y15 ∨ Far13 y15 t13 ∨ Far2 y15 t13 t2 ∨ Near y15 t13 t2 := by
  rcases le_total y15 (5/4) with hy | hy
  · exact Or.inl hy
  · rcases le_total t13 (147/512) with h13 | h13
    · exact Or.inr (Or.inl ⟨hy, h13⟩)
    · rcases le_total t2 (183/512) with h2 | h2
      · exact Or.inr (Or.inr (Or.inl ⟨hy, h13, h2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hy, h13, h2⟩))

theorem near_of_far_exclusions {y15 t13 t2 : ℝ}
    (h15 : ¬ Far15 y15) (h13 : ¬ Far13 y15 t13) (h2 : ¬ Far2 y15 t13 t2) :
    Near y15 t13 t2 := by
  rcases capture_closed_partition y15 t13 t2 with h | h | h | h
  · exact (h15 h).elim
  · exact (h13 h).elim
  · exact (h2 h).elim
  · exact h

/-- Equality at a cut is retained on both adjoining closed branches. -/
theorem capture_boundary_retained :
    Far15 (5/4) ∧ Far13 (5/4) (147/512) ∧
      Far2 (5/4) (147/512) (183/512) ∧ Near (5/4) (147/512) (183/512) := by
  norm_num [Far15, Far13, Far2, Near]

def centeredFieldY (y : ℝ) : ℝ := y/fieldScale-coverCap/2

theorem field_y15_le_cut (y : ℝ) :
    centeredFieldY y ≤ 5/4 ↔ y ≤ fieldScale*(coverCap/2+5/4) := by
  unfold centeredFieldY
  rw [sub_le_iff_le_add, div_le_iff₀ fieldScale_pos]
  constructor <;> intro h <;> nlinarith

theorem field_y15_ge_cut (y : ℝ) :
    5/4 ≤ centeredFieldY y ↔ fieldScale*(coverCap/2+5/4) ≤ y := by
  unfold centeredFieldY
  rw [le_sub_iff_add_le, le_div_iff₀ fieldScale_pos]
  constructor <;> intro h <;> nlinarith

/-- A rational check of the exact first-cut coefficient in the packaged trace. -/
theorem recorded_y15_field_cut :
    fieldScale*(coverCap/2+5/4) =
      (121802296569435750786621 : ℝ)/38770835900228141773100 := by
  norm_num [fieldScale, coverCap]

/-- The normalized cover ordinate corresponding to centered physical height
`5/4`; unlike `5/4` itself, it is strictly below one. -/
def normalizedY15Cut : ℝ := (coverCap/2+5/4-1/2)/(coverCap-1)

theorem normalized_y15_cut_lt_one : normalizedY15Cut < 1 := by
  norm_num [normalizedY15Cut, coverCap]

theorem normalized_y15_cut_correct (y : ℝ) :
    y-coverCap/2 ≤ 5/4 ↔ (y-1/2)/(coverCap-1) ≤ normalizedY15Cut := by
  have hpos : 0 < coverCap-1 := by norm_num [coverCap]
  unfold normalizedY15Cut
  rw [div_le_div_iff₀ hpos hpos]
  constructor <;> intro h <;> nlinarith

end
end ElevenSquare.Tasks.T07
