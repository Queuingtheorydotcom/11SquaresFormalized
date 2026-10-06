import Lean

/-! Bounded kernel regression for the T07 row-block coverage side conditions.

Make order reflexivity available to `rw`, as in the production imports. When
the rows exactly fill the blocks, `rw [nrows]` closes the goal; an unconditional
following `decide` would fail with `No goals to be solved`.
-/
attribute [refl] Nat.le_refl

namespace T07RowBlockCover

theorem full_block {α : Type} (rows : List α) (nrows : rows.length = 104) :
    rows.length ≤ 13 * 8 := by
  rw [nrows] <;> decide

-- The unchanged strict-bound proof still has an arithmetic goal after rewriting.
theorem partial_block {α : Type} (rows : List α) (nrows : rows.length = 103) :
    rows.length ≤ 13 * 8 := by
  rw [nrows]; decide

theorem exact_blocks {α : Type} (rows : List α) (blocks width : Nat)
    (nrows : rows.length = blocks * width) : rows.length ≤ blocks * width := by
  rw [nrows] <;> decide

#print axioms full_block
#print axioms partial_block
#print axioms exact_blocks

end T07RowBlockCover
