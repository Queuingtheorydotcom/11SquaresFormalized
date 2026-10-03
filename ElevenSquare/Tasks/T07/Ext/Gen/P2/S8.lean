import ElevenSquare.Tasks.T07.Ext.Gen.P2.S8D
import ElevenSquare.Tasks.T07.Ext.Gen.P2.S8C0
import ElevenSquare.Simplified.U5RowBlocks
import Mathlib.Tactic.IntervalCases
import ElevenSquare.Tasks.T07.Ext.Gen.P2.S8P

namespace ElevenSquare.Tasks.T07.Ext.P2.S8
open ElevenSquare.Simplified.U5RowBlocks
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certs : List (List Sub) := [cert0]

theorem nrows : (prev.rows 7).length = 1 := by decide +kernel

theorem step_ok : stepB prev 7 rs pcov certs = true := by
  apply stepB_of_row_blocks (width := 8) (blocks := 1) (by decide)
    (by rw [nrows]; rfl) (by rw [nrows]; decide)
  intro b hb
  interval_cases b <;> decide +kernel

theorem prune : ExtStep prev mid := stepB_sound pcov_ok step_ok

theorem promote_ok : promoteB mid 7 kern prs combs = true := by decide +kernel

theorem trace : ExtTrace prev next :=
  ExtTrace.cons prune (ExtTrace.cons (ExtStep.base (promoteB_sound promote_ok)) (ExtTrace.refl _))

end ElevenSquare.Tasks.T07.Ext.P2.S8
