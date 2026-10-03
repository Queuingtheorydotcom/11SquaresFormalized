import ElevenSquare.Tasks.T07.Ext.Gen.Near.S25D
import ElevenSquare.Tasks.T07.Ext.Gen.Near.S25C0
import ElevenSquare.Simplified.U5RowBlocks
import Mathlib.Tactic.IntervalCases
import ElevenSquare.Tasks.T07.Ext.Gen.Near.S25P

namespace ElevenSquare.Tasks.T07.Ext.Near.S25
open ElevenSquare.Simplified.U5RowBlocks
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certs : List (List Sub) := [cert0, cert1, cert2, cert3, cert4, cert5, cert6]

theorem nrows : (prev.rows 8).length = 7 := by decide +kernel

theorem rows_block_0 : rowBlockB prev 8 rs pcov certs 0 8 = true := by
  decide +kernel

theorem step_ok : stepB prev 8 rs pcov certs = true := by
  apply stepB_of_row_blocks (width := 8) (blocks := 1) (by decide)
    (by rw [nrows]; rfl) (by rw [nrows]; decide)
  intro b hb
  interval_cases b
  · exact rows_block_0

theorem prune : ExtStep prev mid := stepB_sound pcov_ok step_ok

theorem promote_ok : promoteB mid 8 kern prs combs = true := by decide +kernel

theorem trace : ExtTrace prev next :=
  ExtTrace.cons prune (ExtTrace.cons (ExtStep.base (promoteB_sound promote_ok)) (ExtTrace.refl _))

end ElevenSquare.Tasks.T07.Ext.Near.S25
