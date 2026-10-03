import ElevenSquare.Tasks.T07.Ext.Gen.P2.S76D
import ElevenSquare.Tasks.T07.Ext.Gen.P2.S76C0
import ElevenSquare.Tasks.T07.Ext.Gen.P2.S76C1
import ElevenSquare.Simplified.U5RowBlocks
import Mathlib.Tactic.IntervalCases
import ElevenSquare.Tasks.T07.Ext.Gen.P2.S76P

namespace ElevenSquare.Tasks.T07.Ext.P2.S76
open ElevenSquare.Simplified.U5RowBlocks
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certs : List (List Sub) := [cert0, cert1, cert2, cert3, cert4, cert5, cert6, cert7, cert8, cert9, cert10, cert11, cert12, cert13, cert14, cert15, cert16, cert17, cert18, cert19, cert20, cert21, cert22, cert23, cert24, cert25, cert26, cert27, cert28, cert29, cert30, cert31, cert32, cert33, cert34, cert35, cert36, cert37, cert38, cert39, cert40, cert41, cert42, cert43, cert44, cert45, cert46, cert47, cert48, cert49, cert50, cert51, cert52, cert53]

theorem nrows : (prev.rows 1).length = 54 := by decide +kernel

theorem rows_block_0 : rowBlockB prev 1 rs pcov certs 0 8 = true := by
  decide +kernel

theorem rows_block_1 : rowBlockB prev 1 rs pcov certs 8 8 = true := by
  decide +kernel

theorem rows_block_2 : rowBlockB prev 1 rs pcov certs 16 8 = true := by
  decide +kernel

theorem rows_block_3 : rowBlockB prev 1 rs pcov certs 24 8 = true := by
  decide +kernel

theorem rows_block_4 : rowBlockB prev 1 rs pcov certs 32 8 = true := by
  decide +kernel

theorem rows_block_5 : rowBlockB prev 1 rs pcov certs 40 8 = true := by
  decide +kernel

theorem rows_block_6 : rowBlockB prev 1 rs pcov certs 48 8 = true := by
  decide +kernel

theorem step_ok : stepB prev 1 rs pcov certs = true := by
  apply stepB_of_row_blocks (width := 8) (blocks := 7) (by decide)
    (by rw [nrows]; rfl) (by rw [nrows]; decide)
  intro b hb
  interval_cases b
  · exact rows_block_0
  · exact rows_block_1
  · exact rows_block_2
  · exact rows_block_3
  · exact rows_block_4
  · exact rows_block_5
  · exact rows_block_6

theorem prune : ExtStep prev mid := stepB_sound pcov_ok step_ok

theorem promote_ok : promoteB mid 1 kern prs combs = true := by decide +kernel

theorem trace : ExtTrace prev next :=
  ExtTrace.cons prune (ExtTrace.cons (ExtStep.base (promoteB_sound promote_ok)) (ExtTrace.refl _))

end ElevenSquare.Tasks.T07.Ext.P2.S76
