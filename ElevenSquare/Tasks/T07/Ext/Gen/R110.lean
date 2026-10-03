import ElevenSquare.Tasks.T07.Ext.Gen.R110.S0
import ElevenSquare.Tasks.T07.Ext.Gen.R110.S1
import ElevenSquare.Tasks.T07.Ext.Gen.R110.S2
import ElevenSquare.Tasks.T07.Ext.Gen.R110.S3
import ElevenSquare.Tasks.T07.Ext.Gen.R110.S4
import ElevenSquare.Tasks.T07.Ext.Gen.R110.S5
import ElevenSquare.Tasks.T07.Ext.Gen.R110.S6
import ElevenSquare.Tasks.T07.Ext.Gen.R110.S7
import ElevenSquare.Tasks.T07.Ext.Gen.R110.S8
import ElevenSquare.Tasks.T07.Ext.Gen.R110.S9
import ElevenSquare.Tasks.T07.Ext.Gen.R110.S10
import ElevenSquare.Tasks.T07.CaptureTraceCombinators

namespace ElevenSquare.Tasks.T07.Ext.R110
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def final : PoseState := S10.next

theorem trace : ExtTrace st0 final := by
  exact (ExtTrace.trans S0.trace (ExtTrace.trans S1.trace (ExtTrace.trans S2.trace (ExtTrace.trans S3.trace (ExtTrace.trans S4.trace (ExtTrace.trans S5.trace (ExtTrace.trans S6.trace (ExtTrace.trans S7.trace (ExtTrace.trans S8.trace (ExtTrace.trans S9.trace S10.trace))))))))))

theorem terminal : Terminal final :=
  terminal_of_empty_owner _ 2 (by simp [final, S10.next, S10.mid, replaceRows, S10.rs])

end ElevenSquare.Tasks.T07.Ext.R110
