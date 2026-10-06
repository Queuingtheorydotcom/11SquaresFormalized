import ElevenSquare.Tasks.T07.Ext.Gen.Far15.S0
import ElevenSquare.Tasks.T07.Ext.Gen.Far15.S1
import ElevenSquare.Tasks.T07.Ext.Gen.Far15.S2
import ElevenSquare.Tasks.T07.Ext.Gen.Far15.S3
import ElevenSquare.Tasks.T07.Ext.Gen.Far15.S4
import ElevenSquare.Tasks.T07.Ext.Gen.Far15.S5
import ElevenSquare.Tasks.T07.Ext.Gen.Far15.S6
import ElevenSquare.Tasks.T07.Ext.Gen.Far15.S7
import ElevenSquare.Tasks.T07.CaptureTraceCombinators

namespace ElevenSquare.Tasks.T07.Ext.Far15
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def final : PoseState := S7.next

theorem trace : ExtTrace st0 final := by
  exact (ExtTrace.trans S0.trace (ExtTrace.trans S1.trace (ExtTrace.trans S2.trace (ExtTrace.trans S3.trace (ExtTrace.trans S4.trace (ExtTrace.trans S5.trace (ExtTrace.trans S6.trace S7.trace)))))))

theorem terminal : Terminal final :=
  terminal_of_empty_owner _ 2 (by simp [final, S7.next, S7.mid, replaceRows, S7.rs])

end ElevenSquare.Tasks.T07.Ext.Far15
