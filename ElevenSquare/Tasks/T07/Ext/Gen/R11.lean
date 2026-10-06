import ElevenSquare.Tasks.T07.Ext.Gen.R11.S0
import ElevenSquare.Tasks.T07.Ext.Gen.R11.S1
import ElevenSquare.Tasks.T07.Ext.Gen.R11.S2
import ElevenSquare.Tasks.T07.Ext.Gen.R11.S3
import ElevenSquare.Tasks.T07.Ext.Gen.R11.S4
import ElevenSquare.Tasks.T07.Ext.Gen.R11.S5
import ElevenSquare.Tasks.T07.Ext.Gen.R11.S6
import ElevenSquare.Tasks.T07.CaptureTraceCombinators

namespace ElevenSquare.Tasks.T07.Ext.R11
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def final : PoseState := S6.next

theorem trace : ExtTrace st0 final := by
  exact (ExtTrace.trans S0.trace (ExtTrace.trans S1.trace (ExtTrace.trans S2.trace (ExtTrace.trans S3.trace (ExtTrace.trans S4.trace (ExtTrace.trans S5.trace S6.trace))))))

end ElevenSquare.Tasks.T07.Ext.R11
