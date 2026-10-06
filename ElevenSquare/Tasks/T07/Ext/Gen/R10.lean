import ElevenSquare.Tasks.T07.Ext.Gen.R10.S0
import ElevenSquare.Tasks.T07.Ext.Gen.R10.S1
import ElevenSquare.Tasks.T07.Ext.Gen.R10.S2
import ElevenSquare.Tasks.T07.Ext.Gen.R10.S3
import ElevenSquare.Tasks.T07.Ext.Gen.R10.S4
import ElevenSquare.Tasks.T07.Ext.Gen.R10.S5
import ElevenSquare.Tasks.T07.Ext.Gen.R10.S6
import ElevenSquare.Tasks.T07.Ext.Gen.R10.S7
import ElevenSquare.Tasks.T07.Ext.Gen.R10.S8
import ElevenSquare.Tasks.T07.Ext.Gen.R10.S9
import ElevenSquare.Tasks.T07.Ext.Gen.R10.S10
import ElevenSquare.Tasks.T07.Ext.Gen.R10.S11
import ElevenSquare.Tasks.T07.Ext.Gen.R10.S12
import ElevenSquare.Tasks.T07.CaptureTraceCombinators

namespace ElevenSquare.Tasks.T07.Ext.R10
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def final : PoseState := S12.next

theorem trace : ExtTrace st0 final := by
  exact (ExtTrace.trans S0.trace (ExtTrace.trans S1.trace (ExtTrace.trans S2.trace (ExtTrace.trans S3.trace (ExtTrace.trans S4.trace (ExtTrace.trans S5.trace (ExtTrace.trans S6.trace (ExtTrace.trans S7.trace (ExtTrace.trans S8.trace (ExtTrace.trans S9.trace (ExtTrace.trans S10.trace (ExtTrace.trans S11.trace S12.trace))))))))))))

end ElevenSquare.Tasks.T07.Ext.R10
