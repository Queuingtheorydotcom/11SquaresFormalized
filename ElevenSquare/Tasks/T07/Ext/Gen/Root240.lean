import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S0
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S1
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S2
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S3
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S4
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S5
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S6
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S7
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S8
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S9
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S10
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S11
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S12
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S13
import ElevenSquare.Tasks.T07.CaptureTraceCombinators

namespace ElevenSquare.Tasks.T07.Ext.Root240
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def final : PoseState := S13.next

theorem trace : ExtTrace st0 final := by
  exact (ExtTrace.trans S0.trace (ExtTrace.trans S1.trace (ExtTrace.trans S2.trace (ExtTrace.trans S3.trace (ExtTrace.trans S4.trace (ExtTrace.trans S5.trace (ExtTrace.trans S6.trace (ExtTrace.trans S7.trace (ExtTrace.trans S8.trace (ExtTrace.trans S9.trace (ExtTrace.trans S10.trace (ExtTrace.trans S11.trace (ExtTrace.trans S12.trace S13.trace)))))))))))))

end ElevenSquare.Tasks.T07.Ext.Root240
