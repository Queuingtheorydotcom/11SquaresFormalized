import ElevenSquare.Tasks.T07.Ext.Gen.R111.S0
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S1
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S2
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S3
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S4
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S5
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S6
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S7
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S8
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S9
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S10
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S11
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S12
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S13
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S14
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S15
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S16
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S17
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S18
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S19
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S20
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S21
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S22
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S23
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S24
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S25
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S26
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S27
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S28
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S29
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S30
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S31
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S32
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S33
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S34
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S35
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S36
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S37
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S38
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S39
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S40
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S41
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S42
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S43
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S44
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S45
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S46
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S47
import ElevenSquare.Tasks.T07.CaptureTraceCombinators

namespace ElevenSquare.Tasks.T07.Ext.R111
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def final : PoseState := S47.next

theorem trace : ExtTrace st0 final := by
  exact (ExtTrace.trans S0.trace (ExtTrace.trans S1.trace (ExtTrace.trans S2.trace (ExtTrace.trans S3.trace (ExtTrace.trans S4.trace (ExtTrace.trans S5.trace (ExtTrace.trans S6.trace (ExtTrace.trans S7.trace (ExtTrace.trans S8.trace (ExtTrace.trans S9.trace (ExtTrace.trans S10.trace (ExtTrace.trans S11.trace (ExtTrace.trans S12.trace (ExtTrace.trans S13.trace (ExtTrace.trans S14.trace (ExtTrace.trans S15.trace (ExtTrace.trans S16.trace (ExtTrace.trans S17.trace (ExtTrace.trans S18.trace (ExtTrace.trans S19.trace (ExtTrace.trans S20.trace (ExtTrace.trans S21.trace (ExtTrace.trans S22.trace (ExtTrace.trans S23.trace (ExtTrace.trans S24.trace (ExtTrace.trans S25.trace (ExtTrace.trans S26.trace (ExtTrace.trans S27.trace (ExtTrace.trans S28.trace (ExtTrace.trans S29.trace (ExtTrace.trans S30.trace (ExtTrace.trans S31.trace (ExtTrace.trans S32.trace (ExtTrace.trans S33.trace (ExtTrace.trans S34.trace (ExtTrace.trans S35.trace (ExtTrace.trans S36.trace (ExtTrace.trans S37.trace (ExtTrace.trans S38.trace (ExtTrace.trans S39.trace (ExtTrace.trans S40.trace (ExtTrace.trans S41.trace (ExtTrace.trans S42.trace (ExtTrace.trans S43.trace (ExtTrace.trans S44.trace (ExtTrace.trans S45.trace (ExtTrace.trans S46.trace S47.trace)))))))))))))))))))))))))))))))))))))))))))))))

end ElevenSquare.Tasks.T07.Ext.R111
