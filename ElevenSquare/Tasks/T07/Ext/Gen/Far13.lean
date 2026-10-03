import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S0
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S1
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S2
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S3
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S4
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S5
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S6
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S7
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S8
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S9
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S10
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S11
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S12
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S13
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S14
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S15
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S16
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S17
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S18
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S19
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S20
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S21
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S22
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S23
import ElevenSquare.Tasks.T07.CaptureTraceCombinators

namespace ElevenSquare.Tasks.T07.Ext.Far13
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def final : PoseState := S23.next

theorem trace : ExtTrace st0 final := by
  exact (ExtTrace.trans S0.trace (ExtTrace.trans S1.trace (ExtTrace.trans S2.trace (ExtTrace.trans S3.trace (ExtTrace.trans S4.trace (ExtTrace.trans S5.trace (ExtTrace.trans S6.trace (ExtTrace.trans S7.trace (ExtTrace.trans S8.trace (ExtTrace.trans S9.trace (ExtTrace.trans S10.trace (ExtTrace.trans S11.trace (ExtTrace.trans S12.trace (ExtTrace.trans S13.trace (ExtTrace.trans S14.trace (ExtTrace.trans S15.trace (ExtTrace.trans S16.trace (ExtTrace.trans S17.trace (ExtTrace.trans S18.trace (ExtTrace.trans S19.trace (ExtTrace.trans S20.trace (ExtTrace.trans S21.trace (ExtTrace.trans S22.trace S23.trace)))))))))))))))))))))))

theorem terminal : Terminal final :=
  terminal_of_empty_owner _ 9 (by simp [final, S23.next, S23.mid, replaceRows, S23.rs])

end ElevenSquare.Tasks.T07.Ext.Far13
