import ElevenSquare.Tasks.T07.Ext.Compose
import ElevenSquare.Tasks.T07.Ext.Gen.Far15
import ElevenSquare.Tasks.T07.Ext.Gen.Far13
import ElevenSquare.Tasks.T07.Ext.Gen.R110
import ElevenSquare.Tasks.T07.Ext.Gen.NearConn
import ElevenSquare.Tasks.T07.ConditionalGlobal

/-! The case-438 near certificate from the generated extended traces.

The phase-2 chain runs from the closed-cell seed `siteSeedFor roleCell` to the
root of the capture tree; the root trace is followed by the three closed cuts of
`ext_near_of_far`, whose far branches end in terminal states.  The final near
state is enclosed row by row in the frozen near packet. -/
namespace ElevenSquare.Tasks.T07.Ext
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07

theorem role_near_box_certificate : RoleNearBoxCertificate := by
  intro S Q _ _ hrole hchart
  have hseed : StateHolds Q (siteSeedFor roleCell) := siteSeedFor_holds Q roleCell hchart hrole
  have hR : StateHolds Q Root240.final :=
    ext_trace_sound Q (ext_trace_sound Q hseed P2.trace) Root240.trace
  have hN : StateHolds Q Near.final :=
    ext_near_of_far hchart 1 10 6 hR Far15.trace Far15.terminal R1.trace
      (R10.trace.trans Far13.trace) Far13.terminal (Near13.trace.trans R11.trace)
      R110.trace R110.terminal (R111.trace.trans Near.trace)
  exact stateHolds_nearOuterState_of_subsumed Q _ hN NearConn.subsumed

theorem case438_near_certificate' : Case438NearCertificate :=
  role_near_box_to_case438_certificate role_near_box_certificate

end ElevenSquare.Tasks.T07.Ext
