import ElevenSquare.Tasks.T07.Ext.Compose
import ElevenSquare.Tasks.T07.Ext.Gen.Far15
import ElevenSquare.Tasks.T07.Ext.Gen.Far13
import ElevenSquare.Tasks.T07.Ext.Gen.R110
import ElevenSquare.Tasks.T07.Ext.Gen.NearConn

/-! The case-438 near state from the generated extended traces.

The phase-2 chain runs from the closed-cell seed `siteSeedFor roleCell` to the
root of the capture tree; the root trace is followed by the three closed cuts of
`ext_near_of_far`, whose far branches end in terminal states.  The final near
state is enclosed row by row in the frozen near packet.  `extNearOuterState` is a
copy of `nearOuterState`; this is the body of `RoleNearBoxCertificate` (see
`Case438Global`). -/
namespace ElevenSquare.Tasks.T07.Ext
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07

theorem role_near_box_state (Q : Packing 11 coverCap)
    (hrole : ∀ i, ClosedCell (roleCell i) (normalizeCenter (Q.squares i).center))
    (hchart : IsCharted Q) : StateHolds Q extNearOuterState := by
  have hseed : StateHolds Q (siteSeedFor roleCell) := siteSeedFor_holds Q roleCell hchart hrole
  have hR : StateHolds Q Root240.final :=
    ext_trace_sound Q (ext_trace_sound Q hseed P2.trace) Root240.trace
  have hN : StateHolds Q Near.final :=
    ext_near_of_far hchart 1 10 6 hR Far15.trace Far15.terminal R1.trace
      (R10.trace.trans Far13.trace) Far13.terminal (Near13.trace.trans R11.trace)
      R110.trace R110.terminal (R111.trace.trans Near.trace)
  exact stateHolds_extNearOuterState Q _ hN NearConn.subsumed

end ElevenSquare.Tasks.T07.Ext
