import ElevenSquare.Tasks.T03.Batch04.Case1476.Forward.Step051Trace

namespace ElevenSquare.Pending.T03.Batch04.Case1476.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step051Trace.state := Or.inl ⟨10,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 1476) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 1476) InitialState.state Step051Trace.state
    InitialState.initial Step051Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch04.Case1476.Forward.Certificate
