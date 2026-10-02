import ElevenSquare.Tasks.T03.Batch10.Case2047.Forward.Step222Trace

namespace ElevenSquare.Pending.T03.Batch10.Case2047.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step222Trace.state := Or.inl ⟨7,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 2047) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 2047) InitialState.state Step222Trace.state
    InitialState.initial Step222Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch10.Case2047.Forward.Certificate
