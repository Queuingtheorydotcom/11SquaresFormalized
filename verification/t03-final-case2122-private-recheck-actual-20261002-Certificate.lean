import ElevenSquare.Tasks.T03.Batch12.Case2122.Forward.Step352Trace

namespace ElevenSquare.Pending.T03.Batch12.Case2122.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step352Trace.state := Or.inl ⟨3,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 2122) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 2122) InitialState.state Step352Trace.state
    InitialState.initial Step352Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch12.Case2122.Forward.Certificate
