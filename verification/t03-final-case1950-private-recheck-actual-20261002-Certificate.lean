import ElevenSquare.Tasks.T03.Batch09.Case1950.Forward.Step064Trace

namespace ElevenSquare.Pending.T03.Batch09.Case1950.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step064Trace.state := Or.inl ⟨7,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 1950) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 1950) InitialState.state Step064Trace.state
    InitialState.initial Step064Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch09.Case1950.Forward.Certificate
