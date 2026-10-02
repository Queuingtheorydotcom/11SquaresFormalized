import ElevenSquare.Tasks.T03.Batch09.Case1885.Forward.Step158Trace

namespace ElevenSquare.Pending.T03.Batch09.Case1885.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step158Trace.state := Or.inl ⟨4,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 1885) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 1885) InitialState.state Step158Trace.state
    InitialState.initial Step158Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch09.Case1885.Forward.Certificate
