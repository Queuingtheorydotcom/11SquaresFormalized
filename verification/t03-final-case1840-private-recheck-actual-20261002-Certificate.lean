import ElevenSquare.Tasks.T03.Batch08.Case1840.Forward.Step130Trace

namespace ElevenSquare.Pending.T03.Batch08.Case1840.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step130Trace.state := Or.inl ⟨10,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 1840) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 1840) InitialState.state Step130Trace.state
    InitialState.initial Step130Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch08.Case1840.Forward.Certificate
