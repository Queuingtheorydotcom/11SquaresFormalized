import ElevenSquare.Tasks.T03.Batch09.Case1889.Forward.Step076Trace

namespace ElevenSquare.Pending.T03.Batch09.Case1889.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step076Trace.state := Or.inl ⟨4,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 1889) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 1889) InitialState.state Step076Trace.state
    InitialState.initial Step076Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch09.Case1889.Forward.Certificate
