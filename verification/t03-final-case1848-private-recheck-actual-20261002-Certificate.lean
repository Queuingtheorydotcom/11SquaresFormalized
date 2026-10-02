import ElevenSquare.Tasks.T03.Batch09.Case1848.Forward.Step119Trace

namespace ElevenSquare.Pending.T03.Batch09.Case1848.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step119Trace.state := Or.inl ⟨7,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 1848) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 1848) InitialState.state Step119Trace.state
    InitialState.initial Step119Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch09.Case1848.Forward.Certificate
