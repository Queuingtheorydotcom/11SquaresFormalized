import ElevenSquare.Tasks.T03.Batch10.Case2048.Forward.Step144Trace

namespace ElevenSquare.Pending.T03.Batch10.Case2048.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step144Trace.state := Or.inl ⟨5,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 2048) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 2048) InitialState.state Step144Trace.state
    InitialState.initial Step144Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch10.Case2048.Forward.Certificate
