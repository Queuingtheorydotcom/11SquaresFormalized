import ElevenSquare.Tasks.T03.Batch10.Case2049.Forward.Step048Trace

namespace ElevenSquare.Pending.T03.Batch10.Case2049.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step048Trace.state := Or.inl ⟨3,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 2049) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 2049) InitialState.state Step048Trace.state
    InitialState.initial Step048Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch10.Case2049.Forward.Certificate
