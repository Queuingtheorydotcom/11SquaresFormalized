import ElevenSquare.Tasks.T03.Batch12.Case2125.Forward.Step118Trace

namespace ElevenSquare.Pending.T03.Batch12.Case2125.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step118Trace.state := Or.inl ⟨9,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 2125) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 2125) InitialState.state Step118Trace.state
    InitialState.initial Step118Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch12.Case2125.Forward.Certificate
