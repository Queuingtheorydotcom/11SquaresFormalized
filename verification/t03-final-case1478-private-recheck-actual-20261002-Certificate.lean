import ElevenSquare.Tasks.T03.Batch04.Case1478.Forward.Step046Trace

namespace ElevenSquare.Pending.T03.Batch04.Case1478.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step046Trace.state := Or.inl ⟨10,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 1478) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 1478) InitialState.state Step046Trace.state
    InitialState.initial Step046Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch04.Case1478.Forward.Certificate
