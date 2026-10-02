import ElevenSquare.Tasks.T03.Batch08.Case1775.Forward.Step264Trace

namespace ElevenSquare.Pending.T03.Batch08.Case1775.Forward.Certificate
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem terminal : Terminal Step264Trace.state := Or.inl ⟨3,by rfl⟩
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 1775) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 1775) InitialState.state Step264Trace.state
    InitialState.initial Step264Trace.trace terminal

end
end ElevenSquare.Pending.T03.Batch08.Case1775.Forward.Certificate
