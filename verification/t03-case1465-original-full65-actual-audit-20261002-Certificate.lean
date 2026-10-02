import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.Prefix012
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.ReplayBatch000Retry01
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch001
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch002
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch003
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch004
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch005
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch006
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch007
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch008
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch009
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch010
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch011
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch012
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch013
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch014
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.PartnerReplayBatch015

namespace ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Composition
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem trace : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step074State.state := by
  have h012 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step012State.state := ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Prefix012.trace
  have h013 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step013State.state := SemanticReplay.trans h012 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step013Trace.step_trace
  have h014 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step014State.state := SemanticReplay.trans h013 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step014Trace.step_trace
  have h015 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step015State.state := SemanticReplay.trans h014 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step015Trace.step_trace
  have h016 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step016State.state := SemanticReplay.trans h015 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step016Trace.step_trace
  have h017 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step017State.state := SemanticReplay.trans h016 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step017Trace.step_trace
  have h018 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step018State.state := SemanticReplay.trans h017 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step018Trace.step_trace
  have h019 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step019State.state := SemanticReplay.trans h018 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step019Trace.step_trace
  have h020 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step020State.state := SemanticReplay.trans h019 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step020Trace.step_trace
  have h021 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step021State.state := SemanticReplay.trans h020 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step021Trace.step_trace
  have h022 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step022State.state := SemanticReplay.trans h021 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step022Trace.step_trace
  have h023 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step023State.state := SemanticReplay.trans h022 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step023Trace.step_trace
  have h024 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step024State.state := SemanticReplay.trans h023 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step024Trace.step_trace
  have h025 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step025State.state := SemanticReplay.trans h024 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step025Trace.step_trace
  have h026 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step026State.state := SemanticReplay.trans h025 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step026Trace.step_trace
  have h027 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step027State.state := SemanticReplay.trans h026 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step027Trace.step_trace
  have h028 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step028State.state := SemanticReplay.trans h027 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step028Trace.step_trace
  have h029 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step029State.state := SemanticReplay.trans h028 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step029Trace.step_trace
  have h030 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step030State.state := SemanticReplay.trans h029 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step030Trace.step_trace
  have h031 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step031State.state := SemanticReplay.trans h030 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step031Trace.step_trace
  have h032 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step032State.state := SemanticReplay.trans h031 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step032Trace.step_trace
  have h033 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step033State.state := SemanticReplay.trans h032 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step033Trace.step_trace
  have h034 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step034State.state := SemanticReplay.trans h033 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step034Trace.step_trace
  have h035 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step035State.state := SemanticReplay.trans h034 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step035Trace.step_trace
  have h036 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step036State.state := SemanticReplay.trans h035 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step036Trace.step_trace
  have h037 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step037State.state := SemanticReplay.trans h036 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step037Trace.step_trace
  have h038 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step038State.state := SemanticReplay.trans h037 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step038Trace.step_trace
  have h039 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step039State.state := SemanticReplay.trans h038 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step039Trace.step_trace
  have h040 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step040State.state := SemanticReplay.trans h039 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step040Trace.step_trace
  have h041 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step041State.state := SemanticReplay.trans h040 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step041Trace.step_trace
  have h042 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step042State.state := SemanticReplay.trans h041 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step042Trace.step_trace
  have h043 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step043State.state := SemanticReplay.trans h042 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step043Trace.step_trace
  have h044 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step044State.state := SemanticReplay.trans h043 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step044Trace.step_trace
  have h045 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step045State.state := SemanticReplay.trans h044 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step045Trace.step_trace
  have h046 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step046State.state := SemanticReplay.trans h045 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step046Trace.step_trace
  have h047 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step047State.state := SemanticReplay.trans h046 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step047Trace.step_trace
  have h048 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step048State.state := SemanticReplay.trans h047 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step048Trace.step_trace
  have h049 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step049State.state := SemanticReplay.trans h048 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step049Trace.step_trace
  have h050 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step050State.state := SemanticReplay.trans h049 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step050Trace.step_trace
  have h051 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step051State.state := SemanticReplay.trans h050 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step051Trace.step_trace
  have h052 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step052State.state := SemanticReplay.trans h051 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step052Trace.step_trace
  have h053 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step053State.state := SemanticReplay.trans h052 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step053Trace.step_trace
  have h054 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step054State.state := SemanticReplay.trans h053 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step054Trace.step_trace
  have h055 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step055State.state := SemanticReplay.trans h054 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step055Trace.step_trace
  have h056 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step056State.state := SemanticReplay.trans h055 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step056Trace.step_trace
  have h057 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step057State.state := SemanticReplay.trans h056 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step057Trace.step_trace
  have h058 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step058State.state := SemanticReplay.trans h057 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step058Trace.step_trace
  have h059 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step059State.state := SemanticReplay.trans h058 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step059Trace.step_trace
  have h060 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step060State.state := SemanticReplay.trans h059 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step060Trace.step_trace
  have h061 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step061State.state := SemanticReplay.trans h060 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step061Trace.step_trace
  have h062 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step062State.state := SemanticReplay.trans h061 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step062Trace.step_trace
  have h063 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step063State.state := SemanticReplay.trans h062 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step063Trace.step_trace
  have h064 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step064State.state := SemanticReplay.trans h063 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step064Trace.step_trace
  have h065 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step065State.state := SemanticReplay.trans h064 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step065Trace.step_trace
  have h066 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step066State.state := SemanticReplay.trans h065 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step066Trace.step_trace
  have h067 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step067State.state := SemanticReplay.trans h066 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step067Trace.step_trace
  have h068 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step068State.state := SemanticReplay.trans h067 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step068Trace.step_trace
  have h069 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step069State.state := SemanticReplay.trans h068 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step069Trace.step_trace
  have h070 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step070State.state := SemanticReplay.trans h069 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step070Trace.step_trace
  have h071 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step071State.state := SemanticReplay.trans h070 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step071Trace.step_trace
  have h072 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step072State.state := SemanticReplay.trans h071 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step072Trace.step_trace
  have h073 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step073State.state := SemanticReplay.trans h072 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step073Trace.step_trace
  have h074 : SemanticReplay InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step074State.state := SemanticReplay.trans h073 ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step074Trace.step_trace
  exact h074

theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 1465) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  semantic_replay_certificate (caseMask 1465) InitialState.state ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Step074State.state
    InitialState.initial trace ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.terminal_snapshot

end
end ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Composition

namespace ElevenSquare.Pending.T03.Batch04.Case1465.Forward.Certificate
noncomputable section
theorem certificate_exists : ∃ a b : PoseState,
    (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask 1465) →
      ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
    VerifiedTrace a b ∧ Terminal b :=
  ElevenSquare.Pending.T03.Batch04.Case1465.Forward.IndependentReplay.Composition.certificate_exists
end
end ElevenSquare.Pending.T03.Batch04.Case1465.Forward.Certificate
