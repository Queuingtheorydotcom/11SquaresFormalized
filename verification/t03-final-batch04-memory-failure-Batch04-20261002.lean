import ElevenSquare.Tasks.T03.Assembly.Types
import ElevenSquare.Tasks.T03.Batch04.Case1433.Forward.Certificate
import ElevenSquare.Tasks.T03.Batch04.Case1436.Forward.Certificate
import ElevenSquare.Tasks.T03.Batch04.Case1437.Forward.Certificate
import ElevenSquare.Tasks.T03.Batch04.Case1438.Forward.Certificate
import ElevenSquare.Tasks.T03.Batch04.Case1439.Forward.Certificate
import ElevenSquare.Tasks.T03.Batch04.Case1441.Forward.Certificate
import ElevenSquare.Tasks.T03.Batch04.Case1449.Forward.Certificate
import ElevenSquare.Tasks.T03.Batch04.Case1450.Forward.Certificate
import ElevenSquare.Tasks.T03.Wand125.PrunedTrees.C1463.Certificate
import ElevenSquare.Tasks.T03.Wand125.ReboundPrunedTrees.C1464.Certificate
import ElevenSquare.Tasks.T03.Batch04.Case1465.IndependentReplay.Certificate
import ElevenSquare.Tasks.T03.Batch04.Case1467.Forward.Certificate
import ElevenSquare.Tasks.T03.Batch04.Case1476.Forward.Certificate
import ElevenSquare.Tasks.T03.Batch04.Case1478.Forward.Certificate
import ElevenSquare.Tasks.T03.Batch04.Case1484.Forward.Certificate

namespace ElevenSquare.Pending.T03.Assembly
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace Batch04
def indices : List (Fin 2184) := [1433,1436,1437,1438,1439,1441,1449,1450,1463,1464,1465,1467,1476,1478,1484]
theorem certificates (k : Fin 2184) (hk : k ∈ indices) : CaseCertificate k := by
  simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ElevenSquare.Pending.T03.Batch04.Case1433.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1436.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1437.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1438.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1439.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1441.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1449.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1450.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1463.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1464.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1465.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1467.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1476.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1478.Forward.Certificate.certificate_exists
  · exact ElevenSquare.Pending.T03.Batch04.Case1484.Forward.Certificate.certificate_exists
end Batch04
end
end ElevenSquare.Pending.T03.Assembly
