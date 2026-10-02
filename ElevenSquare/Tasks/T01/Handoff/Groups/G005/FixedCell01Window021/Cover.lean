import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window021.CoverLeaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window021.CoverLeaf002

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window021
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-15855/16913), (-5888/16913), (-8057250220150911949837240113418397149730797/4677264374249740000000000000000000000000000)⟩ :: nodeSource000 = nodeSource002 := by
    norm_num [baselineFlip, nodeSource000, nodeSource002]
  change node002.Check (baselineFlip ⟨(-15855/16913), (-5888/16913), (-8057250220150911949837240113418397149730797/4677264374249740000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node002_checked

theorem cover_checked : node000.Check source targets := by
  simpa only [nodeSource000, source] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window021
