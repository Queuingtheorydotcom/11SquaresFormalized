import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window030.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window030.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window030.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window030
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(3712/4937), (-3255/4937), (628951866133797537767748336008378590367/455139819149687500000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(3712/4937), (-3255/4937), (628951866133797537767748336008378590367/455139819149687500000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(3255/4937), (3712/4937), (95664740332943650997045405653199/38126895845000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(3255/4937), (3712/4937), (95664740332943650997045405653199/38126895845000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa only [nodeSource000, source] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window030
