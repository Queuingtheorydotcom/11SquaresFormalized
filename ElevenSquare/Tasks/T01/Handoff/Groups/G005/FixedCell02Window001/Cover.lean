import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window001.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window001.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window001.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window001
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(92726068460142313087578812611/955000000000000000000000000000), (2489668839624791121678198769/764000000000000000000000000000), (211346275009504426927348616472457953917792918699284522317050720919521/848509585678160000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(92726068460142313087578812611/955000000000000000000000000000), (2489668839624791121678198769/764000000000000000000000000000), (211346275009504426927348616472457953917792918699284522317050720919521/848509585678160000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(1015/1033), (192/1033), (2904619914101856979243959487220866560293/1110614640940000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(1015/1033), (192/1033), (2904619914101856979243959487220866560293/1110614640940000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa only [nodeSource000, source] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window001
