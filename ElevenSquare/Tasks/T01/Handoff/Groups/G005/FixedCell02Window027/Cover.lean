import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window027.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window027.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window027.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window027
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(13056/18985), (-13783/18985), (643792794149243470563741777022250387647/538887854520312500000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(13056/18985), (-13783/18985), (643792794149243470563741777022250387647/538887854520312500000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(13783/18985), (13056/18985), (22416998014980918413849752876562223/8622205672325000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(13783/18985), (13056/18985), (22416998014980918413849752876562223/8622205672325000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa only [nodeSource000, source] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window027
