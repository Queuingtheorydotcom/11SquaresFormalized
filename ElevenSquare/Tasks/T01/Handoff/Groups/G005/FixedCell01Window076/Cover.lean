import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window076.CoverLeaf001
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window076.CoverLeaf002

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window076
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-28928/29153), (3615/29153), (-101719099421786400547158484642546310259629/74017296967292000000000000000000000000000)⟩ :: nodeSource000 = nodeSource002 := by
    norm_num [baselineFlip, nodeSource000, nodeSource002]
  change node002.Check (baselineFlip ⟨(-28928/29153), (3615/29153), (-101719099421786400547158484642546310259629/74017296967292000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node002_checked

theorem cover_checked : node000.Check source targets := by
  simpa only [nodeSource000, source] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window076
