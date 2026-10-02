import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window004.CoverLeaf002
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window004.CoverLeaf003
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window004.CoverLeaf004

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window004
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(387708359002281417731/5000000000000000000000), (-320893285263457706409451472577/3820000000000000000000000000000), (29122786810024492407512790478093474894034327362111570306273069/197456540422960000000000000000000000000000000000000000000000000)⟩ :: nodeSource001 = nodeSource003 := by
    norm_num [baselineFlip, nodeSource001, nodeSource003]
  change node003.Check (baselineFlip ⟨(387708359002281417731/5000000000000000000000), (-320893285263457706409451472577/3820000000000000000000000000000), (29122786810024492407512790478093474894034327362111570306273069/197456540422960000000000000000000000000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node003_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(15543/17225), (7424/17225), (3357343810836307493739607459130567054505397/1234103377643500000000000000000000000000000)⟩ :: nodeSource000 = nodeSource004 := by
    norm_num [baselineFlip, nodeSource000, nodeSource004]
  change node004.Check (baselineFlip ⟨(15543/17225), (7424/17225), (3357343810836307493739607459130567054505397/1234103377643500000000000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node004_checked

theorem cover_checked : node000.Check source targets := by
  simpa only [nodeSource000, source] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell02Window004
