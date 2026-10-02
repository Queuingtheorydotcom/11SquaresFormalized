import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window066.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window066.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window066.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window066.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window066.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window066
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(-387708359002281417731/4000000000000000000000), (-271525087292028299883516527423/3820000000000000000000000000000), (-157705842442229676640120926090887089057896317325015644465178583/853556322207100000000000000000000000000000000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(-387708359002281417731/4000000000000000000000), (-271525087292028299883516527423/3820000000000000000000000000000), (-157705842442229676640120926090887089057896317325015644465178583/853556322207100000000000000000000000000000000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(-197472790722592549096895527423/3820000000000000000000000000000), (98736395555150454049588472577/3820000000000000000000000000000), (-33513635099180688308761197792325553813934662408012991249445859082399351/652117030166224400000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource002, nodeSource006]
  change node006.Check (baselineFlip ⟨(-197472790722592549096895527423/3820000000000000000000000000000), (98736395555150454049588472577/3820000000000000000000000000000), (-33513635099180688308761197792325553813934662408012991249445859082399351/652117030166224400000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-4992/5617), (2575/5617), (-2328958228482289326606995263276946037083/2667363506897187500000000000000000000000)⟩ :: nodeSource001 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource001, nodeSource007]
  change node007.Check (baselineFlip ⟨(-4992/5617), (2575/5617), (-2328958228482289326606995263276946037083/2667363506897187500000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node007_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-2575/5617), (-4992/5617), (-274594730511159758838454660984871/223444063405000000000000000000000)⟩ :: nodeSource000 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource000, nodeSource008]
  change node008.Check (baselineFlip ⟨(-2575/5617), (-4992/5617), (-274594730511159758838454660984871/223444063405000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node008_checked

theorem cover_checked : node000.Check source targets := by
  simpa only [nodeSource000, source] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window066
