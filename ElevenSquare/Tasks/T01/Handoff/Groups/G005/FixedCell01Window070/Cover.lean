import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window070.CoverLeaf004
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window070.CoverLeaf005
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window070.CoverLeaf006
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window070.CoverLeaf007
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window070.CoverLeaf008

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window070
open ElevenSquare.Pending ElevenSquare.Tasks.T01
noncomputable section

theorem node003_checked : node003.Check nodeSource003 targets := by
  refine ⟨node004_checked, ?_⟩
  have he : baselineFlip ⟨(-173431483117976703253419723021/3820000000000000000000000000000), (-55592369876637204828989733211/1910000000000000000000000000000), (-79152105091717815774536555277975103650067186234359359494040919512711/962428360769200000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource003 = nodeSource005 := by
    norm_num [baselineFlip, nodeSource003, nodeSource005]
  change node005.Check (baselineFlip ⟨(-173431483117976703253419723021/3820000000000000000000000000000), (-55592369876637204828989733211/1910000000000000000000000000000), (-79152105091717815774536555277975103650067186234359359494040919512711/962428360769200000000000000000000000000000000000000000000000000000000)⟩ :: nodeSource003) targets
  rw [he]
  exact node005_checked

theorem node002_checked : node002.Check nodeSource002 targets := by
  refine ⟨node003_checked, ?_⟩
  have he : baselineFlip ⟨(-387708359002281417731/4000000000000000000000), (-271525087292028299883516527423/3820000000000000000000000000000), (-43598800840294961120911194366067717473727475790106970966416579/240607090192300000000000000000000000000000000000000000000000000)⟩ :: nodeSource002 = nodeSource006 := by
    norm_num [baselineFlip, nodeSource002, nodeSource006]
  change node006.Check (baselineFlip ⟨(-387708359002281417731/4000000000000000000000), (-271525087292028299883516527423/3820000000000000000000000000000), (-43598800840294961120911194366067717473727475790106970966416579/240607090192300000000000000000000000000000000000000000000000000)⟩ :: nodeSource002) targets
  rw [he]
  exact node006_checked

theorem node001_checked : node001.Check nodeSource001 targets := by
  refine ⟨node002_checked, ?_⟩
  have he : baselineFlip ⟨(-6016/6305), (1887/6305), (-1443995663160223290832845916777664353903/1259722985300000000000000000000000000000)⟩ :: nodeSource001 = nodeSource007 := by
    norm_num [baselineFlip, nodeSource001, nodeSource007]
  change node007.Check (baselineFlip ⟨(-6016/6305), (1887/6305), (-1443995663160223290832845916777664353903/1259722985300000000000000000000000000000)⟩ :: nodeSource001) targets
  rw [he]
  exact node007_checked

theorem node000_checked : node000.Check nodeSource000 targets := by
  refine ⟨node001_checked, ?_⟩
  have he : baselineFlip ⟨(-1887/6305), (-6016/6305), (-18984925974992277123326965543554235989/19683171645312500000000000000000000000)⟩ :: nodeSource000 = nodeSource008 := by
    norm_num [baselineFlip, nodeSource000, nodeSource008]
  change node008.Check (baselineFlip ⟨(-1887/6305), (-6016/6305), (-18984925974992277123326965543554235989/19683171645312500000000000000000000000)⟩ :: nodeSource000) targets
  rw [he]
  exact node008_checked

theorem cover_checked : node000.Check source targets := by
  simpa only [nodeSource000, source] using node000_checked

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedCell01Window070
