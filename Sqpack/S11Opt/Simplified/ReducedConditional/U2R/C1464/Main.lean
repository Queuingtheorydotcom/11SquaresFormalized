import Sqpack.S11Opt.Simplified.ConditionalOwnedTrace
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1464.SharedStages000
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1464.SharedStages001
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1464.SharedStages002
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1464.SharedStages003
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1464.SharedStages004
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1464.SharedStages005
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1464.SharedStages006

namespace SquarePacking.S11Opt.Simplified.ReducedConditional.U2R.C1464
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.ConditionalOwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- One record per promotion; branch conditions remain in the program type. -/
private def program_r : Program cs_r :=
  .promote ⟨0, tris0, tgt0, [], cov0⟩ <|
  .promote ⟨1, tris1, tgt1, [0], cov1⟩ <|
  .promote ⟨3, tris2, tgt2, [0], cov2⟩ <|
  .promote ⟨5, tris3, tgt3, [2, 1], cov3⟩ <|
  .promote ⟨6, tris4, tgt4, [2, 1, 0], cov4⟩ <|
  .promote ⟨8, tris5, tgt5, [1], cov5⟩ <|
  .promote ⟨11, tris6, tgt6, [1], cov6⟩ <|
  .promote ⟨12, tris7, tgt7, [1], cov7⟩ <|
  .promote ⟨13, tris8, tgt8, [2, 0], cov8⟩ <|
  .promote ⟨14, tris9, tgt9, [0], cov9⟩ <|
  .promote ⟨0, tris10, tgt10, [8, 6], cov10⟩ <|
  .promote ⟨1, tris11, tgt11, [7, 0], cov11⟩ <|
  .promote ⟨3, tris12, tgt12, [7, 0], cov12⟩ <|
  .promote ⟨5, tris13, tgt13, [8, 7, 2, 1], cov13⟩ <|
  .promote ⟨6, tris14, tgt14, [7, 2, 1, 0], cov14⟩ <|
  .promote ⟨8, tris15, tgt15, [7, 6, 1], cov15⟩ <|
  .promote ⟨10, tris16, tgt16, [9, 7, 6, 2, 1], cov16⟩ <|
  .promote ⟨11, tris17, tgt17, [7, 2, 0], cov17⟩ <|
  .promote ⟨12, tris18, tgt18, [9, 2], cov18⟩ <|
  .promote ⟨13, tris19, tgt19, [9, 3, 2, 0], cov19⟩ <|
  .promote ⟨14, tris20, tgt20, [3, 0], cov20⟩ <|
  .promote ⟨0, tris21, tgt21, [9, 7, 5], cov21⟩ <|
  .promote ⟨5, tris22, tgt22, [10, 7, 6, 5, 0], cov22⟩ <|
  .promote ⟨6, tris23, tgt23, [11, 10, 6, 5, 0], cov23⟩ <|
  .promote ⟨8, tris24, tgt24, [5, 4, 1], cov24⟩ <|
  .promote ⟨10, tris25, tgt25, [7, 5, 4, 2, 1], cov25⟩ <|
  .promote ⟨11, tris26, tgt26, [5, 2, 0], cov26⟩ <|
  .promote ⟨12, tris27, tgt27, [7, 2], cov27⟩ <|
  .promote ⟨13, tris28, tgt28, [7, 3, 2, 0], cov28⟩ <|
  .promote ⟨14, tris29, tgt29, [3, 0], cov29⟩ <|
  .promote ⟨0, tris30, tgt30, [18, 7], cov30⟩ <|
  .promote ⟨1, tris31, tgt31, [8, 7, 0], cov31⟩ <|
  .promote ⟨3, tris32, tgt32, [8], cov32⟩ <|
  .promote ⟨5, tris33, tgt33, [9, 8, 7, 2, 1], cov33⟩ <|
  .promote ⟨6, tris34, tgt34, [8, 7, 2, 1, 0], cov34⟩ <|
  .promote ⟨8, tris35, tgt35, [9, 7, 6, 1], cov35⟩ <|
  .promote ⟨10, tris36, tgt36, [9, 7, 6, 2, 1], cov36⟩ <|
  .promote ⟨11, tris37, tgt37, [7, 2, 0], cov37⟩ <|
  .promote ⟨12, tris38, tgt38, [9, 2], cov38⟩ <|
  .promote ⟨13, tris39, tgt39, [9, 3, 2, 0], cov39⟩ <|
  .promote ⟨14, tris40, tgt40, [3, 2, 0], cov40⟩ <|
  .promote ⟨0, tris41, tgt41, [9, 7], cov41⟩ <|
  .promote ⟨1, tris42, tgt42, [8, 7, 0], cov42⟩ <|
  .promote ⟨3, tris43, tgt43, [8, 0], cov43⟩ <|
  .promote ⟨5, tris44, tgt44, [9, 8, 7, 2, 1], cov44⟩ <|
  .promote ⟨6, tris45, tgt45, [8, 7, 2, 1, 0], cov45⟩ <|
  .promote ⟨8, tris46, tgt46, [9, 7, 6, 1], cov46⟩ <|
  .promote ⟨10, tris47, tgt47, [9, 7, 6, 2, 1], cov47⟩ <|
  .promote ⟨11, tris48, tgt48, [7, 2, 0], cov48⟩ <|
  .promote ⟨12, tris49, tgt49, [9, 2], cov49⟩ <|
  .promote ⟨13, tris50, tgt50, [9, 3, 2, 0], cov50⟩ <|
  .promote ⟨14, tris51, tgt51, [3, 2, 0], cov51⟩ <|
  .promote ⟨0, tris52, tgt52, [9, 7], cov52⟩ <|
  .promote ⟨1, tris53, tgt53, [8, 7, 0], cov53⟩ <|
  .promote ⟨3, tris54, tgt54, [8, 0], cov54⟩ <|
  .promote ⟨5, tris55, tgt55, [9, 8, 7, 2, 1], cov55⟩ <|
  .promote ⟨6, tris56, tgt56, [8, 7, 2, 1, 0], cov56⟩ <|
  .promote ⟨8, tris57, tgt57, [9, 7, 6, 1], cov57⟩ <|
  .promote ⟨10, tris58, tgt58, [9, 7, 6, 2, 1], cov58⟩ <|
  .promote ⟨11, tris59, tgt59, [7, 2, 0], cov59⟩ <|
  .promote ⟨12, tris60, tgt60, [9, 2], cov60⟩ <|
  .promote ⟨13, tris61, tgt61, [9, 3, 2, 0], cov61⟩ <|
  .promote ⟨14, tris62, tgt62, [3, 2, 0], cov62⟩ <|
  .promote ⟨0, tris63, tgt63, [9, 7], cov63⟩ <|
  .promote ⟨1, tris64, tgt64, [8, 7, 0], cov64⟩ <|
  .promote ⟨3, tris65, tgt65, [8, 0], cov65⟩ <|
  .promote ⟨5, tris66, tgt66, [9, 8, 7, 2, 1], cov66⟩ <|
  .promote ⟨6, tris67, tgt67, [8, 7, 2, 1, 0], cov67⟩ <|
  .promote ⟨8, tris68, tgt68, [9, 7, 6, 1], cov68⟩ <|
  .promote ⟨10, tris69, tgt69, [9, 7, 6, 2, 1], cov69⟩ <|
  .promote ⟨11, tris70, tgt70, [7, 2, 0], cov70⟩ <|
  .promote ⟨12, tris71, tgt71, [9, 2], cov71⟩ <|
  .promote ⟨13, tris72, tgt72, [9, 3, 2, 0], cov72⟩ <|
  .promote ⟨14, tris73, tgt73, [3, 2, 0], cov73⟩ <|
  .promote ⟨0, tris74, tgt74, [9, 7], cov74⟩ <|
  .promote ⟨1, tris75, tgt75, [8, 7, 0], cov75⟩ <|
  .promote ⟨3, tris76, tgt76, [8, 0], cov76⟩ <|
  .promote ⟨5, tris77, tgt77, [9, 8, 7, 2, 1], cov77⟩ <|
  .promote ⟨6, tris78, tgt78, [8, 7, 2, 1, 0], cov78⟩ <|
  .promote ⟨8, tris79, tgt79, [9, 7, 6, 1], cov79⟩ <|
  .promote ⟨10, tris80, tgt80, [9, 7, 6, 2, 1], cov80⟩ <|
  .promote ⟨11, tris81, tgt81, [7, 2, 0], cov81⟩ <|
  .promote ⟨12, tris82, tgt82, [9, 2], cov82⟩ <|
  .promote ⟨13, tris83, tgt83, [9, 3, 2, 0], cov83⟩ <|
  .stop ⟨14, tris84, [3, 2, 0], cov84⟩

lemma hJ : J = maskAt 1464 := by decide +kernel

theorem excl_r : Excl Ux J cs_r :=
  check_sound le_rfl (by norm_num [Ux]) program_r
    (batchesOwnedC_nil Ux J cs_r) (by decide +kernel)

theorem notIn : ¬ RealizesIn Ux J := not_in_of_excl excl_r

theorem excluded : CaseExcluded (maskAt 1464) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Simplified.ReducedConditional.U2R.C1464
#print axioms SquarePacking.S11Opt.Simplified.ReducedConditional.U2R.C1464.excluded
