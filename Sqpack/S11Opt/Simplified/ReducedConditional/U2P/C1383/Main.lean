import Sqpack.S11Opt.Simplified.ConditionalOwnedTrace
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages000
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages002
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages004
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages006
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages008
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages010
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages012
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages013
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages014
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages001
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages003
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages005
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages007
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages009
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C1383.SharedStages011

namespace SquarePacking.S11Opt.Simplified.ReducedConditional.U2P.C1383
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.ConditionalOwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- One record per promotion; branch conditions remain in the program type. -/
private def program_r : Program cs_r :=
  .promote ⟨0, tris0, tgt0, [], cov0⟩ <|
  .promote ⟨1, tris1, tgt1, [0], cov1⟩ <|
  .promote ⟨3, tris2, tgt2, [0], cov2⟩ <|
  .promote ⟨4, tris3, tgt3, [2, 1], cov3⟩ <|
  .promote ⟨6, tris4, tgt4, [2, 1], cov4⟩ <|
  .promote ⟨8, tris5, tgt5, [1], cov5⟩ <|
  .promote ⟨9, tris6, tgt6, [2, 1, 0], cov6⟩ <|
  .promote ⟨10, tris7, tgt7, [2, 0], cov7⟩ <|
  .promote ⟨11, tris8, tgt8, [3, 0], cov8⟩ <|
  .promote ⟨13, tris9, tgt9, [3, 2, 1], cov9⟩ <|
  .promote ⟨15, tris10, tgt10, [2, 1], cov10⟩ <|
  .promote ⟨0, tris11, tgt11, [9, 7], cov11⟩ <|
  .promote ⟨1, tris12, tgt12, [0], cov12⟩ <|
  .promote ⟨3, tris13, tgt13, [8, 0], cov13⟩ <|
  .promote ⟨4, tris14, tgt14, [12, 8, 7, 2, 1], cov14⟩ <|
  .promote ⟨6, tris15, tgt15, [8, 7, 6, 2, 1], cov15⟩ <|
  .promote ⟨8, tris16, tgt16, [9, 6, 1], cov16⟩ <|
  .promote ⟨9, tris17, tgt17, [9, 7, 2, 1, 0], cov17⟩ <|
  .promote ⟨10, tris18, tgt18, [9, 8, 7, 2, 0], cov18⟩ <|
  .promote ⟨11, tris19, tgt19, [8, 3, 0], cov19⟩ <|
  .promote ⟨13, tris20, tgt20, [3, 2, 1], cov20⟩ <|
  .promote ⟨15, tris21, tgt21, [2, 1], cov21⟩ <|
  .promote ⟨0, tris22, tgt22, [20, 9, 7], cov22⟩ <|
  .promote ⟨1, tris23, tgt23, [8, 7, 0], cov23⟩ <|
  .promote ⟨3, tris24, tgt24, [8, 0], cov24⟩ <|
  .promote ⟨4, tris25, tgt25, [8, 7, 2], cov25⟩ <|
  .promote ⟨6, tris26, tgt26, [8, 7, 6, 2, 1], cov26⟩ <|
  .promote ⟨8, tris27, tgt27, [9, 6, 1], cov27⟩ <|
  .promote ⟨9, tris28, tgt28, [9, 7, 2, 1, 0], cov28⟩ <|
  .promote ⟨10, tris29, tgt29, [9, 8, 7, 2, 0], cov29⟩ <|
  .promote ⟨11, tris30, tgt30, [3, 0], cov30⟩ <|
  .promote ⟨13, tris31, tgt31, [3, 2, 1], cov31⟩ <|
  .promote ⟨15, tris32, tgt32, [2], cov32⟩ <|
  .promote ⟨0, tris33, tgt33, [9, 7, 4], cov33⟩ <|
  .promote ⟨1, tris34, tgt34, [8, 7, 5, 0], cov34⟩ <|
  .promote ⟨3, tris35, tgt35, [8, 4], cov35⟩ <|
  .promote ⟨4, tris36, tgt36, [8, 7, 2], cov36⟩ <|
  .promote ⟨6, tris37, tgt37, [8, 7, 6, 2, 1], cov37⟩ <|
  .promote ⟨8, tris38, tgt38, [9, 6, 1], cov38⟩ <|
  .promote ⟨9, tris39, tgt39, [9, 7, 2, 1, 0], cov39⟩ <|
  .promote ⟨10, tris40, tgt40, [9, 8, 7, 2, 0], cov40⟩ <|
  .promote ⟨11, tris41, tgt41, [3, 0], cov41⟩ <|
  .promote ⟨13, tris42, tgt42, [3, 2, 1], cov42⟩ <|
  .promote ⟨15, tris43, tgt43, [2, 1], cov43⟩ <|
  .promote ⟨0, tris44, tgt44, [9, 7, 4], cov44⟩ <|
  .promote ⟨1, tris45, tgt45, [8, 7, 5, 0], cov45⟩ <|
  .promote ⟨3, tris46, tgt46, [8, 4], cov46⟩ <|
  .promote ⟨4, tris47, tgt47, [8, 7, 2, 1], cov47⟩ <|
  .promote ⟨6, tris48, tgt48, [8, 7, 6, 2, 1], cov48⟩ <|
  .promote ⟨8, tris49, tgt49, [9, 6, 1], cov49⟩ <|
  .promote ⟨9, tris50, tgt50, [9, 7, 2, 1, 0], cov50⟩ <|
  .promote ⟨10, tris51, tgt51, [9, 8, 7, 2, 0], cov51⟩ <|
  .promote ⟨11, tris52, tgt52, [3, 0], cov52⟩ <|
  .promote ⟨13, tris53, tgt53, [3, 2, 1], cov53⟩ <|
  .promote ⟨15, tris54, tgt54, [2, 1], cov54⟩ <|
  .promote ⟨0, tris55, tgt55, [9, 7], cov55⟩ <|
  .promote ⟨1, tris56, tgt56, [8, 7, 5, 0], cov56⟩ <|
  .promote ⟨3, tris57, tgt57, [8, 4], cov57⟩ <|
  .promote ⟨4, tris58, tgt58, [8, 7, 2, 1], cov58⟩ <|
  .promote ⟨6, tris59, tgt59, [8, 7, 6, 2, 1], cov59⟩ <|
  .promote ⟨8, tris60, tgt60, [9, 6, 1], cov60⟩ <|
  .promote ⟨9, tris61, tgt61, [9, 2, 1, 0], cov61⟩ <|
  .promote ⟨10, tris62, tgt62, [9, 8, 7, 0], cov62⟩ <|
  .promote ⟨11, tris63, tgt63, [3, 0], cov63⟩ <|
  .promote ⟨13, tris64, tgt64, [3, 2, 1], cov64⟩ <|
  .promote ⟨15, tris65, tgt65, [2, 1], cov65⟩ <|
  .promote ⟨0, tris66, tgt66, [9, 7], cov66⟩ <|
  .promote ⟨1, tris67, tgt67, [8, 7, 5, 0], cov67⟩ <|
  .promote ⟨3, tris68, tgt68, [8, 4], cov68⟩ <|
  .promote ⟨4, tris69, tgt69, [8, 7, 2, 1], cov69⟩ <|
  .promote ⟨6, tris70, tgt70, [8, 7, 6, 2, 1], cov70⟩ <|
  .promote ⟨8, tris71, tgt71, [9, 6, 1], cov71⟩ <|
  .promote ⟨9, tris72, tgt72, [9, 7, 2, 1, 0], cov72⟩ <|
  .promote ⟨10, tris73, tgt73, [9, 8, 7, 2, 0], cov73⟩ <|
  .promote ⟨11, tris74, tgt74, [3, 0], cov74⟩ <|
  .promote ⟨13, tris75, tgt75, [3, 2, 1], cov75⟩ <|
  .promote ⟨15, tris76, tgt76, [2, 1], cov76⟩ <|
  .promote ⟨0, tris77, tgt77, [9, 7], cov77⟩ <|
  .promote ⟨1, tris78, tgt78, [8, 7, 5, 0], cov78⟩ <|
  .promote ⟨3, tris79, tgt79, [8, 4], cov79⟩ <|
  .promote ⟨4, tris80, tgt80, [8, 7, 2, 1], cov80⟩ <|
  .promote ⟨6, tris81, tgt81, [8, 7, 6, 2, 1], cov81⟩ <|
  .promote ⟨8, tris82, tgt82, [9, 6, 1], cov82⟩ <|
  .promote ⟨9, tris83, tgt83, [9, 7, 2, 1, 0], cov83⟩ <|
  .promote ⟨10, tris84, tgt84, [9, 8, 7, 2, 0], cov84⟩ <|
  .promote ⟨11, tris85, tgt85, [3, 0], cov85⟩ <|
  .promote ⟨13, tris86, tgt86, [3, 2, 1], cov86⟩ <|
  .promote ⟨15, tris87, tgt87, [2, 1], cov87⟩ <|
  .promote ⟨0, tris88, tgt88, [9, 7], cov88⟩ <|
  .promote ⟨1, tris89, tgt89, [8, 7, 5, 0], cov89⟩ <|
  .promote ⟨3, tris90, tgt90, [8, 4], cov90⟩ <|
  .promote ⟨4, tris91, tgt91, [8, 7, 2, 1], cov91⟩ <|
  .promote ⟨6, tris92, tgt92, [8, 7, 6, 2, 1], cov92⟩ <|
  .promote ⟨8, tris93, tgt93, [9, 6, 1], cov93⟩ <|
  .promote ⟨9, tris94, tgt94, [9, 7, 2, 1, 0], cov94⟩ <|
  .promote ⟨10, tris95, tgt95, [9, 8, 7, 2, 0], cov95⟩ <|
  .stop ⟨11, tris96, [3, 0], cov96⟩

lemma hJ : J = maskAt 1383 := by decide +kernel

theorem excl_r : Excl Ux J cs_r :=
  check_sound le_rfl (by norm_num [Ux]) program_r
    (batchesOwnedC_nil Ux J cs_r) (by decide +kernel)

theorem notIn : ¬ RealizesIn Ux J := not_in_of_excl excl_r

theorem excluded : CaseExcluded (maskAt 1383) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Simplified.ReducedConditional.U2P.C1383
#print axioms SquarePacking.S11Opt.Simplified.ReducedConditional.U2P.C1383.excluded
