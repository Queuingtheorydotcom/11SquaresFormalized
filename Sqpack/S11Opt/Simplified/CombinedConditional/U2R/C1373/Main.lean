import Sqpack.S11Opt.Simplified.ConditionalOwnedTrace
import Sqpack.S11Opt.Simplified.CombinedConditional.U2R.C1373.SharedStages000
import Sqpack.S11Opt.Simplified.CombinedConditional.U2R.C1373.SharedStages001
import Sqpack.S11Opt.Simplified.CombinedConditional.U2R.C1373.SharedStages002
import Sqpack.S11Opt.Simplified.CombinedConditional.U2R.C1373.SharedStages003
import Sqpack.S11Opt.Simplified.CombinedConditional.U2R.C1373.SharedStages004
import Sqpack.S11Opt.Simplified.CombinedConditional.U2R.C1373.SharedStages005

namespace SquarePacking.S11Opt.Simplified.CombinedConditional.U2R.C1373
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
  .promote ⟨7, tris5, tgt5, [2, 0], cov5⟩ <|
  .promote ⟨9, tris6, tgt6, [2, 1], cov6⟩ <|
  .promote ⟨10, tris7, tgt7, [2, 1, 0], cov7⟩ <|
  .promote ⟨12, tris8, tgt8, [1], cov8⟩ <|
  .promote ⟨14, tris9, tgt9, [1], cov9⟩ <|
  .promote ⟨15, tris10, tgt10, [4, 2, 0], cov10⟩ <|
  .promote ⟨0, tris11, tgt11, [9, 7], cov11⟩ <|
  .promote ⟨1, tris12, tgt12, [0], cov12⟩ <|
  .promote ⟨3, tris13, tgt13, [7, 0], cov13⟩ <|
  .promote ⟨4, tris14, tgt14, [7, 2, 1], cov14⟩ <|
  .promote ⟨6, tris15, tgt15, [9, 8, 7, 2, 1], cov15⟩ <|
  .promote ⟨7, tris16, tgt16, [2, 0], cov16⟩ <|
  .promote ⟨9, tris17, tgt17, [9, 8, 7, 2, 1], cov17⟩ <|
  .promote ⟨10, tris18, tgt18, [8, 7, 2, 1, 0], cov18⟩ <|
  .promote ⟨12, tris19, tgt19, [1], cov19⟩ <|
  .promote ⟨14, tris20, tgt20, [9, 2, 1], cov20⟩ <|
  .promote ⟨15, tris21, tgt21, [2, 0], cov21⟩ <|
  .promote ⟨0, tris22, tgt22, [9, 7], cov22⟩ <|
  .promote ⟨1, tris23, tgt23, [7, 0], cov23⟩ <|
  .promote ⟨3, tris24, tgt24, [8, 7, 0], cov24⟩ <|
  .promote ⟨4, tris25, tgt25, [9, 7, 2, 1], cov25⟩ <|
  .promote ⟨6, tris26, tgt26, [9, 8, 7, 2, 1], cov26⟩ <|
  .promote ⟨7, tris27, tgt27, [8, 2, 0], cov27⟩ <|
  .promote ⟨9, tris28, tgt28, [9, 8, 7, 2, 1], cov28⟩ <|
  .promote ⟨10, tris29, tgt29, [8, 7, 2, 1, 0], cov29⟩ <|
  .promote ⟨12, tris30, tgt30, [9, 1], cov30⟩ <|
  .promote ⟨14, tris31, tgt31, [2, 1], cov31⟩ <|
  .promote ⟨15, tris32, tgt32, [2], cov32⟩ <|
  .promote ⟨0, tris33, tgt33, [9, 7], cov33⟩ <|
  .promote ⟨1, tris34, tgt34, [7, 0], cov34⟩ <|
  .promote ⟨3, tris35, tgt35, [8, 7, 0], cov35⟩ <|
  .promote ⟨4, tris36, tgt36, [7, 2], cov36⟩ <|
  .promote ⟨6, tris37, tgt37, [9, 8, 7, 2, 1], cov37⟩ <|
  .promote ⟨7, tris38, tgt38, [8, 2, 0], cov38⟩ <|
  .promote ⟨9, tris39, tgt39, [9, 8, 7, 2, 1], cov39⟩ <|
  .promote ⟨10, tris40, tgt40, [8, 7, 2, 1, 0], cov40⟩ <|
  .promote ⟨12, tris41, tgt41, [9, 1], cov41⟩ <|
  .promote ⟨14, tris42, tgt42, [2, 1], cov42⟩ <|
  .promote ⟨15, tris43, tgt43, [2], cov43⟩ <|
  .promote ⟨0, tris44, tgt44, [9, 7], cov44⟩ <|
  .promote ⟨1, tris45, tgt45, [8, 7, 0], cov45⟩ <|
  .promote ⟨3, tris46, tgt46, [8, 7, 0], cov46⟩ <|
  .promote ⟨4, tris47, tgt47, [9, 7, 2], cov47⟩ <|
  .promote ⟨6, tris48, tgt48, [9, 8, 7, 2, 1], cov48⟩ <|
  .promote ⟨7, tris49, tgt49, [8, 2, 0], cov49⟩ <|
  .promote ⟨9, tris50, tgt50, [9, 8, 7, 2, 1], cov50⟩ <|
  .promote ⟨10, tris51, tgt51, [8, 7, 2, 1, 0], cov51⟩ <|
  .promote ⟨12, tris52, tgt52, [9, 1], cov52⟩ <|
  .promote ⟨14, tris53, tgt53, [2, 1], cov53⟩ <|
  .promote ⟨15, tris54, tgt54, [2, 0], cov54⟩ <|
  .promote ⟨0, tris55, tgt55, [9, 7, 6], cov55⟩ <|
  .promote ⟨1, tris56, tgt56, [8, 7, 0], cov56⟩ <|
  .promote ⟨3, tris57, tgt57, [8, 7, 0], cov57⟩ <|
  .promote ⟨4, tris58, tgt58, [9, 7, 2], cov58⟩ <|
  .promote ⟨6, tris59, tgt59, [9, 8, 7, 2, 1], cov59⟩ <|
  .promote ⟨7, tris60, tgt60, [8, 2, 0], cov60⟩ <|
  .promote ⟨9, tris61, tgt61, [9, 8, 7, 2, 1], cov61⟩ <|
  .promote ⟨10, tris62, tgt62, [8, 7, 2, 1, 0], cov62⟩ <|
  .promote ⟨12, tris63, tgt63, [9, 1], cov63⟩ <|
  .promote ⟨14, tris64, tgt64, [2, 1], cov64⟩ <|
  .promote ⟨0, tris65, tgt65, [8, 6], cov65⟩ <|
  .promote ⟨1, tris66, tgt66, [7, 6, 0], cov66⟩ <|
  .promote ⟨3, tris67, tgt67, [7, 6, 0], cov67⟩ <|
  .promote ⟨4, tris68, tgt68, [6, 2], cov68⟩ <|
  .promote ⟨6, tris69, tgt69, [8, 7, 6, 2, 1], cov69⟩ <|
  .stop ⟨9, tris70, [7, 6, 5, 1, 0], cov70⟩

lemma hJ : J = maskAt 1373 := by decide +kernel

theorem excl_r : Excl Ux J cs_r :=
  check_sound le_rfl (by norm_num [Ux]) program_r
    (batchesOwnedC_nil Ux J cs_r) (by decide +kernel)

theorem notIn : ¬ RealizesIn Ux J := not_in_of_excl excl_r

theorem excluded : CaseExcluded (maskAt 1373) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Simplified.CombinedConditional.U2R.C1373
#print axioms SquarePacking.S11Opt.Simplified.CombinedConditional.U2R.C1373.excluded
