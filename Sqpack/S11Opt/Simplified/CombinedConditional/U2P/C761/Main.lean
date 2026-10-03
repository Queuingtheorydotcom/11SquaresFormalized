import Sqpack.S11Opt.Simplified.ConditionalOwnedTrace
import Sqpack.S11Opt.Simplified.CombinedConditional.U2P.C761.SharedStages000
import Sqpack.S11Opt.Simplified.CombinedConditional.U2P.C761.SharedStages001
import Sqpack.S11Opt.Simplified.CombinedConditional.U2P.C761.SharedStages003
import Sqpack.S11Opt.Simplified.CombinedConditional.U2P.C761.SharedStages004
import Sqpack.S11Opt.Simplified.CombinedConditional.U2P.C761.SharedStages005
import Sqpack.S11Opt.Simplified.CombinedConditional.U2P.C761.SharedStages002

namespace SquarePacking.S11Opt.Simplified.CombinedConditional.U2P.C761
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.ConditionalOwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- One record per promotion; branch conditions remain in the program type. -/
private def program_r : Program cs_r :=
  .promote ⟨0, tris0, tgt0, [], cov0⟩ <|
  .promote ⟨1, tris1, tgt1, [0], cov1⟩ <|
  .promote ⟨2, tris2, tgt2, [0], cov2⟩ <|
  .promote ⟨3, tris3, tgt3, [0], cov3⟩ <|
  .promote ⟨8, tris4, tgt4, [], cov4⟩ <|
  .promote ⟨11, tris5, tgt5, [], cov5⟩ <|
  .promote ⟨12, tris6, tgt6, [1], cov6⟩ <|
  .promote ⟨13, tris7, tgt7, [2, 0], cov7⟩ <|
  .promote ⟨15, tris8, tgt8, [2], cov8⟩ <|
  .promote ⟨0, tris9, tgt9, [7], cov9⟩ <|
  .promote ⟨1, tris10, tgt10, [7, 0], cov10⟩ <|
  .promote ⟨2, tris11, tgt11, [7, 0], cov11⟩ <|
  .promote ⟨3, tris12, tgt12, [0], cov12⟩ <|
  .promote ⟨8, tris13, tgt13, [6, 5], cov13⟩ <|
  .promote ⟨9, tris14, tgt14, [7, 6, 2, 0], cov14⟩ <|
  .promote ⟨10, tris15, tgt15, [9, 7, 6, 3, 0], cov15⟩ <|
  .promote ⟨11, tris16, tgt16, [7, 4, 0], cov16⟩ <|
  .promote ⟨12, tris17, tgt17, [9, 3], cov17⟩ <|
  .promote ⟨13, tris18, tgt18, [4, 3, 2, 0], cov18⟩ <|
  .promote ⟨15, tris19, tgt19, [3, 2], cov19⟩ <|
  .promote ⟨0, tris20, tgt20, [9, 6], cov20⟩ <|
  .promote ⟨1, tris21, tgt21, [9, 0], cov21⟩ <|
  .promote ⟨2, tris22, tgt22, [9, 0], cov22⟩ <|
  .promote ⟨8, tris23, tgt23, [8, 5, 4], cov23⟩ <|
  .promote ⟨9, tris24, tgt24, [8, 6, 5, 1, 0], cov24⟩ <|
  .promote ⟨10, tris25, tgt25, [8, 6, 5, 2, 0], cov25⟩ <|
  .promote ⟨11, tris26, tgt26, [3, 0], cov26⟩ <|
  .promote ⟨12, tris27, tgt27, [8, 3], cov27⟩ <|
  .promote ⟨13, tris28, tgt28, [4, 3, 2, 0], cov28⟩ <|
  .promote ⟨15, tris29, tgt29, [3, 2], cov29⟩ <|
  .promote ⟨0, tris30, tgt30, [8, 6, 5], cov30⟩ <|
  .promote ⟨1, tris31, tgt31, [8, 6, 0], cov31⟩ <|
  .promote ⟨2, tris32, tgt32, [19, 7, 6, 5, 0], cov32⟩ <|
  .promote ⟨3, tris33, tgt33, [6, 0], cov33⟩ <|
  .promote ⟨8, tris34, tgt34, [9, 6, 5], cov34⟩ <|
  .promote ⟨9, tris35, tgt35, [9, 6, 2, 0], cov35⟩ <|
  .promote ⟨10, tris36, tgt36, [9, 7, 6, 3, 0], cov36⟩ <|
  .promote ⟨11, tris37, tgt37, [4, 0], cov37⟩ <|
  .promote ⟨12, tris38, tgt38, [9, 3], cov38⟩ <|
  .promote ⟨13, tris39, tgt39, [4, 3, 2, 0], cov39⟩ <|
  .promote ⟨0, tris40, tgt40, [8, 5, 4], cov40⟩ <|
  .promote ⟨1, tris41, tgt41, [8, 5, 0], cov41⟩ <|
  .promote ⟨2, tris42, tgt42, [8, 6, 4, 0], cov42⟩ <|
  .promote ⟨8, tris43, tgt43, [7, 4, 3], cov43⟩ <|
  .promote ⟨9, tris44, tgt44, [7, 4, 1, 0], cov44⟩ <|
  .promote ⟨0, tris45, tgt45, [3, 1, 0], cov45⟩ <|
  .stop ⟨1, tris46, [3, 1, 0], cov46⟩

lemma hJ : J = maskAt 761 := by decide +kernel

theorem excl_r : Excl Ux J cs_r :=
  check_sound le_rfl (by norm_num [Ux]) program_r
    (batchesOwnedC_nil Ux J cs_r) (by decide +kernel)

theorem notIn : ¬ RealizesIn Ux J := not_in_of_excl excl_r

theorem excluded : CaseExcluded (maskAt 761) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Simplified.CombinedConditional.U2P.C761
#print axioms SquarePacking.S11Opt.Simplified.CombinedConditional.U2P.C761.excluded
