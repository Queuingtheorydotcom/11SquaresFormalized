import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1775.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2182.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1769.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1769.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1774.B000
import Sqpack.S11Opt.Split.U2R.C1774.S16
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1775.B010
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1775.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1775.B008
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1775.B009
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1775.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1775.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1775.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1775.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1775.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1775.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1775.B007
import Sqpack.S11Opt.Split.U2R.C1775.S73

namespace SquarePacking.S11Opt.Split.U2R.C1775
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨0, tris0, tgt0,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov0 (by decide +kernel))⟩,
  ⟨2, tris1, tgt1,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov0 (by decide +kernel))⟩,
  ⟨3, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov1 (by decide +kernel))⟩,
  ⟨4, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov3 (by decide +kernel))⟩,
  ⟨6, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov3 (by decide +kernel))⟩,
  ⟨7, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov4 (by decide +kernel))⟩,
  ⟨9, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1769.cov6 (by decide +kernel))⟩,
  ⟨10, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1769.cov7 (by decide +kernel))⟩,
  ⟨12, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1769.cov9 (by decide +kernel))⟩,
  ⟨13, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1774.cov9 (by decide +kernel))⟩,
  ⟨15, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1769.cov11 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2182.cov9 (by decide +kernel))⟩,
  ⟨3, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov11 (by decide +kernel))⟩,
  ⟨4, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1769.cov14 (by decide +kernel))⟩,
  ⟨6, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1774.cov15 (by decide +kernel))⟩,
  ⟨7, tris16, tgt16,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1774.cov16 (by decide +kernel))⟩,
  ⟨9, tris17, tgt17,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1774.cov17 (by decide +kernel))⟩,
  ⟨10, tris18, tgt18, cov18⟩,
  ⟨12, tris19, tgt19, cov19⟩,
  ⟨13, tris20, tgt20, cov20⟩,
  ⟨15, tris21, tgt21, cov21⟩,
  ⟨0, tris22, tgt22, cov22⟩,
  ⟨2, tris23, tgt23, cov23⟩,
  ⟨3, tris24, tgt24, cov24⟩,
  ⟨4, tris25, tgt25, cov25⟩,
  ⟨6, tris26, tgt26, cov26⟩,
  ⟨7, tris27, tgt27, cov27⟩,
  ⟨9, tris28, tgt28, cov28⟩,
  ⟨10, tris29, tgt29, cov29⟩,
  ⟨12, tris30, tgt30, cov30⟩,
  ⟨13, tris31, tgt31, cov31⟩,
  ⟨15, tris32, tgt32, cov32⟩,
  ⟨0, tris33, tgt33, cov33⟩,
  ⟨2, tris34, tgt34, cov34⟩,
  ⟨3, tris35, tgt35, cov35⟩,
  ⟨4, tris36, tgt36, cov36⟩,
  ⟨6, tris37, tgt37, cov37⟩,
  ⟨7, tris38, tgt38, cov38⟩,
  ⟨9, tris39, tgt39, cov39⟩,
  ⟨10, tris40, tgt40, cov40⟩,
  ⟨12, tris41, tgt41, cov41⟩,
  ⟨13, tris42, tgt42, cov42⟩,
  ⟨15, tris43, tgt43, cov43⟩,
  ⟨0, tris44, tgt44, cov44⟩,
  ⟨2, tris45, tgt45, cov45⟩,
  ⟨3, tris46, tgt46, cov46⟩,
  ⟨4, tris47, tgt47, cov47⟩,
  ⟨6, tris48, tgt48, cov48⟩,
  ⟨7, tris49, tgt49, cov49⟩,
  ⟨9, tris50, tgt50, cov50⟩,
  ⟨10, tris51, tgt51, cov51⟩,
  ⟨12, tris52, tgt52, cov52⟩,
  ⟨13, tris53, tgt53, cov53⟩,
  ⟨0, tris54, tgt54, cov54⟩,
  ⟨2, tris55, tgt55, cov55⟩,
  ⟨3, tris56, tgt56, cov56⟩,
  ⟨4, tris57, tgt57, cov57⟩,
  ⟨6, tris58, tgt58, cov58⟩,
  ⟨7, tris59, tgt59, cov59⟩,
  ⟨9, tris60, tgt60, cov60⟩,
  ⟨10, tris61, tgt61, cov61⟩,
  ⟨12, tris62, tgt62, cov62⟩,
  ⟨13, tris63, tgt63, cov63⟩,
  ⟨15, tris64, tgt64, cov64⟩,
  ⟨0, tris65, tgt65, cov65⟩,
  ⟨2, tris66, tgt66, cov66⟩,
  ⟨3, tris67, tgt67, cov67⟩,
  ⟨4, tris68, tgt68, cov68⟩,
  ⟨6, tris69, tgt69, cov69⟩,
  ⟨7, tris70, tgt70, cov70⟩,
  ⟨9, tris71, tgt71, cov71⟩,
  ⟨10, tris72, tgt72, cov72⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨13, tris73, cov73⟩

lemma hJ : J = maskAt 1775 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1775) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1775
#print axioms SquarePacking.S11Opt.Split.U2R.C1775.excluded
