import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1694.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1636.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1640.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1636.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1650.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1686.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1686.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1693.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1693.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1693.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B016
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B012
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B007
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B013
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B011
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B015
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B010
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B008
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B009
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B014
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1694.B003
import Sqpack.S11Opt.Split.U2R.C1694.S105

namespace SquarePacking.S11Opt.Split.U2R.C1694
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
  ⟨5, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov4 (by decide +kernel))⟩,
  ⟨6, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov5 (by decide +kernel))⟩,
  ⟨9, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1636.cov7 (by decide +kernel))⟩,
  ⟨11, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1673.cov8 (by decide +kernel))⟩,
  ⟨12, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1640.cov9 (by decide +kernel))⟩,
  ⟨13, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1650.cov9 (by decide +kernel))⟩,
  ⟨15, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1673.cov12 (by decide +kernel))⟩,
  ⟨3, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1673.cov13 (by decide +kernel))⟩,
  ⟨4, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1636.cov14 (by decide +kernel))⟩,
  ⟨5, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1686.cov15 (by decide +kernel))⟩,
  ⟨6, tris16, tgt16,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1693.cov16 (by decide +kernel))⟩,
  ⟨9, tris17, tgt17, cov17⟩,
  ⟨11, tris18, tgt18, cov18⟩,
  ⟨12, tris19, tgt19, cov19⟩,
  ⟨13, tris20, tgt20, cov20⟩,
  ⟨15, tris21, tgt21, cov21⟩,
  ⟨0, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1686.cov22 (by decide +kernel))⟩,
  ⟨2, tris23, tgt23,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1693.cov23 (by decide +kernel))⟩,
  ⟨3, tris24, tgt24,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1693.cov24 (by decide +kernel))⟩,
  ⟨4, tris25, tgt25, cov25⟩,
  ⟨5, tris26, tgt26, cov26⟩,
  ⟨6, tris27, tgt27, cov27⟩,
  ⟨9, tris28, tgt28, cov28⟩,
  ⟨11, tris29, tgt29, cov29⟩,
  ⟨12, tris30, tgt30, cov30⟩,
  ⟨13, tris31, tgt31, cov31⟩,
  ⟨15, tris32, tgt32, cov32⟩,
  ⟨0, tris33, tgt33, cov33⟩,
  ⟨2, tris34, tgt34, cov34⟩,
  ⟨3, tris35, tgt35, cov35⟩,
  ⟨4, tris36, tgt36, cov36⟩,
  ⟨5, tris37, tgt37, cov37⟩,
  ⟨6, tris38, tgt38, cov38⟩,
  ⟨9, tris39, tgt39, cov39⟩,
  ⟨11, tris40, tgt40, cov40⟩,
  ⟨12, tris41, tgt41, cov41⟩,
  ⟨13, tris42, tgt42, cov42⟩,
  ⟨15, tris43, tgt43, cov43⟩,
  ⟨0, tris44, tgt44, cov44⟩,
  ⟨2, tris45, tgt45, cov45⟩,
  ⟨3, tris46, tgt46, cov46⟩,
  ⟨4, tris47, tgt47, cov47⟩,
  ⟨5, tris48, tgt48, cov48⟩,
  ⟨6, tris49, tgt49, cov49⟩,
  ⟨9, tris50, tgt50, cov50⟩,
  ⟨11, tris51, tgt51, cov51⟩,
  ⟨12, tris52, tgt52, cov52⟩,
  ⟨13, tris53, tgt53, cov53⟩,
  ⟨15, tris54, tgt54, cov54⟩,
  ⟨0, tris55, tgt55, cov55⟩,
  ⟨2, tris56, tgt56, cov56⟩,
  ⟨3, tris57, tgt57, cov57⟩,
  ⟨4, tris58, tgt58, cov58⟩,
  ⟨5, tris59, tgt59, cov59⟩,
  ⟨6, tris60, tgt60, cov60⟩,
  ⟨9, tris61, tgt61, cov61⟩,
  ⟨11, tris62, tgt62, cov62⟩,
  ⟨12, tris63, tgt63, cov63⟩,
  ⟨13, tris64, tgt64, cov64⟩,
  ⟨0, tris65, tgt65, cov65⟩,
  ⟨2, tris66, tgt66, cov66⟩,
  ⟨3, tris67, tgt67, cov67⟩,
  ⟨4, tris68, tgt68, cov68⟩,
  ⟨5, tris69, tgt69, cov69⟩,
  ⟨6, tris70, tgt70, cov70⟩,
  ⟨9, tris71, tgt71, cov71⟩,
  ⟨11, tris72, tgt72, cov72⟩,
  ⟨12, tris73, tgt73, cov73⟩,
  ⟨13, tris74, tgt74, cov74⟩,
  ⟨0, tris75, tgt75, cov75⟩,
  ⟨2, tris76, tgt76, cov76⟩,
  ⟨3, tris77, tgt77, cov77⟩,
  ⟨4, tris78, tgt78, cov78⟩,
  ⟨5, tris79, tgt79, cov79⟩,
  ⟨6, tris80, tgt80, cov80⟩,
  ⟨9, tris81, tgt81, cov81⟩,
  ⟨12, tris82, tgt82, cov82⟩,
  ⟨13, tris83, tgt83, cov83⟩,
  ⟨15, tris84, tgt84, cov84⟩,
  ⟨0, tris85, tgt85, cov85⟩,
  ⟨2, tris86, tgt86, cov86⟩,
  ⟨3, tris87, tgt87, cov87⟩,
  ⟨4, tris88, tgt88, cov88⟩,
  ⟨5, tris89, tgt89, cov89⟩,
  ⟨6, tris90, tgt90, cov90⟩,
  ⟨9, tris91, tgt91, cov91⟩,
  ⟨11, tris92, tgt92, cov92⟩,
  ⟨12, tris93, tgt93, cov93⟩,
  ⟨13, tris94, tgt94, cov94⟩,
  ⟨0, tris95, tgt95, cov95⟩,
  ⟨2, tris96, tgt96, cov96⟩,
  ⟨3, tris97, tgt97, cov97⟩,
  ⟨4, tris98, tgt98, cov98⟩,
  ⟨5, tris99, tgt99, cov99⟩,
  ⟨6, tris100, tgt100, cov100⟩,
  ⟨9, tris101, tgt101, cov101⟩,
  ⟨0, tris102, tgt102, cov102⟩,
  ⟨2, tris103, tgt103, cov103⟩,
  ⟨4, tris104, tgt104, cov104⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, tris105, cov105⟩

lemma hJ : J = maskAt 1694 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1694) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1694
#print axioms SquarePacking.S11Opt.Split.U2R.C1694.excluded
