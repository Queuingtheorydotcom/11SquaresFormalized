import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1646.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1636.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1640.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1636.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1645.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1645.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B009
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B010
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B008
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B007
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B012
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B011
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B013
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1646.B014

namespace SquarePacking.S11Opt.Split.U2R.C1646
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
  ⟨7, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov6 (by decide +kernel))⟩,
  ⟨9, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1636.cov7 (by decide +kernel))⟩,
  ⟨11, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov8 (by decide +kernel))⟩,
  ⟨12, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1640.cov9 (by decide +kernel))⟩,
  ⟨14, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov11 (by decide +kernel))⟩,
  ⟨3, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov12 (by decide +kernel))⟩,
  ⟨4, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1636.cov14 (by decide +kernel))⟩,
  ⟨5, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1636.cov15 (by decide +kernel))⟩,
  ⟨6, tris16, tgt16,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1645.cov16 (by decide +kernel))⟩,
  ⟨7, tris17, tgt17,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1645.cov17 (by decide +kernel))⟩,
  ⟨9, tris18, tgt18, cov18⟩,
  ⟨11, tris19, tgt19, cov19⟩,
  ⟨12, tris20, tgt20, cov20⟩,
  ⟨14, tris21, tgt21, cov21⟩,
  ⟨0, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1645.cov19 (by decide +kernel))⟩,
  ⟨2, tris23, tgt23,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1645.cov20 (by decide +kernel))⟩,
  ⟨3, tris24, tgt24, cov24⟩,
  ⟨4, tris25, tgt25, cov25⟩,
  ⟨5, tris26, tgt26, cov26⟩,
  ⟨6, tris27, tgt27, cov27⟩,
  ⟨7, tris28, tgt28, cov28⟩,
  ⟨9, tris29, tgt29, cov29⟩,
  ⟨11, tris30, tgt30, cov30⟩,
  ⟨12, tris31, tgt31, cov31⟩,
  ⟨14, tris32, tgt32, cov32⟩,
  ⟨0, tris33, tgt33, cov33⟩,
  ⟨2, tris34, tgt34, cov34⟩,
  ⟨3, tris35, tgt35, cov35⟩,
  ⟨4, tris36, tgt36, cov36⟩,
  ⟨5, tris37, tgt37, cov37⟩,
  ⟨6, tris38, tgt38, cov38⟩,
  ⟨7, tris39, tgt39, cov39⟩,
  ⟨9, tris40, tgt40, cov40⟩,
  ⟨11, tris41, tgt41, cov41⟩,
  ⟨12, tris42, tgt42, cov42⟩,
  ⟨14, tris43, tgt43, cov43⟩,
  ⟨0, tris44, tgt44, cov44⟩,
  ⟨2, tris45, tgt45, cov45⟩,
  ⟨3, tris46, tgt46, cov46⟩,
  ⟨4, tris47, tgt47, cov47⟩,
  ⟨5, tris48, tgt48, cov48⟩,
  ⟨6, tris49, tgt49, cov49⟩,
  ⟨7, tris50, tgt50, cov50⟩,
  ⟨9, tris51, tgt51, cov51⟩,
  ⟨11, tris52, tgt52, cov52⟩,
  ⟨12, tris53, tgt53, cov53⟩,
  ⟨14, tris54, tgt54, cov54⟩,
  ⟨0, tris55, tgt55, cov55⟩,
  ⟨2, tris56, tgt56, cov56⟩,
  ⟨3, tris57, tgt57, cov57⟩,
  ⟨4, tris58, tgt58, cov58⟩,
  ⟨5, tris59, tgt59, cov59⟩,
  ⟨6, tris60, tgt60, cov60⟩,
  ⟨7, tris61, tgt61, cov61⟩,
  ⟨9, tris62, tgt62, cov62⟩,
  ⟨11, tris63, tgt63, cov63⟩,
  ⟨12, tris64, tgt64, cov64⟩,
  ⟨14, tris65, tgt65, cov65⟩,
  ⟨0, tris66, tgt66, cov66⟩,
  ⟨2, tris67, tgt67, cov67⟩,
  ⟨3, tris68, tgt68, cov68⟩,
  ⟨4, tris69, tgt69, cov69⟩,
  ⟨5, tris70, tgt70, cov70⟩,
  ⟨6, tris71, tgt71, cov71⟩,
  ⟨7, tris72, tgt72, cov72⟩,
  ⟨9, tris73, tgt73, cov73⟩,
  ⟨11, tris74, tgt74, cov74⟩,
  ⟨12, tris75, tgt75, cov75⟩,
  ⟨14, tris76, tgt76, cov76⟩,
  ⟨0, tris77, tgt77, cov77⟩,
  ⟨2, tris78, tgt78, cov78⟩,
  ⟨3, tris79, tgt79, cov79⟩,
  ⟨4, tris80, tgt80, cov80⟩,
  ⟨5, tris81, tgt81, cov81⟩,
  ⟨6, tris82, tgt82, cov82⟩,
  ⟨7, tris83, tgt83, cov83⟩,
  ⟨9, tris84, tgt84, cov84⟩,
  ⟨0, tris85, tgt85, cov85⟩,
  ⟨2, tris86, tgt86, cov86⟩,
  ⟨4, tris87, tgt87, cov87⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, tris88, cov88⟩

lemma hJ : J = maskAt 1646 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1646) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1646
#print axioms SquarePacking.S11Opt.Split.U2R.C1646.excluded
