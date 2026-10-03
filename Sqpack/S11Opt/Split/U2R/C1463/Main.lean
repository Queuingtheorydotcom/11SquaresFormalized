import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1463.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1411.B000
import Sqpack.S11Opt.Split.U2R.C1411.S4
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1597.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1429.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B019
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B007
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B018
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B009
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B012
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B016
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B015
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B017
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B011
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B020
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B008
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B013
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B014
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B010
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1463.B021

namespace SquarePacking.S11Opt.Split.U2R.C1463
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨0, tris0, tgt0,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov0 (by decide +kernel))⟩,
  ⟨1, tris1, tgt1,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov1 (by decide +kernel))⟩,
  ⟨3, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1235.cov2 (by decide +kernel))⟩,
  ⟨5, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov3 (by decide +kernel))⟩,
  ⟨6, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov4 (by decide +kernel))⟩,
  ⟨8, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov6 (by decide +kernel))⟩,
  ⟨9, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov7 (by decide +kernel))⟩,
  ⟨11, tris7, tgt7, cov7⟩,
  ⟨12, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov9 (by decide +kernel))⟩,
  ⟨13, tris9, tgt9, cov9⟩,
  ⟨15, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1597.cov9 (by decide +kernel))⟩,
  ⟨1, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov12 (by decide +kernel))⟩,
  ⟨3, tris13, tgt13, cov13⟩,
  ⟨5, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov14 (by decide +kernel))⟩,
  ⟨6, tris15, tgt15, cov15⟩,
  ⟨8, tris16, tgt16, cov16⟩,
  ⟨9, tris17, tgt17, cov17⟩,
  ⟨11, tris18, tgt18, cov18⟩,
  ⟨12, tris19, tgt19, cov19⟩,
  ⟨13, tris20, tgt20, cov20⟩,
  ⟨15, tris21, tgt21, cov21⟩,
  ⟨0, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov22 (by decide +kernel))⟩,
  ⟨1, tris23, tgt23,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1429.cov23 (by decide +kernel))⟩,
  ⟨3, tris24, tgt24, cov24⟩,
  ⟨5, tris25, tgt25, cov25⟩,
  ⟨6, tris26, tgt26, cov26⟩,
  ⟨8, tris27, tgt27, cov27⟩,
  ⟨9, tris28, tgt28, cov28⟩,
  ⟨11, tris29, tgt29, cov29⟩,
  ⟨12, tris30, tgt30, cov30⟩,
  ⟨13, tris31, tgt31, cov31⟩,
  ⟨15, tris32, tgt32, cov32⟩,
  ⟨0, tris33, tgt33, cov33⟩,
  ⟨1, tris34, tgt34, cov34⟩,
  ⟨3, tris35, tgt35, cov35⟩,
  ⟨5, tris36, tgt36, cov36⟩,
  ⟨6, tris37, tgt37, cov37⟩,
  ⟨8, tris38, tgt38, cov38⟩,
  ⟨9, tris39, tgt39, cov39⟩,
  ⟨11, tris40, tgt40, cov40⟩,
  ⟨12, tris41, tgt41, cov41⟩,
  ⟨13, tris42, tgt42, cov42⟩,
  ⟨15, tris43, tgt43, cov43⟩,
  ⟨0, tris44, tgt44, cov44⟩,
  ⟨1, tris45, tgt45, cov45⟩,
  ⟨3, tris46, tgt46, cov46⟩,
  ⟨5, tris47, tgt47, cov47⟩,
  ⟨6, tris48, tgt48, cov48⟩,
  ⟨8, tris49, tgt49, cov49⟩,
  ⟨9, tris50, tgt50, cov50⟩,
  ⟨11, tris51, tgt51, cov51⟩,
  ⟨12, tris52, tgt52, cov52⟩,
  ⟨13, tris53, tgt53, cov53⟩,
  ⟨15, tris54, tgt54, cov54⟩,
  ⟨0, tris55, tgt55, cov55⟩,
  ⟨1, tris56, tgt56, cov56⟩,
  ⟨3, tris57, tgt57, cov57⟩,
  ⟨5, tris58, tgt58, cov58⟩,
  ⟨6, tris59, tgt59, cov59⟩,
  ⟨8, tris60, tgt60, cov60⟩,
  ⟨9, tris61, tgt61, cov61⟩,
  ⟨11, tris62, tgt62, cov62⟩,
  ⟨12, tris63, tgt63, cov63⟩,
  ⟨13, tris64, tgt64, cov64⟩,
  ⟨15, tris65, tgt65, cov65⟩,
  ⟨0, tris66, tgt66, cov66⟩,
  ⟨1, tris67, tgt67, cov67⟩,
  ⟨3, tris68, tgt68, cov68⟩,
  ⟨5, tris69, tgt69, cov69⟩,
  ⟨6, tris70, tgt70, cov70⟩,
  ⟨8, tris71, tgt71, cov71⟩,
  ⟨9, tris72, tgt72, cov72⟩,
  ⟨11, tris73, tgt73, cov73⟩,
  ⟨12, tris74, tgt74, cov74⟩,
  ⟨13, tris75, tgt75, cov75⟩,
  ⟨15, tris76, tgt76, cov76⟩,
  ⟨0, tris77, tgt77, cov77⟩,
  ⟨1, tris78, tgt78, cov78⟩,
  ⟨3, tris79, tgt79, cov79⟩,
  ⟨5, tris80, tgt80, cov80⟩,
  ⟨6, tris81, tgt81, cov81⟩,
  ⟨8, tris82, tgt82, cov82⟩,
  ⟨9, tris83, tgt83, cov83⟩,
  ⟨11, tris84, tgt84, cov84⟩,
  ⟨12, tris85, tgt85, cov85⟩,
  ⟨13, tris86, tgt86, cov86⟩,
  ⟨15, tris87, tgt87, cov87⟩,
  ⟨0, tris88, tgt88, cov88⟩,
  ⟨1, tris89, tgt89, cov89⟩,
  ⟨3, tris90, tgt90, cov90⟩,
  ⟨5, tris91, tgt91, cov91⟩,
  ⟨6, tris92, tgt92, cov92⟩,
  ⟨8, tris93, tgt93, cov93⟩,
  ⟨9, tris94, tgt94, cov94⟩,
  ⟨11, tris95, tgt95, cov95⟩,
  ⟨12, tris96, tgt96, cov96⟩,
  ⟨13, tris97, tgt97, cov97⟩,
  ⟨15, tris98, tgt98, cov98⟩,
  ⟨0, tris99, tgt99, cov99⟩,
  ⟨1, tris100, tgt100, cov100⟩,
  ⟨3, tris101, tgt101, cov101⟩,
  ⟨5, tris102, tgt102, cov102⟩,
  ⟨6, tris103, tgt103, cov103⟩,
  ⟨8, tris104, tgt104, cov104⟩,
  ⟨9, tris105, tgt105, cov105⟩,
  ⟨11, tris106, tgt106, cov106⟩,
  ⟨12, tris107, tgt107, cov107⟩,
  ⟨13, tris108, tgt108, cov108⟩,
  ⟨15, tris109, tgt109, cov109⟩,
  ⟨0, tris110, tgt110, cov110⟩,
  ⟨1, tris111, tgt111, cov111⟩,
  ⟨3, tris112, tgt112, cov112⟩,
  ⟨5, tris113, tgt113, cov113⟩,
  ⟨6, tris114, tgt114, cov114⟩,
  ⟨8, tris115, tgt115, cov115⟩,
  ⟨9, tris116, tgt116, cov116⟩,
  ⟨11, tris117, tgt117, cov117⟩,
  ⟨12, tris118, tgt118, cov118⟩,
  ⟨13, tris119, tgt119, cov119⟩,
  ⟨15, tris120, tgt120, cov120⟩,
  ⟨0, tris121, tgt121, cov121⟩,
  ⟨1, tris122, tgt122, cov122⟩,
  ⟨3, tris123, tgt123, cov123⟩,
  ⟨5, tris124, tgt124, cov124⟩,
  ⟨6, tris125, tgt125, cov125⟩,
  ⟨8, tris126, tgt126, cov126⟩,
  ⟨9, tris127, tgt127, cov127⟩,
  ⟨11, tris128, tgt128, cov128⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨15, tris129, cov129⟩

lemma hJ : J = maskAt 1463 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1463) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1463
#print axioms SquarePacking.S11Opt.Split.U2R.C1463.excluded
