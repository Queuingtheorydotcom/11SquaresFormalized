import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1499.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.B001
import Sqpack.S11Opt.Split.U2P.C763.S9
import Sqpack.S11Opt.Split.U2P.C2176.S6
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2176.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B020
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1484.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B026
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B012
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B008
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B014
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B016
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B020
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B015
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B024
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B019
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B017
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B010
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B018
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B027
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B025
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B023
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B022
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B009
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B021
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B011
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B007
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B013
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1499.B028

namespace SquarePacking.S11Opt.Split.U2R.C1499
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
  ⟨8, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨11, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov5 (by decide +kernel))⟩,
  ⟨12, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨13, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov6 (by decide +kernel))⟩,
  ⟨15, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov8 (by decide +kernel))⟩,
  ⟨0, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov9 (by decide +kernel))⟩,
  ⟨1, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1484.cov9 (by decide +kernel))⟩,
  ⟨3, tris9, tgt9, cov9⟩,
  ⟨6, tris10, tgt10, cov10⟩,
  ⟨8, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov10 (by decide +kernel))⟩,
  ⟨9, tris12, tgt12, cov12⟩,
  ⟨10, tris13, tgt13, cov13⟩,
  ⟨11, tris14, tgt14, cov14⟩,
  ⟨12, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov13 (by decide +kernel))⟩,
  ⟨13, tris16, tgt16, cov16⟩,
  ⟨15, tris17, tgt17, cov17⟩,
  ⟨6, tris18, tgt18, cov18⟩,
  ⟨8, tris19, tgt19, cov19⟩,
  ⟨9, tris20, tgt20, cov20⟩,
  ⟨10, tris21, tgt21, cov21⟩,
  ⟨11, tris22, tgt22, cov22⟩,
  ⟨12, tris23, tgt23, cov23⟩,
  ⟨13, tris24, tgt24, cov24⟩,
  ⟨15, tris25, tgt25, cov25⟩,
  ⟨0, tris26, tgt26, cov26⟩,
  ⟨1, tris27, tgt27, cov27⟩,
  ⟨3, tris28, tgt28, cov28⟩,
  ⟨6, tris29, tgt29, cov29⟩,
  ⟨8, tris30, tgt30, cov30⟩,
  ⟨9, tris31, tgt31, cov31⟩,
  ⟨10, tris32, tgt32, cov32⟩,
  ⟨11, tris33, tgt33, cov33⟩,
  ⟨12, tris34, tgt34, cov34⟩,
  ⟨13, tris35, tgt35, cov35⟩,
  ⟨15, tris36, tgt36, cov36⟩,
  ⟨0, tris37, tgt37, cov37⟩,
  ⟨1, tris38, tgt38, cov38⟩,
  ⟨3, tris39, tgt39, cov39⟩,
  ⟨6, tris40, tgt40, cov40⟩,
  ⟨8, tris41, tgt41, cov41⟩,
  ⟨9, tris42, tgt42, cov42⟩,
  ⟨10, tris43, tgt43, cov43⟩,
  ⟨11, tris44, tgt44, cov44⟩,
  ⟨12, tris45, tgt45, cov45⟩,
  ⟨13, tris46, tgt46, cov46⟩,
  ⟨15, tris47, tgt47, cov47⟩,
  ⟨0, tris48, tgt48, cov48⟩,
  ⟨1, tris49, tgt49, cov49⟩,
  ⟨3, tris50, tgt50, cov50⟩,
  ⟨6, tris51, tgt51, cov51⟩,
  ⟨8, tris52, tgt52, cov52⟩,
  ⟨9, tris53, tgt53, cov53⟩,
  ⟨10, tris54, tgt54, cov54⟩,
  ⟨11, tris55, tgt55, cov55⟩,
  ⟨12, tris56, tgt56, cov56⟩,
  ⟨13, tris57, tgt57, cov57⟩,
  ⟨15, tris58, tgt58, cov58⟩,
  ⟨0, tris59, tgt59, cov59⟩,
  ⟨1, tris60, tgt60, cov60⟩,
  ⟨3, tris61, tgt61, cov61⟩,
  ⟨6, tris62, tgt62, cov62⟩,
  ⟨8, tris63, tgt63, cov63⟩,
  ⟨9, tris64, tgt64, cov64⟩,
  ⟨10, tris65, tgt65, cov65⟩,
  ⟨11, tris66, tgt66, cov66⟩,
  ⟨12, tris67, tgt67, cov67⟩,
  ⟨13, tris68, tgt68, cov68⟩,
  ⟨15, tris69, tgt69, cov69⟩,
  ⟨0, tris70, tgt70, cov70⟩,
  ⟨1, tris71, tgt71, cov71⟩,
  ⟨3, tris72, tgt72, cov72⟩,
  ⟨6, tris73, tgt73, cov73⟩,
  ⟨8, tris74, tgt74, cov74⟩,
  ⟨9, tris75, tgt75, cov75⟩,
  ⟨10, tris76, tgt76, cov76⟩,
  ⟨11, tris77, tgt77, cov77⟩,
  ⟨12, tris78, tgt78, cov78⟩,
  ⟨15, tris79, tgt79, cov79⟩,
  ⟨0, tris80, tgt80, cov80⟩,
  ⟨1, tris81, tgt81, cov81⟩,
  ⟨3, tris82, tgt82, cov82⟩,
  ⟨6, tris83, tgt83, cov83⟩,
  ⟨8, tris84, tgt84, cov84⟩,
  ⟨9, tris85, tgt85, cov85⟩,
  ⟨10, tris86, tgt86, cov86⟩,
  ⟨11, tris87, tgt87, cov87⟩,
  ⟨12, tris88, tgt88, cov88⟩,
  ⟨13, tris89, tgt89, cov89⟩,
  ⟨15, tris90, tgt90, cov90⟩,
  ⟨0, tris91, tgt91, cov91⟩,
  ⟨1, tris92, tgt92, cov92⟩,
  ⟨3, tris93, tgt93, cov93⟩,
  ⟨6, tris94, tgt94, cov94⟩,
  ⟨8, tris95, tgt95, cov95⟩,
  ⟨9, tris96, tgt96, cov96⟩,
  ⟨10, tris97, tgt97, cov97⟩,
  ⟨11, tris98, tgt98, cov98⟩,
  ⟨12, tris99, tgt99, cov99⟩,
  ⟨13, tris100, tgt100, cov100⟩,
  ⟨15, tris101, tgt101, cov101⟩,
  ⟨0, tris102, tgt102, cov102⟩,
  ⟨1, tris103, tgt103, cov103⟩,
  ⟨3, tris104, tgt104, cov104⟩,
  ⟨6, tris105, tgt105, cov105⟩,
  ⟨8, tris106, tgt106, cov106⟩,
  ⟨9, tris107, tgt107, cov107⟩,
  ⟨10, tris108, tgt108, cov108⟩,
  ⟨11, tris109, tgt109, cov109⟩,
  ⟨12, tris110, tgt110, cov110⟩,
  ⟨13, tris111, tgt111, cov111⟩,
  ⟨15, tris112, tgt112, cov112⟩,
  ⟨0, tris113, tgt113, cov113⟩,
  ⟨1, tris114, tgt114, cov114⟩,
  ⟨3, tris115, tgt115, cov115⟩,
  ⟨6, tris116, tgt116, cov116⟩,
  ⟨8, tris117, tgt117, cov117⟩,
  ⟨9, tris118, tgt118, cov118⟩,
  ⟨10, tris119, tgt119, cov119⟩,
  ⟨11, tris120, tgt120, cov120⟩,
  ⟨12, tris121, tgt121, cov121⟩,
  ⟨13, tris122, tgt122, cov122⟩,
  ⟨15, tris123, tgt123, cov123⟩,
  ⟨0, tris124, tgt124, cov124⟩,
  ⟨1, tris125, tgt125, cov125⟩,
  ⟨3, tris126, tgt126, cov126⟩,
  ⟨6, tris127, tgt127, cov127⟩,
  ⟨8, tris128, tgt128, cov128⟩,
  ⟨9, tris129, tgt129, cov129⟩,
  ⟨10, tris130, tgt130, cov130⟩,
  ⟨11, tris131, tgt131, cov131⟩,
  ⟨12, tris132, tgt132, cov132⟩,
  ⟨13, tris133, tgt133, cov133⟩,
  ⟨15, tris134, tgt134, cov134⟩,
  ⟨0, tris135, tgt135, cov135⟩,
  ⟨1, tris136, tgt136, cov136⟩,
  ⟨3, tris137, tgt137, cov137⟩,
  ⟨6, tris138, tgt138, cov138⟩,
  ⟨8, tris139, tgt139, cov139⟩,
  ⟨9, tris140, tgt140, cov140⟩,
  ⟨10, tris141, tgt141, cov141⟩,
  ⟨11, tris142, tgt142, cov142⟩,
  ⟨0, tris143, tgt143, cov143⟩,
  ⟨1, tris144, tgt144, cov144⟩,
  ⟨3, tris145, tgt145, cov145⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨6, tris146, cov146⟩

lemma hJ : J = maskAt 1499 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1499) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1499
#print axioms SquarePacking.S11Opt.Split.U2R.C1499.excluded
