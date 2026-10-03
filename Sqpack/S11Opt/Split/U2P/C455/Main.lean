import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C455.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C439.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B018
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B020
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B014
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B021
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B017
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B012
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B009
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B013
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B022
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B015
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B019
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B008
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B023
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B016
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B010
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B007
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B011
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B000

namespace SquarePacking.S11Opt.Split.U2P.C455
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
  ⟨2, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov2 (by decide +kernel))⟩,
  ⟨3, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov3 (by decide +kernel))⟩,
  ⟨4, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov4 (by decide +kernel))⟩,
  ⟨11, tris5, tgt5, cov5⟩,
  ⟨12, tris6, tgt6, cov6⟩,
  ⟨13, tris7, tgt7, cov7⟩,
  ⟨15, tris8, tgt8, cov8⟩,
  ⟨0, tris9, tgt9, cov9⟩,
  ⟨1, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C439.cov11 (by decide +kernel))⟩,
  ⟨2, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C439.cov12 (by decide +kernel))⟩,
  ⟨3, tris12, tgt12, cov12⟩,
  ⟨4, tris13, tgt13, cov13⟩,
  ⟨9, tris14, tgt14, cov14⟩,
  ⟨10, tris15, tgt15, cov15⟩,
  ⟨11, tris16, tgt16, cov16⟩,
  ⟨12, tris17, tgt17, cov17⟩,
  ⟨13, tris18, tgt18, cov18⟩,
  ⟨15, tris19, tgt19, cov19⟩,
  ⟨0, tris20, tgt20, cov20⟩,
  ⟨1, tris21, tgt21, cov21⟩,
  ⟨2, tris22, tgt22, cov22⟩,
  ⟨3, tris23, tgt23, cov23⟩,
  ⟨4, tris24, tgt24, cov24⟩,
  ⟨9, tris25, tgt25, cov25⟩,
  ⟨10, tris26, tgt26, cov26⟩,
  ⟨11, tris27, tgt27, cov27⟩,
  ⟨12, tris28, tgt28, cov28⟩,
  ⟨13, tris29, tgt29, cov29⟩,
  ⟨15, tris30, tgt30, cov30⟩,
  ⟨0, tris31, tgt31, cov31⟩,
  ⟨1, tris32, tgt32, cov32⟩,
  ⟨2, tris33, tgt33, cov33⟩,
  ⟨3, tris34, tgt34, cov34⟩,
  ⟨4, tris35, tgt35, cov35⟩,
  ⟨9, tris36, tgt36, cov36⟩,
  ⟨10, tris37, tgt37, cov37⟩,
  ⟨11, tris38, tgt38, cov38⟩,
  ⟨12, tris39, tgt39, cov39⟩,
  ⟨13, tris40, tgt40, cov40⟩,
  ⟨15, tris41, tgt41, cov41⟩,
  ⟨0, tris42, tgt42, cov42⟩,
  ⟨1, tris43, tgt43, cov43⟩,
  ⟨2, tris44, tgt44, cov44⟩,
  ⟨3, tris45, tgt45, cov45⟩,
  ⟨4, tris46, tgt46, cov46⟩,
  ⟨9, tris47, tgt47, cov47⟩,
  ⟨10, tris48, tgt48, cov48⟩,
  ⟨11, tris49, tgt49, cov49⟩,
  ⟨12, tris50, tgt50, cov50⟩,
  ⟨13, tris51, tgt51, cov51⟩,
  ⟨15, tris52, tgt52, cov52⟩,
  ⟨0, tris53, tgt53, cov53⟩,
  ⟨1, tris54, tgt54, cov54⟩,
  ⟨2, tris55, tgt55, cov55⟩,
  ⟨3, tris56, tgt56, cov56⟩,
  ⟨4, tris57, tgt57, cov57⟩,
  ⟨9, tris58, tgt58, cov58⟩,
  ⟨10, tris59, tgt59, cov59⟩,
  ⟨11, tris60, tgt60, cov60⟩,
  ⟨12, tris61, tgt61, cov61⟩,
  ⟨13, tris62, tgt62, cov62⟩,
  ⟨15, tris63, tgt63, cov63⟩,
  ⟨0, tris64, tgt64, cov64⟩,
  ⟨2, tris65, tgt65, cov65⟩,
  ⟨4, tris66, tgt66, cov66⟩,
  ⟨9, tris67, tgt67, cov67⟩,
  ⟨10, tris68, tgt68, cov68⟩,
  ⟨11, tris69, tgt69, cov69⟩,
  ⟨12, tris70, tgt70, cov70⟩,
  ⟨13, tris71, tgt71, cov71⟩,
  ⟨15, tris72, tgt72, cov72⟩,
  ⟨0, tris73, tgt73, cov73⟩,
  ⟨1, tris74, tgt74, cov74⟩,
  ⟨2, tris75, tgt75, cov75⟩,
  ⟨3, tris76, tgt76, cov76⟩,
  ⟨4, tris77, tgt77, cov77⟩,
  ⟨9, tris78, tgt78, cov78⟩,
  ⟨10, tris79, tgt79, cov79⟩,
  ⟨11, tris80, tgt80, cov80⟩,
  ⟨12, tris81, tgt81, cov81⟩,
  ⟨13, tris82, tgt82, cov82⟩,
  ⟨15, tris83, tgt83, cov83⟩,
  ⟨0, tris84, tgt84, cov84⟩,
  ⟨1, tris85, tgt85, cov85⟩,
  ⟨2, tris86, tgt86, cov86⟩,
  ⟨3, tris87, tgt87, cov87⟩,
  ⟨4, tris88, tgt88, cov88⟩,
  ⟨9, tris89, tgt89, cov89⟩,
  ⟨10, tris90, tgt90, cov90⟩,
  ⟨11, tris91, tgt91, cov91⟩,
  ⟨12, tris92, tgt92, cov92⟩,
  ⟨13, tris93, tgt93, cov93⟩,
  ⟨15, tris94, tgt94, cov94⟩,
  ⟨0, tris95, tgt95, cov95⟩,
  ⟨1, tris96, tgt96, cov96⟩,
  ⟨2, tris97, tgt97, cov97⟩,
  ⟨3, tris98, tgt98, cov98⟩,
  ⟨4, tris99, tgt99, cov99⟩,
  ⟨9, tris100, tgt100, cov100⟩,
  ⟨10, tris101, tgt101, cov101⟩,
  ⟨11, tris102, tgt102, cov102⟩,
  ⟨12, tris103, tgt103, cov103⟩,
  ⟨13, tris104, tgt104, cov104⟩,
  ⟨15, tris105, tgt105, cov105⟩,
  ⟨0, tris106, tgt106, cov106⟩,
  ⟨1, tris107, tgt107, cov107⟩,
  ⟨2, tris108, tgt108, cov108⟩,
  ⟨3, tris109, tgt109, cov109⟩,
  ⟨4, tris110, tgt110, cov110⟩,
  ⟨9, tris111, tgt111, cov111⟩,
  ⟨10, tris112, tgt112, cov112⟩,
  ⟨11, tris113, tgt113, cov113⟩,
  ⟨12, tris114, tgt114, cov114⟩,
  ⟨13, tris115, tgt115, cov115⟩,
  ⟨15, tris116, tgt116, cov116⟩,
  ⟨0, tris117, tgt117, cov117⟩,
  ⟨1, tris118, tgt118, cov118⟩,
  ⟨2, tris119, tgt119, cov119⟩,
  ⟨3, tris120, tgt120, cov120⟩,
  ⟨4, tris121, tgt121, cov121⟩,
  ⟨9, tris122, tgt122, cov122⟩,
  ⟨10, tris123, tgt123, cov123⟩,
  ⟨11, tris124, tgt124, cov124⟩,
  ⟨12, tris125, tgt125, cov125⟩,
  ⟨13, tris126, tgt126, cov126⟩,
  ⟨15, tris127, tgt127, cov127⟩,
  ⟨0, tris128, tgt128, cov128⟩,
  ⟨1, tris129, tgt129, cov129⟩,
  ⟨2, tris130, tgt130, cov130⟩,
  ⟨4, tris131, tgt131, cov131⟩,
  ⟨9, tris132, tgt132, cov132⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris133, cov133⟩

lemma hJ : J = maskAt 455 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 455) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C455
#print axioms SquarePacking.S11Opt.Split.U2P.C455.excluded
