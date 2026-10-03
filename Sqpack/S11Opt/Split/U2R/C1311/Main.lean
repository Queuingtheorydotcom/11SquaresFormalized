import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B039
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B007
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B044
import Sqpack.S11Opt.Split.U2R.C1311.S4
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B043
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B013
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B027
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B014
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B017
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B025
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B032
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B031
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B050
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B018
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B035
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B023
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B024
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B034
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B026
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B030
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B019
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B038
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B048
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B052
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B012
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B008
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B051
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B042
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B015
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B047
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B037
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B010
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B029
import Sqpack.S11Opt.Split.U2R.C1311.S53
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B046
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B028
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B036
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B009
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B053
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B022
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B049
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B021
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B045
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B033
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B040
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B016
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B020
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B041
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B011
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1311.B004
import Sqpack.S11Opt.Split.U2R.C1311.S169

namespace SquarePacking.S11Opt.Split.U2R.C1311
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨0, tris0, tgt0, cov0⟩,
  ⟨1, tris1, tgt1, cov1⟩,
  ⟨3, tris2, tgt2, cov2⟩,
  ⟨4, tris3, tgt3, cov3⟩,
  ⟨5, tris4, tgt4, cov4⟩,
  ⟨7, tris5, tgt5, cov5⟩,
  ⟨9, tris6, tgt6, cov6⟩,
  ⟨10, tris7, tgt7, cov7⟩,
  ⟨12, tris8, tgt8, cov8⟩,
  ⟨14, tris9, tgt9, cov9⟩,
  ⟨15, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11, cov11⟩,
  ⟨1, tris12, tgt12, cov12⟩,
  ⟨3, tris13, tgt13, cov13⟩,
  ⟨4, tris14, tgt14, cov14⟩,
  ⟨5, tris15, tgt15, cov15⟩,
  ⟨7, tris16, tgt16, cov16⟩,
  ⟨9, tris17, tgt17, cov17⟩,
  ⟨10, tris18, tgt18, cov18⟩,
  ⟨12, tris19, tgt19, cov19⟩,
  ⟨14, tris20, tgt20, cov20⟩,
  ⟨15, tris21, tgt21, cov21⟩,
  ⟨0, tris22, tgt22, cov22⟩,
  ⟨1, tris23, tgt23, cov23⟩,
  ⟨3, tris24, tgt24, cov24⟩,
  ⟨4, tris25, tgt25, cov25⟩,
  ⟨5, tris26, tgt26, cov26⟩,
  ⟨7, tris27, tgt27, cov27⟩,
  ⟨9, tris28, tgt28, cov28⟩,
  ⟨10, tris29, tgt29, cov29⟩,
  ⟨12, tris30, tgt30, cov30⟩,
  ⟨14, tris31, tgt31, cov31⟩,
  ⟨15, tris32, tgt32, cov32⟩,
  ⟨0, tris33, tgt33, cov33⟩,
  ⟨1, tris34, tgt34, cov34⟩,
  ⟨3, tris35, tgt35, cov35⟩,
  ⟨4, tris36, tgt36, cov36⟩,
  ⟨5, tris37, tgt37, cov37⟩,
  ⟨7, tris38, tgt38, cov38⟩,
  ⟨9, tris39, tgt39, cov39⟩,
  ⟨10, tris40, tgt40, cov40⟩,
  ⟨12, tris41, tgt41, cov41⟩,
  ⟨14, tris42, tgt42, cov42⟩,
  ⟨15, tris43, tgt43, cov43⟩,
  ⟨0, tris44, tgt44, cov44⟩,
  ⟨1, tris45, tgt45, cov45⟩,
  ⟨3, tris46, tgt46, cov46⟩,
  ⟨4, tris47, tgt47, cov47⟩,
  ⟨5, tris48, tgt48, cov48⟩,
  ⟨7, tris49, tgt49, cov49⟩,
  ⟨9, tris50, tgt50, cov50⟩,
  ⟨10, tris51, tgt51, cov51⟩,
  ⟨12, tris52, tgt52, cov52⟩,
  ⟨14, tris53, tgt53, cov53⟩,
  ⟨15, tris54, tgt54, cov54⟩,
  ⟨0, tris55, tgt55, cov55⟩,
  ⟨1, tris56, tgt56, cov56⟩,
  ⟨3, tris57, tgt57, cov57⟩,
  ⟨4, tris58, tgt58, cov58⟩,
  ⟨5, tris59, tgt59, cov59⟩,
  ⟨7, tris60, tgt60, cov60⟩,
  ⟨9, tris61, tgt61, cov61⟩,
  ⟨10, tris62, tgt62, cov62⟩,
  ⟨12, tris63, tgt63, cov63⟩,
  ⟨14, tris64, tgt64, cov64⟩,
  ⟨15, tris65, tgt65, cov65⟩,
  ⟨0, tris66, tgt66, cov66⟩,
  ⟨1, tris67, tgt67, cov67⟩,
  ⟨4, tris68, tgt68, cov68⟩,
  ⟨5, tris69, tgt69, cov69⟩,
  ⟨7, tris70, tgt70, cov70⟩,
  ⟨9, tris71, tgt71, cov71⟩,
  ⟨10, tris72, tgt72, cov72⟩,
  ⟨12, tris73, tgt73, cov73⟩,
  ⟨14, tris74, tgt74, cov74⟩,
  ⟨15, tris75, tgt75, cov75⟩,
  ⟨0, tris76, tgt76, cov76⟩,
  ⟨1, tris77, tgt77, cov77⟩,
  ⟨3, tris78, tgt78, cov78⟩,
  ⟨4, tris79, tgt79, cov79⟩,
  ⟨5, tris80, tgt80, cov80⟩,
  ⟨7, tris81, tgt81, cov81⟩,
  ⟨9, tris82, tgt82, cov82⟩,
  ⟨10, tris83, tgt83, cov83⟩,
  ⟨12, tris84, tgt84, cov84⟩,
  ⟨14, tris85, tgt85, cov85⟩,
  ⟨15, tris86, tgt86, cov86⟩,
  ⟨0, tris87, tgt87, cov87⟩,
  ⟨1, tris88, tgt88, cov88⟩,
  ⟨4, tris89, tgt89, cov89⟩,
  ⟨5, tris90, tgt90, cov90⟩,
  ⟨7, tris91, tgt91, cov91⟩,
  ⟨9, tris92, tgt92, cov92⟩,
  ⟨10, tris93, tgt93, cov93⟩,
  ⟨12, tris94, tgt94, cov94⟩,
  ⟨14, tris95, tgt95, cov95⟩,
  ⟨15, tris96, tgt96, cov96⟩,
  ⟨0, tris97, tgt97, cov97⟩,
  ⟨1, tris98, tgt98, cov98⟩,
  ⟨3, tris99, tgt99, cov99⟩,
  ⟨4, tris100, tgt100, cov100⟩,
  ⟨5, tris101, tgt101, cov101⟩,
  ⟨7, tris102, tgt102, cov102⟩,
  ⟨9, tris103, tgt103, cov103⟩,
  ⟨10, tris104, tgt104, cov104⟩,
  ⟨14, tris105, tgt105, cov105⟩,
  ⟨15, tris106, tgt106, cov106⟩,
  ⟨0, tris107, tgt107, cov107⟩,
  ⟨1, tris108, tgt108, cov108⟩,
  ⟨3, tris109, tgt109, cov109⟩,
  ⟨4, tris110, tgt110, cov110⟩,
  ⟨5, tris111, tgt111, cov111⟩,
  ⟨7, tris112, tgt112, cov112⟩,
  ⟨9, tris113, tgt113, cov113⟩,
  ⟨10, tris114, tgt114, cov114⟩,
  ⟨14, tris115, tgt115, cov115⟩,
  ⟨0, tris116, tgt116, cov116⟩,
  ⟨1, tris117, tgt117, cov117⟩,
  ⟨3, tris118, tgt118, cov118⟩,
  ⟨4, tris119, tgt119, cov119⟩,
  ⟨5, tris120, tgt120, cov120⟩,
  ⟨9, tris121, tgt121, cov121⟩,
  ⟨10, tris122, tgt122, cov122⟩,
  ⟨12, tris123, tgt123, cov123⟩,
  ⟨14, tris124, tgt124, cov124⟩,
  ⟨15, tris125, tgt125, cov125⟩,
  ⟨0, tris126, tgt126, cov126⟩,
  ⟨1, tris127, tgt127, cov127⟩,
  ⟨4, tris128, tgt128, cov128⟩,
  ⟨5, tris129, tgt129, cov129⟩,
  ⟨7, tris130, tgt130, cov130⟩,
  ⟨9, tris131, tgt131, cov131⟩,
  ⟨10, tris132, tgt132, cov132⟩,
  ⟨12, tris133, tgt133, cov133⟩,
  ⟨14, tris134, tgt134, cov134⟩,
  ⟨15, tris135, tgt135, cov135⟩,
  ⟨0, tris136, tgt136, cov136⟩,
  ⟨1, tris137, tgt137, cov137⟩,
  ⟨3, tris138, tgt138, cov138⟩,
  ⟨4, tris139, tgt139, cov139⟩,
  ⟨5, tris140, tgt140, cov140⟩,
  ⟨7, tris141, tgt141, cov141⟩,
  ⟨9, tris142, tgt142, cov142⟩,
  ⟨10, tris143, tgt143, cov143⟩,
  ⟨12, tris144, tgt144, cov144⟩,
  ⟨14, tris145, tgt145, cov145⟩,
  ⟨15, tris146, tgt146, cov146⟩,
  ⟨0, tris147, tgt147, cov147⟩,
  ⟨1, tris148, tgt148, cov148⟩,
  ⟨3, tris149, tgt149, cov149⟩,
  ⟨4, tris150, tgt150, cov150⟩,
  ⟨5, tris151, tgt151, cov151⟩,
  ⟨7, tris152, tgt152, cov152⟩,
  ⟨9, tris153, tgt153, cov153⟩,
  ⟨10, tris154, tgt154, cov154⟩,
  ⟨12, tris155, tgt155, cov155⟩,
  ⟨14, tris156, tgt156, cov156⟩,
  ⟨15, tris157, tgt157, cov157⟩,
  ⟨0, tris158, tgt158, cov158⟩,
  ⟨1, tris159, tgt159, cov159⟩,
  ⟨3, tris160, tgt160, cov160⟩,
  ⟨4, tris161, tgt161, cov161⟩,
  ⟨5, tris162, tgt162, cov162⟩,
  ⟨7, tris163, tgt163, cov163⟩,
  ⟨9, tris164, tgt164, cov164⟩,
  ⟨10, tris165, tgt165, cov165⟩,
  ⟨0, tris166, tgt166, cov166⟩,
  ⟨1, tris167, tgt167, cov167⟩,
  ⟨4, tris168, tgt168, cov168⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, tris169, cov169⟩

lemma hJ : J = maskAt 1311 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1311) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1311
#print axioms SquarePacking.S11Opt.Split.U2R.C1311.excluded
