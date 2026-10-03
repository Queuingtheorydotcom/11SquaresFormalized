import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1840.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.B001
import Sqpack.S11Opt.Split.U2P.C2176.S6
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C654.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1840.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1840.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1840.B008
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1840.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1840.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1840.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1840.B007
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1840.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1840.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1840.B009
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1840.B010

namespace SquarePacking.S11Opt.Split.U2R.C1840
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
  ⟨5, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov3 (by decide +kernel))⟩,
  ⟨6, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov4 (by decide +kernel))⟩,
  ⟨8, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨11, tris6, tgt6, cov6⟩,
  ⟨12, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨13, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov6 (by decide +kernel))⟩,
  ⟨14, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C654.cov9 (by decide +kernel))⟩,
  ⟨0, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov9 (by decide +kernel))⟩,
  ⟨2, tris11, tgt11, cov11⟩,
  ⟨3, tris12, tgt12, cov12⟩,
  ⟨5, tris13, tgt13, cov13⟩,
  ⟨6, tris14, tgt14, cov14⟩,
  ⟨8, tris15, tgt15, cov15⟩,
  ⟨10, tris16, tgt16, cov16⟩,
  ⟨11, tris17, tgt17, cov17⟩,
  ⟨12, tris18, tgt18, cov18⟩,
  ⟨13, tris19, tgt19, cov19⟩,
  ⟨14, tris20, tgt20, cov20⟩,
  ⟨0, tris21, tgt21, cov21⟩,
  ⟨2, tris22, tgt22, cov22⟩,
  ⟨3, tris23, tgt23, cov23⟩,
  ⟨5, tris24, tgt24, cov24⟩,
  ⟨6, tris25, tgt25, cov25⟩,
  ⟨8, tris26, tgt26, cov26⟩,
  ⟨10, tris27, tgt27, cov27⟩,
  ⟨11, tris28, tgt28, cov28⟩,
  ⟨12, tris29, tgt29, cov29⟩,
  ⟨13, tris30, tgt30, cov30⟩,
  ⟨14, tris31, tgt31, cov31⟩,
  ⟨0, tris32, tgt32, cov32⟩,
  ⟨2, tris33, tgt33, cov33⟩,
  ⟨3, tris34, tgt34, cov34⟩,
  ⟨5, tris35, tgt35, cov35⟩,
  ⟨6, tris36, tgt36, cov36⟩,
  ⟨8, tris37, tgt37, cov37⟩,
  ⟨10, tris38, tgt38, cov38⟩,
  ⟨11, tris39, tgt39, cov39⟩,
  ⟨12, tris40, tgt40, cov40⟩,
  ⟨13, tris41, tgt41, cov41⟩,
  ⟨14, tris42, tgt42, cov42⟩,
  ⟨0, tris43, tgt43, cov43⟩,
  ⟨2, tris44, tgt44, cov44⟩,
  ⟨3, tris45, tgt45, cov45⟩,
  ⟨5, tris46, tgt46, cov46⟩,
  ⟨6, tris47, tgt47, cov47⟩,
  ⟨8, tris48, tgt48, cov48⟩,
  ⟨10, tris49, tgt49, cov49⟩,
  ⟨11, tris50, tgt50, cov50⟩,
  ⟨12, tris51, tgt51, cov51⟩,
  ⟨13, tris52, tgt52, cov52⟩,
  ⟨14, tris53, tgt53, cov53⟩,
  ⟨0, tris54, tgt54, cov54⟩,
  ⟨2, tris55, tgt55, cov55⟩,
  ⟨3, tris56, tgt56, cov56⟩,
  ⟨5, tris57, tgt57, cov57⟩,
  ⟨6, tris58, tgt58, cov58⟩,
  ⟨8, tris59, tgt59, cov59⟩,
  ⟨10, tris60, tgt60, cov60⟩,
  ⟨12, tris61, tgt61, cov61⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨13, tris62, cov62⟩

lemma hJ : J = maskAt 1840 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1840) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1840
#print axioms SquarePacking.S11Opt.Split.U2R.C1840.excluded
