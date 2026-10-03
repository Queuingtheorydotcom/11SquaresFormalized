import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1696.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B018
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1674.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1695.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1695.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1695.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1695.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1696.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1696.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1696.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1696.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1696.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1696.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1696.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1696.B007

namespace SquarePacking.S11Opt.Split.U2R.C1696
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
  ⟨11, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1673.cov8 (by decide +kernel))⟩,
  ⟨12, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov6 (by decide +kernel))⟩,
  ⟨13, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov7 (by decide +kernel))⟩,
  ⟨15, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1674.cov9 (by decide +kernel))⟩,
  ⟨0, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1673.cov12 (by decide +kernel))⟩,
  ⟨3, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1673.cov13 (by decide +kernel))⟩,
  ⟨4, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1695.cov13 (by decide +kernel))⟩,
  ⟨5, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1695.cov14 (by decide +kernel))⟩,
  ⟨6, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1695.cov15 (by decide +kernel))⟩,
  ⟨10, tris16, tgt16, cov16⟩,
  ⟨11, tris17, tgt17, cov17⟩,
  ⟨12, tris18, tgt18, cov18⟩,
  ⟨13, tris19, tgt19, cov19⟩,
  ⟨15, tris20, tgt20, cov20⟩,
  ⟨0, tris21, tgt21,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1695.cov21 (by decide +kernel))⟩,
  ⟨2, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1695.cov22 (by decide +kernel))⟩,
  ⟨3, tris23, tgt23,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1695.cov23 (by decide +kernel))⟩,
  ⟨4, tris24, tgt24,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1695.cov24 (by decide +kernel))⟩,
  ⟨5, tris25, tgt25, cov25⟩,
  ⟨6, tris26, tgt26, cov26⟩,
  ⟨10, tris27, tgt27, cov27⟩,
  ⟨11, tris28, tgt28, cov28⟩,
  ⟨12, tris29, tgt29, cov29⟩,
  ⟨13, tris30, tgt30, cov30⟩,
  ⟨15, tris31, tgt31, cov31⟩,
  ⟨0, tris32, tgt32, cov32⟩,
  ⟨2, tris33, tgt33, cov33⟩,
  ⟨3, tris34, tgt34, cov34⟩,
  ⟨4, tris35, tgt35, cov35⟩,
  ⟨5, tris36, tgt36, cov36⟩,
  ⟨6, tris37, tgt37, cov37⟩,
  ⟨10, tris38, tgt38, cov38⟩,
  ⟨11, tris39, tgt39, cov39⟩,
  ⟨12, tris40, tgt40, cov40⟩,
  ⟨13, tris41, tgt41, cov41⟩,
  ⟨15, tris42, tgt42, cov42⟩,
  ⟨0, tris43, tgt43, cov43⟩,
  ⟨2, tris44, tgt44, cov44⟩,
  ⟨3, tris45, tgt45, cov45⟩,
  ⟨4, tris46, tgt46, cov46⟩,
  ⟨5, tris47, tgt47, cov47⟩,
  ⟨6, tris48, tgt48, cov48⟩,
  ⟨10, tris49, tgt49, cov49⟩,
  ⟨0, tris50, tgt50, cov50⟩,
  ⟨2, tris51, tgt51, cov51⟩,
  ⟨4, tris52, tgt52, cov52⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, tris53, cov53⟩

lemma hJ : J = maskAt 1696 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1696) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1696
#print axioms SquarePacking.S11Opt.Split.U2R.C1696.excluded
