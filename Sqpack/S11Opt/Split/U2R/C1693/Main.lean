import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1693.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1636.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1640.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1636.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1650.B000
import Sqpack.S11Opt.Split.U2R.C1650.S10
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1686.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1686.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1693.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1693.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1693.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1693.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1693.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1693.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1693.B000
import Sqpack.S11Opt.Split.U2R.C1693.S46

namespace SquarePacking.S11Opt.Split.U2R.C1693
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
  ⟨14, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1650.cov10 (by decide +kernel))⟩,
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
  ⟨6, tris16, tgt16, cov16⟩,
  ⟨9, tris17, tgt17, cov17⟩,
  ⟨11, tris18, tgt18, cov18⟩,
  ⟨12, tris19, tgt19, cov19⟩,
  ⟨13, tris20, tgt20, cov20⟩,
  ⟨14, tris21, tgt21, cov21⟩,
  ⟨0, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1686.cov22 (by decide +kernel))⟩,
  ⟨2, tris23, tgt23, cov23⟩,
  ⟨3, tris24, tgt24, cov24⟩,
  ⟨4, tris25, tgt25, cov25⟩,
  ⟨5, tris26, tgt26, cov26⟩,
  ⟨6, tris27, tgt27, cov27⟩,
  ⟨9, tris28, tgt28, cov28⟩,
  ⟨11, tris29, tgt29, cov29⟩,
  ⟨12, tris30, tgt30, cov30⟩,
  ⟨13, tris31, tgt31, cov31⟩,
  ⟨14, tris32, tgt32, cov32⟩,
  ⟨0, tris33, tgt33, cov33⟩,
  ⟨2, tris34, tgt34, cov34⟩,
  ⟨3, tris35, tgt35, cov35⟩,
  ⟨4, tris36, tgt36, cov36⟩,
  ⟨5, tris37, tgt37, cov37⟩,
  ⟨6, tris38, tgt38, cov38⟩,
  ⟨9, tris39, tgt39, cov39⟩,
  ⟨11, tris40, tgt40, cov40⟩,
  ⟨0, tris41, tgt41, cov41⟩,
  ⟨2, tris42, tgt42, cov42⟩,
  ⟨3, tris43, tgt43, cov43⟩,
  ⟨4, tris44, tgt44, cov44⟩,
  ⟨5, tris45, tgt45, cov45⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨6, tris46, cov46⟩

lemma hJ : J = maskAt 1693 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1693) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1693
#print axioms SquarePacking.S11Opt.Split.U2R.C1693.excluded
