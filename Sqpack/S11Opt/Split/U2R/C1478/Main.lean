import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1478.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1335.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1347.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1411.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1597.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1476.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1476.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.B006
import Sqpack.S11Opt.Split.U2R.C1478.S40

namespace SquarePacking.S11Opt.Split.U2R.C1478
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
  ⟨7, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov4 (by decide +kernel))⟩,
  ⟨8, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov6 (by decide +kernel))⟩,
  ⟨11, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1347.cov7 (by decide +kernel))⟩,
  ⟨12, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov8 (by decide +kernel))⟩,
  ⟨13, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov9 (by decide +kernel))⟩,
  ⟨14, tris9, tgt9, cov9⟩,
  ⟨0, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1597.cov9 (by decide +kernel))⟩,
  ⟨1, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov12 (by decide +kernel))⟩,
  ⟨3, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1476.cov13 (by decide +kernel))⟩,
  ⟨5, tris13, tgt13, cov13⟩,
  ⟨7, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1476.cov15 (by decide +kernel))⟩,
  ⟨8, tris15, tgt15, cov15⟩,
  ⟨10, tris16, tgt16, cov16⟩,
  ⟨11, tris17, tgt17, cov17⟩,
  ⟨12, tris18, tgt18, cov18⟩,
  ⟨13, tris19, tgt19, cov19⟩,
  ⟨14, tris20, tgt20, cov20⟩,
  ⟨3, tris21, tgt21, cov21⟩,
  ⟨5, tris22, tgt22, cov22⟩,
  ⟨7, tris23, tgt23, cov23⟩,
  ⟨8, tris24, tgt24, cov24⟩,
  ⟨10, tris25, tgt25, cov25⟩,
  ⟨11, tris26, tgt26, cov26⟩,
  ⟨12, tris27, tgt27, cov27⟩,
  ⟨13, tris28, tgt28, cov28⟩,
  ⟨14, tris29, tgt29, cov29⟩,
  ⟨0, tris30, tgt30, cov30⟩,
  ⟨1, tris31, tgt31, cov31⟩,
  ⟨3, tris32, tgt32, cov32⟩,
  ⟨5, tris33, tgt33, cov33⟩,
  ⟨7, tris34, tgt34, cov34⟩,
  ⟨8, tris35, tgt35, cov35⟩,
  ⟨10, tris36, tgt36, cov36⟩,
  ⟨11, tris37, tgt37, cov37⟩,
  ⟨12, tris38, tgt38, cov38⟩,
  ⟨13, tris39, tgt39, cov39⟩,
  ⟨14, tris40, tgt40, cov40⟩,
  ⟨0, tris41, tgt41, cov41⟩,
  ⟨1, tris42, tgt42, cov42⟩,
  ⟨3, tris43, tgt43, cov43⟩,
  ⟨5, tris44, tgt44, cov44⟩,
  ⟨7, tris45, tgt45, cov45⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris46, cov46⟩

lemma hJ : J = maskAt 1478 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1478) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1478
#print axioms SquarePacking.S11Opt.Split.U2R.C1478.excluded
