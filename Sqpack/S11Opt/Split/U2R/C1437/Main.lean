import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1437.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1411.B000
import Sqpack.S11Opt.Split.U2R.C1411.S4
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1597.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.B000
import Sqpack.S11Opt.Split.U2R.C1430.S21
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1436.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1436.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1437.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1437.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1437.B002
import Sqpack.S11Opt.Split.U2R.C1437.S33

namespace SquarePacking.S11Opt.Split.U2R.C1437
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
  ⟨7, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov5 (by decide +kernel))⟩,
  ⟨8, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov6 (by decide +kernel))⟩,
  ⟨12, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov8 (by decide +kernel))⟩,
  ⟨13, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov9 (by decide +kernel))⟩,
  ⟨15, tris9, tgt9, cov9⟩,
  ⟨0, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1597.cov9 (by decide +kernel))⟩,
  ⟨1, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov12 (by decide +kernel))⟩,
  ⟨3, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov13 (by decide +kernel))⟩,
  ⟨5, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov13 (by decide +kernel))⟩,
  ⟨6, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1436.cov14 (by decide +kernel))⟩,
  ⟨7, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1436.cov15 (by decide +kernel))⟩,
  ⟨8, tris16, tgt16,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov16 (by decide +kernel))⟩,
  ⟨10, tris17, tgt17, cov17⟩,
  ⟨12, tris18, tgt18,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov19 (by decide +kernel))⟩,
  ⟨13, tris19, tgt19, cov19⟩,
  ⟨15, tris20, tgt20, cov20⟩,
  ⟨0, tris21, tgt21,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov21 (by decide +kernel))⟩,
  ⟨1, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1436.cov19 (by decide +kernel))⟩,
  ⟨3, tris23, tgt23,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1436.cov20 (by decide +kernel))⟩,
  ⟨5, tris24, tgt24, cov24⟩,
  ⟨6, tris25, tgt25, cov25⟩,
  ⟨7, tris26, tgt26, cov26⟩,
  ⟨8, tris27, tgt27, cov27⟩,
  ⟨10, tris28, tgt28, cov28⟩,
  ⟨0, tris29, tgt29, cov29⟩,
  ⟨1, tris30, tgt30, cov30⟩,
  ⟨3, tris31, tgt31, cov31⟩,
  ⟨5, tris32, tgt32, cov32⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨6, tris33, cov33⟩

lemma hJ : J = maskAt 1437 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1437) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1437
#print axioms SquarePacking.S11Opt.Split.U2R.C1437.excluded
