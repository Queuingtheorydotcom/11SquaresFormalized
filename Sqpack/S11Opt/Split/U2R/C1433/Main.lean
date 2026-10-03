import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1433.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1411.B000
import Sqpack.S11Opt.Split.U2R.C1411.S4
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1597.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1422.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.B001
import Sqpack.S11Opt.Split.U2R.C1430.S21
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1433.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1433.B000
import Sqpack.S11Opt.Split.U2R.C1433.S23

namespace SquarePacking.S11Opt.Split.U2R.C1433
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
  ⟨11, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1422.cov8 (by decide +kernel))⟩,
  ⟨13, tris8, tgt8, cov8⟩,
  ⟨14, tris9, tgt9, cov9⟩,
  ⟨0, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1597.cov9 (by decide +kernel))⟩,
  ⟨1, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov12 (by decide +kernel))⟩,
  ⟨3, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov13 (by decide +kernel))⟩,
  ⟨5, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov13 (by decide +kernel))⟩,
  ⟨6, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov14 (by decide +kernel))⟩,
  ⟨7, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov15 (by decide +kernel))⟩,
  ⟨8, tris16, tgt16, cov16⟩,
  ⟨10, tris17, tgt17, cov17⟩,
  ⟨11, tris18, tgt18, cov18⟩,
  ⟨0, tris19, tgt19,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov21 (by decide +kernel))⟩,
  ⟨1, tris20, tgt20,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov22 (by decide +kernel))⟩,
  ⟨3, tris21, tgt21,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov23 (by decide +kernel))⟩,
  ⟨5, tris22, tgt22, cov22⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨6, tris23, cov23⟩

lemma hJ : J = maskAt 1433 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1433) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1433
#print axioms SquarePacking.S11Opt.Split.U2R.C1433.excluded
