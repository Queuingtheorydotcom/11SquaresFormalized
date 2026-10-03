import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1636.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1640.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1636.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1636.B001
import Sqpack.S11Opt.Split.U2R.C1636.S18

namespace SquarePacking.S11Opt.Split.U2R.C1636
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
  ⟨7, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov6 (by decide +kernel))⟩,
  ⟨9, tris7, tgt7, cov7⟩,
  ⟨10, tris8, tgt8, cov8⟩,
  ⟨11, tris9, tgt9, cov9⟩,
  ⟨12, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1640.cov9 (by decide +kernel))⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov11 (by decide +kernel))⟩,
  ⟨3, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov12 (by decide +kernel))⟩,
  ⟨4, tris14, tgt14, cov14⟩,
  ⟨5, tris15, tgt15, cov15⟩,
  ⟨6, tris16, tgt16, cov16⟩,
  ⟨9, tris17, tgt17, cov17⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris18, cov18⟩

lemma hJ : J = maskAt 1636 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1636) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1636
#print axioms SquarePacking.S11Opt.Split.U2R.C1636.excluded
