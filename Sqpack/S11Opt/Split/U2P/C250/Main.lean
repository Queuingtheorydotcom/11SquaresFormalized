import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C250.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Split.U2P.C247.S9
import Sqpack.S11Opt.Split.U2P.C247.S10

namespace SquarePacking.S11Opt.Split.U2P.C250
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
  ⟨5, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov5 (by decide +kernel))⟩,
  ⟨0, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov7 (by decide +kernel))⟩,
  ⟨1, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov8 (by decide +kernel))⟩,
  ⟨2, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov9 (by decide +kernel))⟩,
  ⟨4, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C247.cov9 (by decide +kernel))⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, tris10, (CovF.weaken SquarePacking.S11Opt.Split.U2P.C247.cov10 (by decide +kernel))⟩

lemma hJ : J = maskAt 250 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 250) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C250
#print axioms SquarePacking.S11Opt.Split.U2P.C250.excluded
