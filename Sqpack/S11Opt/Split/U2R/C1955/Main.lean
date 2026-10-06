import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1955.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1950.S3
import Sqpack.S11Opt.Split.U2R.C1950.S4
import Sqpack.S11Opt.Split.U2R.C1950.S5
import Sqpack.S11Opt.Split.U2R.C1950.S6
import Sqpack.S11Opt.Split.U2R.C1950.S9
import Sqpack.S11Opt.Split.U2R.C1955.S7
import Sqpack.S11Opt.Split.U2R.C1955.S9
import Sqpack.S11Opt.Split.U2R.C1955.S10

namespace SquarePacking.S11Opt.Split.U2R.C1955
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨0, (traceTriangles 0), (traceTargets 0),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov0 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 1), (traceTargets 1),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov1 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 2), (traceTargets 2),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov3 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1950.cov3 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1950.cov4 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1950.cov5 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1950.cov6 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨12, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1950.cov9 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 9), (traceTargets 9), cov9⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨14, (traceTriangles 10), cov10⟩

lemma hJ : J = maskAt 1955 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1955) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1955
#print axioms SquarePacking.S11Opt.Split.U2R.C1955.excluded
