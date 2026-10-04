import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2G.C2095.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages001
import Sqpack.S11Opt.Split.U2R.C2084.S4
import Sqpack.S11Opt.Split.U2R.C2084.S5
import Sqpack.S11Opt.Split.U2R.C2091.S8
import Sqpack.S11Opt.Split.U2R.C2094.S13
import Sqpack.S11Opt.Split.U2R.C2094.S14
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C2095.SharedStages000
import Sqpack.S11Opt.Split.U2G.C2095.S12

namespace SquarePacking.S11Opt.Split.U2G.C2095
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨1, (traceTriangles 0), (traceTargets 0),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov0 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 1), (traceTargets 1),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov1 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 2), (traceTargets 2),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov2 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2084.cov4 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2084.cov5 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2091.cov8 (by decide +kernel))⟩,
  ⟨14, (traceTriangles 6), (traceTargets 6), cov6⟩,
  ⟨1, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨2, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨3, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨6, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2094.cov13 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2094.cov14 (by decide +kernel))⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, (traceTriangles 12), cov12⟩

lemma hJ : J = maskAt 2095 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2095) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2G.C2095
#print axioms SquarePacking.S11Opt.Split.U2G.C2095.excluded
