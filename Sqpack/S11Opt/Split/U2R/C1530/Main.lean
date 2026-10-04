import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1530.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1261.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1538.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1257.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1530.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1530.S13

namespace SquarePacking.S11Opt.Split.U2R.C1530
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨0, (traceTriangles 0), (traceTargets 0),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov0 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 1), (traceTargets 1),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov1 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 2), (traceTargets 2),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov4 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1235.cov4 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 4), (traceTargets 4), cov4⟩,
  ⟨7, (traceTriangles 5), (traceTargets 5), cov5⟩,
  ⟨9, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1257.cov6 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨11, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨0, (traceTriangles 9), (traceTargets 9),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1261.cov9 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1538.cov9 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1257.cov12 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 12), (traceTargets 12), cov12⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨6, (traceTriangles 13), cov13⟩

lemma hJ : J = maskAt 1530 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1530) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1530
#print axioms SquarePacking.S11Opt.Split.U2R.C1530.excluded
