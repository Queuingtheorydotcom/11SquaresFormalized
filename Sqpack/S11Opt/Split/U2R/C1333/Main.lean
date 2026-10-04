import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1333.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C955.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1261.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1538.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1257.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1303.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1333.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1333.S16

namespace SquarePacking.S11Opt.Split.U2R.C1333
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
  ⟨9, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1257.cov6 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 5), (traceTargets 5), cov5⟩,
  ⟨11, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C955.cov7 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1257.cov8 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨15, (traceTriangles 9), (traceTargets 9),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C955.cov10 (by decide +kernel))⟩,
  ⟨0, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1261.cov9 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1538.cov9 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1257.cov12 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1303.cov15 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨10, (traceTriangles 15), (traceTargets 15), cov15⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨13, (traceTriangles 16), cov16⟩

lemma hJ : J = maskAt 1333 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1333) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1333
#print axioms SquarePacking.S11Opt.Split.U2R.C1333.excluded
