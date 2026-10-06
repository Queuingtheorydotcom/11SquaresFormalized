import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1490.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.SharedStages000
import Sqpack.S11Opt.Split.U2P.C763.S9
import Sqpack.S11Opt.Split.U2P.C2176.S6
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2176.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C654.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1335.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1484.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1490.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1490.S15

namespace SquarePacking.S11Opt.Split.U2R.C1490
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
  ⟨3, (traceTriangles 2), (traceTargets 2),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1235.cov2 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov4 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov6 (by decide +kernel))⟩,
  ⟨14, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C654.cov9 (by decide +kernel))⟩,
  ⟨0, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov9 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 9), (traceTargets 9),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1484.cov9 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1484.cov10 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 11), (traceTargets 11), cov11⟩,
  ⟨7, (traceTriangles 12), (traceTargets 12), cov12⟩,
  ⟨8, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov10 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 14), (traceTargets 14), cov14⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, (traceTriangles 15), cov15⟩

lemma hJ : J = maskAt 1490 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1490) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1490
#print axioms SquarePacking.S11Opt.Split.U2R.C1490.excluded
