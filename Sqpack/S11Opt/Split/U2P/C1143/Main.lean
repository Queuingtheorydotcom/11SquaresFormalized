import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C1143.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C958.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.SharedStages000
import Sqpack.S11Opt.Split.U2P.C763.S9
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.SharedStages000
import Sqpack.S11Opt.Split.U2P.C1143.S17

namespace SquarePacking.S11Opt.Split.U2P.C1143
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
  ⟨2, (traceTriangles 2), (traceTargets 2),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov2 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C958.cov4 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C958.cov5 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 6), (traceTargets 6), cov6⟩,
  ⟨12, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨13, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨14, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨0, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov9 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov10 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 12), (traceTargets 12), cov12⟩,
  ⟨6, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨7, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨8, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨9, (traceTriangles 16), (traceTargets 16), cov16⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, (traceTriangles 17), cov17⟩

lemma hJ : J = maskAt 1143 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1143) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C1143
#print axioms SquarePacking.S11Opt.Split.U2P.C1143.excluded
