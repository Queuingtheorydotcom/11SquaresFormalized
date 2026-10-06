import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1805.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1438.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1805.S18

namespace SquarePacking.S11Opt.Split.U2R.C1805
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨0, (traceTriangles 0), (traceTargets 0),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov0 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 1), (traceTargets 1),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov0 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 2), (traceTargets 2),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov1 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 3), (traceTargets 3), cov3⟩,
  ⟨6, (traceTriangles 4), (traceTargets 4), cov4⟩,
  ⟨7, (traceTriangles 5), (traceTargets 5), cov5⟩,
  ⟨8, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨14, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1438.cov8 (by decide +kernel))⟩,
  ⟨0, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨2, (traceTriangles 10), (traceTargets 10), cov10⟩,
  ⟨3, (traceTriangles 11), (traceTargets 11), cov11⟩,
  ⟨5, (traceTriangles 12), (traceTargets 12), cov12⟩,
  ⟨6, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨7, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨8, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨9, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨10, (traceTriangles 17), (traceTargets 17), cov17⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨14, (traceTriangles 18), cov18⟩

lemma hJ : J = maskAt 1805 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1805) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1805
#print axioms SquarePacking.S11Opt.Split.U2R.C1805.excluded
