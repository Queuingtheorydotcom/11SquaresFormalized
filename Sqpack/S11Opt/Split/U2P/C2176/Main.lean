import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C2176.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2176.SharedStages000
import Sqpack.S11Opt.Split.U2P.C2176.S6
import Sqpack.S11Opt.Split.U2P.C2176.S14

namespace SquarePacking.S11Opt.Split.U2P.C2176
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨1, (traceTriangles 0), (traceTargets 0),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov0 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 1), (traceTargets 1),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov1 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 2), (traceTargets 2),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov4 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 4), (traceTargets 4), cov4⟩,
  ⟨12, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 6), (traceTargets 6), cov6⟩,
  ⟨3, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨6, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨7, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨8, (traceTriangles 10), (traceTargets 10), cov10⟩,
  ⟨9, (traceTriangles 11), (traceTargets 11), cov11⟩,
  ⟨10, (traceTriangles 12), (traceTargets 12), cov12⟩,
  ⟨12, (traceTriangles 13), (traceTargets 13), cov13⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨13, (traceTriangles 14), cov14⟩

lemma hJ : J = maskAt 2176 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2176) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C2176
#print axioms SquarePacking.S11Opt.Split.U2P.C2176.excluded
