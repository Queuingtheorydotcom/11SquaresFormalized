import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C2102.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages001
import Sqpack.S11Opt.Split.U2R.C2084.S4
import Sqpack.S11Opt.Split.U2R.C2084.S5
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C2095.SharedStages000
import Sqpack.S11Opt.Split.U2R.C2102.S6
import Sqpack.S11Opt.Split.U2R.C2102.S7
import Sqpack.S11Opt.Split.U2R.C2102.S8
import Sqpack.S11Opt.Split.U2R.C2102.S9
import Sqpack.S11Opt.Split.U2R.C2102.S10
import Sqpack.S11Opt.Split.U2R.C2102.S14
import Sqpack.S11Opt.Split.U2R.C2102.S15
import Sqpack.S11Opt.Split.U2R.C2102.S16
import Sqpack.S11Opt.Split.U2R.C2102.S17
import Sqpack.S11Opt.Split.U2R.C2102.S18

namespace SquarePacking.S11Opt.Split.U2R.C2102
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
  ⟨4, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov2 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2084.cov4 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2084.cov5 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 6), (traceTargets 6), cov6⟩,
  ⟨10, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨12, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨13, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨14, (traceTriangles 10), (traceTargets 10), cov10⟩,
  ⟨1, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2G.C2095.cov7 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2G.C2095.cov8 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2G.C2095.cov9 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨6, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨7, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨9, (traceTriangles 17), (traceTargets 17), cov17⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, (traceTriangles 18), cov18⟩

lemma hJ : J = maskAt 2102 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2102) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C2102
#print axioms SquarePacking.S11Opt.Split.U2R.C2102.excluded
