import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C1114.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C647.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1049.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C650.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1083.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1107.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1114.SharedStages000
import Sqpack.S11Opt.Split.U2P.C1114.S15

namespace SquarePacking.S11Opt.Split.U2P.C1114
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
  ⟨5, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C647.cov4 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1049.cov4 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1083.cov6 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1083.cov7 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨12, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1083.cov9 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨0, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C650.cov9 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C647.cov12 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1107.cov12 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨6, (traceTriangles 14), (traceTargets 14), cov14⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨9, (traceTriangles 15), cov15⟩

lemma hJ : J = maskAt 1114 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1114) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C1114
#print axioms SquarePacking.S11Opt.Split.U2P.C1114.excluded
