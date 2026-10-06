import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C1025.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C958.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C991.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.SharedStages004
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C439.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C998.SharedStages001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1012.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C997.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1025.SharedStages000
import Sqpack.S11Opt.Split.U2P.C1025.S26

namespace SquarePacking.S11Opt.Split.U2P.C1025
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
  ⟨4, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov4 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C958.cov4 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C991.cov6 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C991.cov7 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨12, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C991.cov9 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 9), (traceTargets 9),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C997.cov9 (by decide +kernel))⟩,
  ⟨15, (traceTriangles 10), (traceTargets 10), cov10⟩,
  ⟨0, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov9 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C439.cov11 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1012.cov13 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 14), (traceTargets 14),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C991.cov14 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨9, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨10, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨11, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨12, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨13, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨0, (traceTriangles 21), (traceTargets 21),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C998.cov22 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨2, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨4, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨6, (traceTriangles 25), (traceTargets 25), cov25⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨9, (traceTriangles 26), cov26⟩

lemma hJ : J = maskAt 1025 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1025) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C1025
#print axioms SquarePacking.S11Opt.Split.U2P.C1025.excluded
