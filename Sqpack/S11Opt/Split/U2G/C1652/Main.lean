import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2G.C1652.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.SharedStages001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.SharedStages005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1695.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1696.SharedStages001
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C1652.SharedStages000
import Sqpack.S11Opt.Split.U2G.C1652.S18

namespace SquarePacking.S11Opt.Split.U2G.C1652
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
  ⟨4, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov3 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov4 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov5 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov6 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov8 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov6 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 9), (traceTargets 9),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov7 (by decide +kernel))⟩,
  ⟨0, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov11 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov12 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1695.cov13 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨6, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨10, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨12, (traceTriangles 17), (traceTargets 17),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1696.cov18 (by decide +kernel))⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨13, (traceTriangles 18), cov18⟩

lemma hJ : J = maskAt 1652 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1652) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2G.C1652
#print axioms SquarePacking.S11Opt.Split.U2G.C1652.excluded
