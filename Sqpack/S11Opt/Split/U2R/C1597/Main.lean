import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1597.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1411.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.SharedStages001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1574.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1597.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1597.S24

namespace SquarePacking.S11Opt.Split.U2R.C1597
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
  ⟨5, (traceTriangles 2), (traceTargets 2),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov3 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1574.cov3 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov6 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1574.cov6 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov8 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov9 (by decide +kernel))⟩,
  ⟨15, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1574.cov8 (by decide +kernel))⟩,
  ⟨0, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨1, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov12 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1478.cov13 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 12), (traceTargets 12), cov12⟩,
  ⟨7, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨8, (traceTriangles 14), (traceTargets 14),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1478.cov15 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨11, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨12, (traceTriangles 17), (traceTargets 17),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1478.cov18 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨15, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨5, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨6, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨7, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨10, (traceTriangles 23), (traceTargets 23), cov23⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨11, (traceTriangles 24), cov24⟩

lemma hJ : J = maskAt 1597 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1597) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1597
#print axioms SquarePacking.S11Opt.Split.U2R.C1597.excluded
