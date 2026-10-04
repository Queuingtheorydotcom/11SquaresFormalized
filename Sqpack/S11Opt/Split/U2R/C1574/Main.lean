import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1574.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.SharedStages004
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C439.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1365.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1335.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1342.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1347.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1574.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1574.S24

namespace SquarePacking.S11Opt.Split.U2R.C1574
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
  ⟨7, (traceTriangles 3), (traceTargets 3), cov3⟩,
  ⟨8, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C439.cov5 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C439.cov6 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 6), (traceTargets 6), cov6⟩,
  ⟨13, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1347.cov8 (by decide +kernel))⟩,
  ⟨15, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨0, (traceTriangles 9), (traceTargets 9),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov9 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1365.cov9 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov13 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 12), (traceTargets 12), cov12⟩,
  ⟨7, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨8, (traceTriangles 14), (traceTargets 14),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1347.cov16 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨10, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨11, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨13, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨0, (traceTriangles 19), (traceTargets 19),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1342.cov21 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨4, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨6, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨8, (traceTriangles 23), (traceTargets 23), cov23⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨9, (traceTriangles 24), cov24⟩

lemma hJ : J = maskAt 1574 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1574) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1574
#print axioms SquarePacking.S11Opt.Split.U2R.C1574.excluded
