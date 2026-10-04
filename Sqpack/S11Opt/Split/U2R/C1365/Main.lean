import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1365.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.SharedStages004
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.SharedStages001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.SharedStages005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1335.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1347.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1365.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1365.S11
import Sqpack.S11Opt.Split.U2R.C1365.S24

namespace SquarePacking.S11Opt.Split.U2R.C1365
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
  ⟨4, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov4 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov4 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1347.cov7 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov6 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov7 (by decide +kernel))⟩,
  ⟨0, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov9 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨3, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov12 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 11), (traceTargets 11), cov11⟩,
  ⟨6, (traceTriangles 12), (traceTargets 12), cov12⟩,
  ⟨7, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨9, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨10, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨11, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨12, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨13, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨3, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨4, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨6, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨7, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨9, (traceTriangles 23), (traceTargets 23), cov23⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, (traceTriangles 24), cov24⟩

lemma hJ : J = maskAt 1365 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1365) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1365
#print axioms SquarePacking.S11Opt.Split.U2R.C1365.excluded
