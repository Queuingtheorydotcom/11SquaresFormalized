import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1476.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1335.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1347.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1411.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1597.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1476.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1476.SharedStages001
import Sqpack.S11Opt.Split.U2R.C1476.S32

namespace SquarePacking.S11Opt.Split.U2R.C1476
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
  ⟨5, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov3 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov4 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov6 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 6), (traceTargets 6), cov6⟩,
  ⟨11, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1347.cov7 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov8 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨14, (traceTriangles 10), (traceTargets 10), cov10⟩,
  ⟨0, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1597.cov9 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov12 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨5, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨7, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨8, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨9, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨11, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨12, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨13, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨14, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨0, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨1, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨3, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨5, (traceTriangles 25), (traceTargets 25), cov25⟩,
  ⟨7, (traceTriangles 26), (traceTargets 26), cov26⟩,
  ⟨8, (traceTriangles 27), (traceTargets 27), cov27⟩,
  ⟨9, (traceTriangles 28), (traceTargets 28), cov28⟩,
  ⟨11, (traceTriangles 29), (traceTargets 29), cov29⟩,
  ⟨12, (traceTriangles 30), (traceTargets 30), cov30⟩,
  ⟨13, (traceTriangles 31), (traceTargets 31), cov31⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨14, (traceTriangles 32), cov32⟩

lemma hJ : J = maskAt 1476 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1476) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1476
#print axioms SquarePacking.S11Opt.Split.U2R.C1476.excluded
