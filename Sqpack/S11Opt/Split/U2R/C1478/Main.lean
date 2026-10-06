import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1478.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1335.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1347.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1411.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1597.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1476.SharedStages001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1476.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.SharedStages001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1478.S40

namespace SquarePacking.S11Opt.Split.U2R.C1478
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
  ⟨11, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1347.cov7 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov8 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov9 (by decide +kernel))⟩,
  ⟨14, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨0, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1597.cov9 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov12 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1476.cov13 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨7, (traceTriangles 14), (traceTargets 14),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1476.cov15 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨10, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨11, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨12, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨13, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨14, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨3, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨5, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨7, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨8, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨10, (traceTriangles 25), (traceTargets 25), cov25⟩,
  ⟨11, (traceTriangles 26), (traceTargets 26), cov26⟩,
  ⟨12, (traceTriangles 27), (traceTargets 27), cov27⟩,
  ⟨13, (traceTriangles 28), (traceTargets 28), cov28⟩,
  ⟨14, (traceTriangles 29), (traceTargets 29), cov29⟩,
  ⟨0, (traceTriangles 30), (traceTargets 30), cov30⟩,
  ⟨1, (traceTriangles 31), (traceTargets 31), cov31⟩,
  ⟨3, (traceTriangles 32), (traceTargets 32), cov32⟩,
  ⟨5, (traceTriangles 33), (traceTargets 33), cov33⟩,
  ⟨7, (traceTriangles 34), (traceTargets 34), cov34⟩,
  ⟨8, (traceTriangles 35), (traceTargets 35), cov35⟩,
  ⟨10, (traceTriangles 36), (traceTargets 36), cov36⟩,
  ⟨11, (traceTriangles 37), (traceTargets 37), cov37⟩,
  ⟨12, (traceTriangles 38), (traceTargets 38), cov38⟩,
  ⟨13, (traceTriangles 39), (traceTargets 39), cov39⟩,
  ⟨14, (traceTriangles 40), (traceTargets 40), cov40⟩,
  ⟨0, (traceTriangles 41), (traceTargets 41), cov41⟩,
  ⟨1, (traceTriangles 42), (traceTargets 42), cov42⟩,
  ⟨3, (traceTriangles 43), (traceTargets 43), cov43⟩,
  ⟨5, (traceTriangles 44), (traceTargets 44), cov44⟩,
  ⟨7, (traceTriangles 45), (traceTargets 45), cov45⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, (traceTriangles 46), cov46⟩

lemma hJ : J = maskAt 1478 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1478) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1478
#print axioms SquarePacking.S11Opt.Split.U2R.C1478.excluded
