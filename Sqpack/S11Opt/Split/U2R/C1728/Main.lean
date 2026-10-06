import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1728.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1716.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1722.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1728.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1728.SharedStages001
import Sqpack.S11Opt.Split.U2R.C1728.S49

namespace SquarePacking.S11Opt.Split.U2R.C1728
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
  ⟨7, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1716.cov5 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov6 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov7 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov9 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨15, (traceTriangles 10), (traceTargets 10), cov10⟩,
  ⟨0, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1716.cov11 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1716.cov12 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 14), (traceTargets 14),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov14 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 15), (traceTargets 15),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov15 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨9, (traceTriangles 17), (traceTargets 17),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov17 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨12, (traceTriangles 19), (traceTargets 19),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov20 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨15, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨0, (traceTriangles 22), (traceTargets 22),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov22 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨3, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨4, (traceTriangles 25), (traceTargets 25),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov25 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 26), (traceTargets 26), cov26⟩,
  ⟨7, (traceTriangles 27), (traceTargets 27), cov27⟩,
  ⟨9, (traceTriangles 28), (traceTargets 28), cov28⟩,
  ⟨10, (traceTriangles 29), (traceTargets 29), cov29⟩,
  ⟨12, (traceTriangles 30), (traceTargets 30), cov30⟩,
  ⟨13, (traceTriangles 31), (traceTargets 31), cov31⟩,
  ⟨15, (traceTriangles 32), (traceTargets 32), cov32⟩,
  ⟨0, (traceTriangles 33), (traceTargets 33), cov33⟩,
  ⟨2, (traceTriangles 34), (traceTargets 34), cov34⟩,
  ⟨3, (traceTriangles 35), (traceTargets 35), cov35⟩,
  ⟨4, (traceTriangles 36), (traceTargets 36), cov36⟩,
  ⟨5, (traceTriangles 37), (traceTargets 37), cov37⟩,
  ⟨7, (traceTriangles 38), (traceTargets 38), cov38⟩,
  ⟨9, (traceTriangles 39), (traceTargets 39), cov39⟩,
  ⟨10, (traceTriangles 40), (traceTargets 40), cov40⟩,
  ⟨12, (traceTriangles 41), (traceTargets 41), cov41⟩,
  ⟨13, (traceTriangles 42), (traceTargets 42), cov42⟩,
  ⟨0, (traceTriangles 43), (traceTargets 43), cov43⟩,
  ⟨2, (traceTriangles 44), (traceTargets 44), cov44⟩,
  ⟨4, (traceTriangles 45), (traceTargets 45), cov45⟩,
  ⟨5, (traceTriangles 46), (traceTargets 46), cov46⟩,
  ⟨9, (traceTriangles 47), (traceTargets 47), cov47⟩,
  ⟨0, (traceTriangles 48), (traceTargets 48), cov48⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨4, (traceTriangles 49), cov49⟩

lemma hJ : J = maskAt 1728 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1728) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1728
#print axioms SquarePacking.S11Opt.Split.U2R.C1728.excluded
