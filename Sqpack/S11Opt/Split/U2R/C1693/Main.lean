import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1693.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1636.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1640.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1650.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1650.S10
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1686.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1693.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1693.SharedStages001
import Sqpack.S11Opt.Split.U2R.C1693.S46

namespace SquarePacking.S11Opt.Split.U2R.C1693
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
  ⟨9, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1636.cov7 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1673.cov8 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1640.cov9 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 9), (traceTargets 9),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1650.cov9 (by decide +kernel))⟩,
  ⟨14, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1650.cov10 (by decide +kernel))⟩,
  ⟨0, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1673.cov12 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1673.cov13 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 14), (traceTargets 14),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1636.cov14 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 15), (traceTargets 15),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1686.cov15 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨9, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨11, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨12, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨13, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨14, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨0, (traceTriangles 22), (traceTargets 22),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1686.cov22 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨3, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨4, (traceTriangles 25), (traceTargets 25), cov25⟩,
  ⟨5, (traceTriangles 26), (traceTargets 26), cov26⟩,
  ⟨6, (traceTriangles 27), (traceTargets 27), cov27⟩,
  ⟨9, (traceTriangles 28), (traceTargets 28), cov28⟩,
  ⟨11, (traceTriangles 29), (traceTargets 29), cov29⟩,
  ⟨12, (traceTriangles 30), (traceTargets 30), cov30⟩,
  ⟨13, (traceTriangles 31), (traceTargets 31), cov31⟩,
  ⟨14, (traceTriangles 32), (traceTargets 32), cov32⟩,
  ⟨0, (traceTriangles 33), (traceTargets 33), cov33⟩,
  ⟨2, (traceTriangles 34), (traceTargets 34), cov34⟩,
  ⟨3, (traceTriangles 35), (traceTargets 35), cov35⟩,
  ⟨4, (traceTriangles 36), (traceTargets 36), cov36⟩,
  ⟨5, (traceTriangles 37), (traceTargets 37), cov37⟩,
  ⟨6, (traceTriangles 38), (traceTargets 38), cov38⟩,
  ⟨9, (traceTriangles 39), (traceTargets 39), cov39⟩,
  ⟨11, (traceTriangles 40), (traceTargets 40), cov40⟩,
  ⟨0, (traceTriangles 41), (traceTargets 41), cov41⟩,
  ⟨2, (traceTriangles 42), (traceTargets 42), cov42⟩,
  ⟨3, (traceTriangles 43), (traceTargets 43), cov43⟩,
  ⟨4, (traceTriangles 44), (traceTargets 44), cov44⟩,
  ⟨5, (traceTriangles 45), (traceTargets 45), cov45⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨6, (traceTriangles 46), cov46⟩

lemma hJ : J = maskAt 1693 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1693) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1693
#print axioms SquarePacking.S11Opt.Split.U2R.C1693.excluded
