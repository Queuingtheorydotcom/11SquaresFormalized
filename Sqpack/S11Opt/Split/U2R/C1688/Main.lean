import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1688.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1636.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1640.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1686.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1688.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1688.S31

namespace SquarePacking.S11Opt.Split.U2R.C1688
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
  ⟨10, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1686.cov7 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1686.cov8 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 9), (traceTargets 9),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1640.cov9 (by decide +kernel))⟩,
  ⟨15, (traceTriangles 10), (traceTargets 10), cov10⟩,
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
  ⟨6, (traceTriangles 16), (traceTargets 16),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1686.cov16 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨10, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨11, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨12, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨0, (traceTriangles 21), (traceTargets 21),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1686.cov22 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨3, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨4, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨5, (traceTriangles 25), (traceTargets 25), cov25⟩,
  ⟨6, (traceTriangles 26), (traceTargets 26), cov26⟩,
  ⟨9, (traceTriangles 27), (traceTargets 27), cov27⟩,
  ⟨0, (traceTriangles 28), (traceTargets 28), cov28⟩,
  ⟨2, (traceTriangles 29), (traceTargets 29), cov29⟩,
  ⟨4, (traceTriangles 30), (traceTargets 30), cov30⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, (traceTriangles 31), cov31⟩

lemma hJ : J = maskAt 1688 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1688) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1688
#print axioms SquarePacking.S11Opt.Split.U2R.C1688.excluded
