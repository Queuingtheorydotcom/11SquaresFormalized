import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1822.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.SharedStages000
import Sqpack.S11Opt.Split.U2P.C2176.S6
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1810.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1822.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1822.S27

namespace SquarePacking.S11Opt.Split.U2R.C1822
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
  ⟨5, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov3 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov4 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov5 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov6 (by decide +kernel))⟩,
  ⟨15, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨0, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov9 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov10 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov11 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov12 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 14), (traceTargets 14),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov13 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 15), (traceTargets 15),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov14 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨10, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨12, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨13, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨15, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨0, (traceTriangles 21), (traceTargets 21),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1810.cov21 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨3, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨5, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨6, (traceTriangles 25), (traceTargets 25), cov25⟩,
  ⟨7, (traceTriangles 26), (traceTargets 26), cov26⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, (traceTriangles 27), cov27⟩

lemma hJ : J = maskAt 1822 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1822) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1822
#print axioms SquarePacking.S11Opt.Split.U2R.C1822.excluded
