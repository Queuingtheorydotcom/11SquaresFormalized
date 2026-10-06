import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1342.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.SharedStages004
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C439.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1335.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1365.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1341.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1342.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1342.S37

namespace SquarePacking.S11Opt.Split.U2R.C1342
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
  ⟨8, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C439.cov5 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C439.cov6 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov7 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov9 (by decide +kernel))⟩,
  ⟨15, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨0, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov9 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1365.cov9 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov12 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov13 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 14), (traceTargets 14),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1341.cov14 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 15), (traceTargets 15),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1341.cov15 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 16), (traceTargets 16),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov16 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 17), (traceTargets 17),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1341.cov17 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨13, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨15, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨0, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨1, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨3, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨4, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨6, (traceTriangles 25), (traceTargets 25), cov25⟩,
  ⟨7, (traceTriangles 26), (traceTargets 26), cov26⟩,
  ⟨8, (traceTriangles 27), (traceTargets 27), cov27⟩,
  ⟨9, (traceTriangles 28), (traceTargets 28), cov28⟩,
  ⟨10, (traceTriangles 29), (traceTargets 29), cov29⟩,
  ⟨13, (traceTriangles 30), (traceTargets 30), cov30⟩,
  ⟨0, (traceTriangles 31), (traceTargets 31), cov31⟩,
  ⟨1, (traceTriangles 32), (traceTargets 32), cov32⟩,
  ⟨3, (traceTriangles 33), (traceTargets 33), cov33⟩,
  ⟨4, (traceTriangles 34), (traceTargets 34), cov34⟩,
  ⟨6, (traceTriangles 35), (traceTargets 35), cov35⟩,
  ⟨8, (traceTriangles 36), (traceTargets 36), cov36⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨9, (traceTriangles 37), cov37⟩

lemma hJ : J = maskAt 1342 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1342) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1342
#print axioms SquarePacking.S11Opt.Split.U2R.C1342.excluded
