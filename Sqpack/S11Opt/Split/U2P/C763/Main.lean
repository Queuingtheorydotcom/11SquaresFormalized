import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C763.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.SharedStages001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C647.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.SharedStages000
import Sqpack.S11Opt.Split.U2P.C763.S9
import Sqpack.S11Opt.Split.U2P.C763.S29

namespace SquarePacking.S11Opt.Split.U2P.C763
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
  ⟨2, (traceTriangles 2), (traceTargets 2),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov2 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov3 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 4), (traceTargets 4), cov4⟩,
  ⟨11, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov5 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov7 (by decide +kernel))⟩,
  ⟨14, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨15, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨0, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨1, (traceTriangles 10), (traceTargets 10), cov10⟩,
  ⟨2, (traceTriangles 11), (traceTargets 11), cov11⟩,
  ⟨3, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C647.cov14 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨9, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨10, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨11, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨13, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨14, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨15, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨0, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨1, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨2, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨3, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨8, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨9, (traceTriangles 25), (traceTargets 25), cov25⟩,
  ⟨10, (traceTriangles 26), (traceTargets 26), cov26⟩,
  ⟨0, (traceTriangles 27), (traceTargets 27), cov27⟩,
  ⟨1, (traceTriangles 28), (traceTargets 28), cov28⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨2, (traceTriangles 29), cov29⟩

lemma hJ : J = maskAt 763 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 763) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C763
#print axioms SquarePacking.S11Opt.Split.U2P.C763.excluded
