import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Split.U2P.C221.S6
import Sqpack.S11Opt.Split.U2P.C221.S11

namespace SquarePacking.S11Opt.Split.U2P.C221
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨0, (traceTriangles 0), (traceTargets 0), cov0⟩,
  ⟨1, (traceTriangles 1), (traceTargets 1), cov1⟩,
  ⟨2, (traceTriangles 2), (traceTargets 2), cov2⟩,
  ⟨3, (traceTriangles 3), (traceTargets 3), cov3⟩,
  ⟨4, (traceTriangles 4), (traceTargets 4), cov4⟩,
  ⟨5, (traceTriangles 5), (traceTargets 5), cov5⟩,
  ⟨8, (traceTriangles 6), (traceTargets 6), cov6⟩,
  ⟨0, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨1, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨2, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨4, (traceTriangles 10), (traceTargets 10), cov10⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, (traceTriangles 11), cov11⟩

lemma hJ : J = maskAt 221 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 221) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C221
#print axioms SquarePacking.S11Opt.Split.U2P.C221.excluded
