import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages001
import Sqpack.S11Opt.Split.U2R.C2135.S16

namespace SquarePacking.S11Opt.Split.U2R.C2135
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨1, (traceTriangles 0), (traceTargets 0), cov0⟩,
  ⟨2, (traceTriangles 1), (traceTargets 1), cov1⟩,
  ⟨3, (traceTriangles 2), (traceTargets 2), cov2⟩,
  ⟨5, (traceTriangles 3), (traceTargets 3), cov3⟩,
  ⟨7, (traceTriangles 4), (traceTargets 4), cov4⟩,
  ⟨8, (traceTriangles 5), (traceTargets 5), cov5⟩,
  ⟨11, (traceTriangles 6), (traceTargets 6), cov6⟩,
  ⟨13, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨14, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨1, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨2, (traceTriangles 10), (traceTargets 10), cov10⟩,
  ⟨3, (traceTriangles 11), (traceTargets 11), cov11⟩,
  ⟨5, (traceTriangles 12), (traceTargets 12), cov12⟩,
  ⟨7, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨8, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨9, (traceTriangles 15), (traceTargets 15), cov15⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, (traceTriangles 16), cov16⟩

lemma hJ : J = maskAt 2135 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2135) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C2135
#print axioms SquarePacking.S11Opt.Split.U2R.C2135.excluded
