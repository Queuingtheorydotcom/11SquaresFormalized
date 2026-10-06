import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C2178.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2182.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.SharedStages000
import Sqpack.S11Opt.Split.U2P.C2178.S18

namespace SquarePacking.S11Opt.Split.U2P.C2178
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨2, (traceTriangles 0), (traceTargets 0), cov0⟩,
  ⟨3, (traceTriangles 1), (traceTargets 1), cov1⟩,
  ⟨4, (traceTriangles 2), (traceTargets 2), cov2⟩,
  ⟨6, (traceTriangles 3), (traceTargets 3), cov3⟩,
  ⟨7, (traceTriangles 4), (traceTargets 4), cov4⟩,
  ⟨8, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov5 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 6), (traceTargets 6), cov6⟩,
  ⟨10, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨11, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨12, (traceTriangles 9), (traceTargets 9),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov9 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2182.cov9 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 11), (traceTargets 11), cov11⟩,
  ⟨4, (traceTriangles 12), (traceTargets 12), cov12⟩,
  ⟨5, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨6, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨7, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨8, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨9, (traceTriangles 17), (traceTargets 17), cov17⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, (traceTriangles 18), cov18⟩

lemma hJ : J = maskAt 2178 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2178) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C2178
#print axioms SquarePacking.S11Opt.Split.U2P.C2178.excluded
