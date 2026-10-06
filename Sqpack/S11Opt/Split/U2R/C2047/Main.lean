import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C2047.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages001
import Sqpack.S11Opt.Split.U2R.C2050.S9
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C2143.SharedStages000
import Sqpack.S11Opt.Split.U2R.C2047.S4
import Sqpack.S11Opt.Split.U2R.C2047.S5
import Sqpack.S11Opt.Split.U2R.C2047.S6
import Sqpack.S11Opt.Split.U2R.C2047.S7
import Sqpack.S11Opt.Split.U2R.C2047.S8
import Sqpack.S11Opt.Split.U2R.C2047.S9
import Sqpack.S11Opt.Split.U2R.C2047.S12
import Sqpack.S11Opt.Split.U2R.C2047.S13
import Sqpack.S11Opt.Split.U2R.C2047.S14
import Sqpack.S11Opt.Split.U2R.C2047.S15
import Sqpack.S11Opt.Split.U2R.C2047.S16
import Sqpack.S11Opt.Split.U2R.C2047.S17
import Sqpack.S11Opt.Split.U2R.C2047.S18
import Sqpack.S11Opt.Split.U2R.C2047.S19
import Sqpack.S11Opt.Split.U2R.C2047.S20
import Sqpack.S11Opt.Split.U2R.C2047.S21

namespace SquarePacking.S11Opt.Split.U2R.C2047
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨1, (traceTriangles 0), (traceTargets 0),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov0 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 1), (traceTargets 1),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov1 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 2), (traceTargets 2),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov2 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov2 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 4), (traceTargets 4), cov4⟩,
  ⟨6, (traceTriangles 5), (traceTargets 5), cov5⟩,
  ⟨8, (traceTriangles 6), (traceTargets 6), cov6⟩,
  ⟨10, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨11, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨12, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨13, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2050.cov9 (by decide +kernel))⟩,
  ⟨1, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2G.C2143.cov9 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 12), (traceTargets 12), cov12⟩,
  ⟨3, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨4, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨5, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨6, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨8, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨1, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨2, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨4, (traceTriangles 20), (traceTargets 20), cov20⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, (traceTriangles 21), cov21⟩

lemma hJ : J = maskAt 2047 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2047) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C2047
#print axioms SquarePacking.S11Opt.Split.U2R.C2047.excluded
