import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1864.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1871.S9
import Sqpack.S11Opt.Split.U2R.C1864.S4
import Sqpack.S11Opt.Split.U2R.C1864.S5
import Sqpack.S11Opt.Split.U2R.C1864.S7
import Sqpack.S11Opt.Split.U2R.C1864.S8
import Sqpack.S11Opt.Split.U2R.C1864.S9
import Sqpack.S11Opt.Split.U2R.C1864.S12
import Sqpack.S11Opt.Split.U2R.C1864.S13
import Sqpack.S11Opt.Split.U2R.C1864.S14
import Sqpack.S11Opt.Split.U2R.C1864.S15
import Sqpack.S11Opt.Split.U2R.C1864.S16
import Sqpack.S11Opt.Split.U2R.C1864.S17
import Sqpack.S11Opt.Split.U2R.C1864.S18
import Sqpack.S11Opt.Split.U2R.C1864.S19

namespace SquarePacking.S11Opt.Split.U2R.C1864
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
  ⟨4, (traceTriangles 2), (traceTargets 2),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov3 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov4 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 4), (traceTargets 4), cov4⟩,
  ⟨7, (traceTriangles 5), (traceTargets 5), cov5⟩,
  ⟨8, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov7 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨10, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨11, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨13, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1871.cov9 (by decide +kernel))⟩,
  ⟨0, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 12), (traceTargets 12), cov12⟩,
  ⟨4, (traceTriangles 13), (traceTargets 13), cov13⟩,
  ⟨5, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨6, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨8, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨9, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨10, (traceTriangles 18), (traceTargets 18), cov18⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨13, (traceTriangles 19), cov19⟩

lemma hJ : J = maskAt 1864 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1864) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1864
#print axioms SquarePacking.S11Opt.Split.U2R.C1864.excluded
