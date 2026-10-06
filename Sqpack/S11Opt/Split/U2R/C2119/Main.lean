import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C2119.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages001
import Sqpack.S11Opt.Split.U2R.C2112.S4
import Sqpack.S11Opt.Split.U2R.C2112.S5
import Sqpack.S11Opt.Split.U2R.C2112.S11
import Sqpack.S11Opt.Split.U2R.C2112.S12
import Sqpack.S11Opt.Split.U2R.C2112.S13
import Sqpack.S11Opt.Split.U2R.C2112.S16
import Sqpack.S11Opt.Split.U2R.C2119.S7
import Sqpack.S11Opt.Split.U2R.C2119.S9
import Sqpack.S11Opt.Split.U2R.C2119.S14
import Sqpack.S11Opt.Split.U2R.C2119.S15
import Sqpack.S11Opt.Split.U2R.C2119.S17
import Sqpack.S11Opt.Split.U2R.C2119.S18
import Sqpack.S11Opt.Split.U2R.C2119.S19
import Sqpack.S11Opt.Split.U2R.C2119.S20

namespace SquarePacking.S11Opt.Split.U2R.C2119
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
  ⟨5, (traceTriangles 3), (traceTargets 3),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov3 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2112.cov4 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2112.cov5 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov5 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 7), (traceTargets 7), cov7⟩,
  ⟨12, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨14, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨1, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov9 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2112.cov11 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2112.cov12 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2112.cov13 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨7, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨8, (traceTriangles 16), (traceTargets 16),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2112.cov16 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨1, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨2, (traceTriangles 19), (traceTargets 19), cov19⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, (traceTriangles 20), cov20⟩

lemma hJ : J = maskAt 2119 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2119) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C2119
#print axioms SquarePacking.S11Opt.Split.U2R.C2119.excluded
