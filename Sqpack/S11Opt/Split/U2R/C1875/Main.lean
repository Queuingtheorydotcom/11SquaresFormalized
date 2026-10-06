import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1875.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1864.S4
import Sqpack.S11Opt.Split.U2R.C1864.S5
import Sqpack.S11Opt.Split.U2R.C1864.S7
import Sqpack.S11Opt.Split.U2R.C1864.S12
import Sqpack.S11Opt.Split.U2R.C1864.S13
import Sqpack.S11Opt.Split.U2R.C1864.S14
import Sqpack.S11Opt.Split.U2R.C1866.S21
import Sqpack.S11Opt.Split.U2R.C1875.S8
import Sqpack.S11Opt.Split.U2R.C1875.S9
import Sqpack.S11Opt.Split.U2R.C1875.S10
import Sqpack.S11Opt.Split.U2R.C1875.S15
import Sqpack.S11Opt.Split.U2R.C1875.S16
import Sqpack.S11Opt.Split.U2R.C1875.S17
import Sqpack.S11Opt.Split.U2R.C1875.S18
import Sqpack.S11Opt.Split.U2R.C1875.S19
import Sqpack.S11Opt.Split.U2R.C1875.S21
import Sqpack.S11Opt.Split.U2R.C1875.S22
import Sqpack.S11Opt.Split.U2R.C1875.S23
import Sqpack.S11Opt.Split.U2R.C1875.S24
import Sqpack.S11Opt.Split.U2R.C1875.S25
import Sqpack.S11Opt.Split.U2R.C1875.S26

namespace SquarePacking.S11Opt.Split.U2R.C1875
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
  ⟨6, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov4 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov5 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov7 (by decide +kernel))⟩,
  ⟨9, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov7 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 8), (traceTargets 8), cov8⟩,
  ⟨13, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨14, (traceTriangles 10), (traceTargets 10), cov10⟩,
  ⟨0, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov12 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov13 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 14), (traceTargets 14),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov14 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨7, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨8, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨9, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨11, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨0, (traceTriangles 20), (traceTargets 20),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1866.cov21 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨4, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨5, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨6, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨7, (traceTriangles 25), (traceTargets 25), cov25⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨2, (traceTriangles 26), cov26⟩

lemma hJ : J = maskAt 1875 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1875) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1875
#print axioms SquarePacking.S11Opt.Split.U2R.C1875.excluded
