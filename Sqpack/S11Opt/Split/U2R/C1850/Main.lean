import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1850.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.SharedStages001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.SharedStages005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1696.SharedStages001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1716.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1731.SharedStages001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1842.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1848.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1850.S12
import Sqpack.S11Opt.Split.U2R.C1850.S14
import Sqpack.S11Opt.Split.U2R.C1850.S15
import Sqpack.S11Opt.Split.U2R.C1850.S17
import Sqpack.S11Opt.Split.U2R.C1850.S18
import Sqpack.S11Opt.Split.U2R.C1850.S20
import Sqpack.S11Opt.Split.U2R.C1850.S21
import Sqpack.S11Opt.Split.U2R.C1850.S22
import Sqpack.S11Opt.Split.U2R.C1850.S23
import Sqpack.S11Opt.Split.U2R.C1850.S24
import Sqpack.S11Opt.Split.U2R.C1850.S25
import Sqpack.S11Opt.Split.U2R.C1850.S26
import Sqpack.S11Opt.Split.U2R.C1850.S27
import Sqpack.S11Opt.Split.U2R.C1850.S28
import Sqpack.S11Opt.Split.U2R.C1850.S29

namespace SquarePacking.S11Opt.Split.U2R.C1850
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
  ⟨7, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1716.cov5 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1716.cov7 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov6 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov7 (by decide +kernel))⟩,
  ⟨14, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1731.cov9 (by decide +kernel))⟩,
  ⟨0, (traceTriangles 9), (traceTargets 9),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov9 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 10), (traceTargets 10),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1842.cov10 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1842.cov11 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 12), (traceTargets 12), cov12⟩,
  ⟨7, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1842.cov13 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 14), (traceTargets 14), cov14⟩,
  ⟨11, (traceTriangles 15), (traceTargets 15), cov15⟩,
  ⟨12, (traceTriangles 16), (traceTargets 16),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1696.cov18 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨14, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨0, (traceTriangles 19), (traceTargets 19),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1848.cov21 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨3, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨5, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨7, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨9, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨10, (traceTriangles 25), (traceTargets 25), cov25⟩,
  ⟨11, (traceTriangles 26), (traceTargets 26), cov26⟩,
  ⟨12, (traceTriangles 27), (traceTargets 27), cov27⟩,
  ⟨13, (traceTriangles 28), (traceTargets 28), cov28⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨14, (traceTriangles 29), cov29⟩

lemma hJ : J = maskAt 1850 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1850) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1850
#print axioms SquarePacking.S11Opt.Split.U2R.C1850.excluded
