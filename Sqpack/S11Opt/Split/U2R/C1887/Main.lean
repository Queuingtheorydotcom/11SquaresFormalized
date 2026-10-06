import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1887.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.SharedStages000
import Sqpack.S11Opt.Split.U2R.C1864.S4
import Sqpack.S11Opt.Split.U2R.C1864.S5
import Sqpack.S11Opt.Split.U2R.C1864.S12
import Sqpack.S11Opt.Split.U2R.C1885.S6
import Sqpack.S11Opt.Split.U2R.C1885.S7
import Sqpack.S11Opt.Split.U2R.C1885.S8
import Sqpack.S11Opt.Split.U2R.C1885.S9
import Sqpack.S11Opt.Split.U2R.C1885.S13
import Sqpack.S11Opt.Split.U2R.C1885.S14
import Sqpack.S11Opt.Split.U2R.C1885.S15
import Sqpack.S11Opt.Split.U2R.C1887.S10
import Sqpack.S11Opt.Split.U2R.C1887.S16
import Sqpack.S11Opt.Split.U2R.C1887.S17
import Sqpack.S11Opt.Split.U2R.C1887.S18
import Sqpack.S11Opt.Split.U2R.C1887.S19
import Sqpack.S11Opt.Split.U2R.C1887.S20
import Sqpack.S11Opt.Split.U2R.C1887.S21
import Sqpack.S11Opt.Split.U2R.C1887.S22
import Sqpack.S11Opt.Split.U2R.C1887.S23
import Sqpack.S11Opt.Split.U2R.C1887.S24
import Sqpack.S11Opt.Split.U2R.C1887.S25
import Sqpack.S11Opt.Split.U2R.C1887.S26
import Sqpack.S11Opt.Split.U2R.C1887.S27
import Sqpack.S11Opt.Split.U2R.C1887.S28
import Sqpack.S11Opt.Split.U2R.C1887.S29
import Sqpack.S11Opt.Split.U2R.C1887.S30
import Sqpack.S11Opt.Split.U2R.C1887.S31

namespace SquarePacking.S11Opt.Split.U2R.C1887
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
  ⟨9, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1885.cov6 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1885.cov7 (by decide +kernel))⟩,
  ⟨11, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1885.cov8 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 9), (traceTargets 9),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1885.cov9 (by decide +kernel))⟩,
  ⟨15, (traceTriangles 10), (traceTargets 10), cov10⟩,
  ⟨0, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov12 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1885.cov13 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 14), (traceTargets 14),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1885.cov14 (by decide +kernel))⟩,
  ⟨6, (traceTriangles 15), (traceTargets 15),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1885.cov15 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨9, (traceTriangles 17), (traceTargets 17), cov17⟩,
  ⟨10, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨11, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨12, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨0, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨2, (traceTriangles 22), (traceTargets 22), cov22⟩,
  ⟨4, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨5, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨6, (traceTriangles 25), (traceTargets 25), cov25⟩,
  ⟨7, (traceTriangles 26), (traceTargets 26), cov26⟩,
  ⟨9, (traceTriangles 27), (traceTargets 27), cov27⟩,
  ⟨0, (traceTriangles 28), (traceTargets 28), cov28⟩,
  ⟨2, (traceTriangles 29), (traceTargets 29), cov29⟩,
  ⟨4, (traceTriangles 30), (traceTargets 30), cov30⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, (traceTriangles 31), cov31⟩

lemma hJ : J = maskAt 1887 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1887) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1887
#print axioms SquarePacking.S11Opt.Split.U2R.C1887.excluded
