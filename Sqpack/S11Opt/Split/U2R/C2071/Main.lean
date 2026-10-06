import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C2071.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.SharedStages000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.SharedStages001
import Sqpack.S11Opt.Split.U2R.C2047.S4
import Sqpack.S11Opt.Split.U2R.C2047.S6
import Sqpack.S11Opt.Split.U2R.C2047.S9
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C2143.SharedStages000
import Sqpack.S11Opt.Split.U2R.C2047.S14
import Sqpack.S11Opt.Split.U2R.C2068.S7
import Sqpack.S11Opt.Split.U2R.C2068.S12
import Sqpack.S11Opt.Split.U2R.C2068.S13
import Sqpack.S11Opt.Split.U2R.C2068.S15
import Sqpack.S11Opt.Split.U2R.C2068.S17
import Sqpack.S11Opt.Split.U2R.C2068.S19
import Sqpack.S11Opt.Split.U2R.C2068.S21
import Sqpack.S11Opt.Split.U2R.C2071.S9
import Sqpack.S11Opt.Split.U2R.C2071.S10
import Sqpack.S11Opt.Split.U2R.C2071.S16
import Sqpack.S11Opt.Split.U2R.C2071.S18
import Sqpack.S11Opt.Split.U2R.C2071.S19
import Sqpack.S11Opt.Split.U2R.C2071.S20
import Sqpack.S11Opt.Split.U2R.C2071.S21
import Sqpack.S11Opt.Split.U2R.C2071.S23
import Sqpack.S11Opt.Split.U2R.C2071.S24
import Sqpack.S11Opt.Split.U2R.C2071.S26
import Sqpack.S11Opt.Split.U2R.C2071.S27
import Sqpack.S11Opt.Split.U2R.C2071.S28

namespace SquarePacking.S11Opt.Split.U2R.C2071
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
  ⟨5, (traceTriangles 4), (traceTargets 4),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2047.cov4 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 5), (traceTargets 5),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov4 (by decide +kernel))⟩,
  ⟨8, (traceTriangles 6), (traceTargets 6),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2047.cov6 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 7), (traceTargets 7),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2068.cov7 (by decide +kernel))⟩,
  ⟨12, (traceTriangles 8), (traceTargets 8),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2047.cov9 (by decide +kernel))⟩,
  ⟨13, (traceTriangles 9), (traceTargets 9), cov9⟩,
  ⟨14, (traceTriangles 10), (traceTargets 10), cov10⟩,
  ⟨1, (traceTriangles 11), (traceTargets 11),
    (CovF.weaken SquarePacking.S11Opt.Split.U2G.C2143.cov9 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 12), (traceTargets 12),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2068.cov12 (by decide +kernel))⟩,
  ⟨3, (traceTriangles 13), (traceTargets 13),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2068.cov13 (by decide +kernel))⟩,
  ⟨4, (traceTriangles 14), (traceTargets 14),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2047.cov14 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 15), (traceTargets 15),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2068.cov15 (by decide +kernel))⟩,
  ⟨7, (traceTriangles 16), (traceTargets 16), cov16⟩,
  ⟨8, (traceTriangles 17), (traceTargets 17),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2068.cov17 (by decide +kernel))⟩,
  ⟨10, (traceTriangles 18), (traceTargets 18), cov18⟩,
  ⟨12, (traceTriangles 19), (traceTargets 19), cov19⟩,
  ⟨13, (traceTriangles 20), (traceTargets 20), cov20⟩,
  ⟨14, (traceTriangles 21), (traceTargets 21), cov21⟩,
  ⟨1, (traceTriangles 22), (traceTargets 22),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2068.cov19 (by decide +kernel))⟩,
  ⟨2, (traceTriangles 23), (traceTargets 23), cov23⟩,
  ⟨3, (traceTriangles 24), (traceTargets 24), cov24⟩,
  ⟨4, (traceTriangles 25), (traceTargets 25),
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2068.cov21 (by decide +kernel))⟩,
  ⟨5, (traceTriangles 26), (traceTargets 26), cov26⟩,
  ⟨7, (traceTriangles 27), (traceTargets 27), cov27⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, (traceTriangles 28), cov28⟩

lemma hJ : J = maskAt 2071 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2071) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C2071
#print axioms SquarePacking.S11Opt.Split.U2R.C2071.excluded
