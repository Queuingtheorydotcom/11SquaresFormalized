import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2G.C2143.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B006
import Sqpack.S11Opt.Split.U2R.C2047.S4
import Sqpack.S11Opt.Split.U2R.C2047.S6
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C2143.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C2143.B001
import Sqpack.S11Opt.Split.U2G.C2143.S13

namespace SquarePacking.S11Opt.Split.U2G.C2143
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨1, tris0, tgt0,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov0 (by decide +kernel))⟩,
  ⟨2, tris1, tgt1,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov1 (by decide +kernel))⟩,
  ⟨4, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov2 (by decide +kernel))⟩,
  ⟨5, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2047.cov4 (by decide +kernel))⟩,
  ⟨6, tris4, tgt4, cov4⟩,
  ⟨7, tris5, tgt5, cov5⟩,
  ⟨8, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2047.cov6 (by decide +kernel))⟩,
  ⟨9, tris7, tgt7, cov7⟩,
  ⟨10, tris8, tgt8, cov8⟩,
  ⟨1, tris9, tgt9, cov9⟩,
  ⟨2, tris10, tgt10, cov10⟩,
  ⟨4, tris11, tgt11, cov11⟩,
  ⟨5, tris12, tgt12, cov12⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨6, tris13, cov13⟩

lemma hJ : J = maskAt 2143 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2143) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2G.C2143
#print axioms SquarePacking.S11Opt.Split.U2G.C2143.excluded
