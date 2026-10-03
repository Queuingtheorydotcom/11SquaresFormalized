import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C2176.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2176.B000
import Sqpack.S11Opt.Split.U2P.C2176.S6
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2176.B001
import Sqpack.S11Opt.Split.U2P.C2176.S14

namespace SquarePacking.S11Opt.Split.U2P.C2176
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨1, tris0, tgt0,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov0 (by decide +kernel))⟩,
  ⟨3, tris1, tgt1,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov1 (by decide +kernel))⟩,
  ⟨7, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov4 (by decide +kernel))⟩,
  ⟨8, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨11, tris4, tgt4, cov4⟩,
  ⟨12, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨13, tris6, tgt6, cov6⟩,
  ⟨3, tris7, tgt7, cov7⟩,
  ⟨6, tris8, tgt8, cov8⟩,
  ⟨7, tris9, tgt9, cov9⟩,
  ⟨8, tris10, tgt10, cov10⟩,
  ⟨9, tris11, tgt11, cov11⟩,
  ⟨10, tris12, tgt12, cov12⟩,
  ⟨12, tris13, tgt13, cov13⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨13, tris14, cov14⟩

lemma hJ : J = maskAt 2176 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2176) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C2176
#print axioms SquarePacking.S11Opt.Split.U2P.C2176.excluded
