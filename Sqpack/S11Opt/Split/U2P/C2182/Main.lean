import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C2182.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2182.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2182.B001
import Sqpack.S11Opt.Split.U2P.C2182.S15

namespace SquarePacking.S11Opt.Split.U2P.C2182
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨2, tris0, tgt0,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov0 (by decide +kernel))⟩,
  ⟨3, tris1, tgt1,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov1 (by decide +kernel))⟩,
  ⟨4, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov2 (by decide +kernel))⟩,
  ⟨6, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov3 (by decide +kernel))⟩,
  ⟨7, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov4 (by decide +kernel))⟩,
  ⟨8, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov5 (by decide +kernel))⟩,
  ⟨11, tris6, tgt6, cov6⟩,
  ⟨12, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov9 (by decide +kernel))⟩,
  ⟨13, tris8, tgt8, cov8⟩,
  ⟨2, tris9, tgt9, cov9⟩,
  ⟨3, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov11 (by decide +kernel))⟩,
  ⟨4, tris11, tgt11, cov11⟩,
  ⟨5, tris12, tgt12, cov12⟩,
  ⟨6, tris13, tgt13, cov13⟩,
  ⟨7, tris14, tgt14, cov14⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris15, cov15⟩

lemma hJ : J = maskAt 2182 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2182) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C2182
#print axioms SquarePacking.S11Opt.Split.U2P.C2182.excluded
