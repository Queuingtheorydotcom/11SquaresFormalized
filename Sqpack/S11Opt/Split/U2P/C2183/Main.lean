import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C2183.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2182.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2183.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2183.B000
import Sqpack.S11Opt.Split.U2P.C2183.S17

namespace SquarePacking.S11Opt.Split.U2P.C2183
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
  ⟨9, tris5, tgt5, cov5⟩,
  ⟨10, tris6, tgt6, cov6⟩,
  ⟨11, tris7, tgt7, cov7⟩,
  ⟨12, tris8, tgt8, cov8⟩,
  ⟨13, tris9, tgt9, cov9⟩,
  ⟨2, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2182.cov9 (by decide +kernel))⟩,
  ⟨3, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov11 (by decide +kernel))⟩,
  ⟨4, tris12, tgt12, cov12⟩,
  ⟨5, tris13, tgt13, cov13⟩,
  ⟨6, tris14, tgt14, cov14⟩,
  ⟨7, tris15, tgt15, cov15⟩,
  ⟨9, tris16, tgt16, cov16⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris17, cov17⟩

lemma hJ : J = maskAt 2183 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2183) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C2183
#print axioms SquarePacking.S11Opt.Split.U2P.C2183.excluded
