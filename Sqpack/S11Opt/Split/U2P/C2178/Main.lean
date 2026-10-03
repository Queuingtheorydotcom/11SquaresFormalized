import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C2178.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2182.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B000
import Sqpack.S11Opt.Split.U2P.C2178.S18

namespace SquarePacking.S11Opt.Split.U2P.C2178
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨2, tris0, tgt0, cov0⟩,
  ⟨3, tris1, tgt1, cov1⟩,
  ⟨4, tris2, tgt2, cov2⟩,
  ⟨6, tris3, tgt3, cov3⟩,
  ⟨7, tris4, tgt4, cov4⟩,
  ⟨8, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov5 (by decide +kernel))⟩,
  ⟨9, tris6, tgt6, cov6⟩,
  ⟨10, tris7, tgt7, cov7⟩,
  ⟨11, tris8, tgt8, cov8⟩,
  ⟨12, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov9 (by decide +kernel))⟩,
  ⟨2, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2182.cov9 (by decide +kernel))⟩,
  ⟨3, tris11, tgt11, cov11⟩,
  ⟨4, tris12, tgt12, cov12⟩,
  ⟨5, tris13, tgt13, cov13⟩,
  ⟨6, tris14, tgt14, cov14⟩,
  ⟨7, tris15, tgt15, cov15⟩,
  ⟨8, tris16, tgt16, cov16⟩,
  ⟨9, tris17, tgt17, cov17⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris18, cov18⟩

lemma hJ : J = maskAt 2178 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2178) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C2178
#print axioms SquarePacking.S11Opt.Split.U2P.C2178.excluded
