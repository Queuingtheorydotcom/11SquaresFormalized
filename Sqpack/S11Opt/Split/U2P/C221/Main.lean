import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Split.U2P.C221.S6
import Sqpack.S11Opt.Split.U2P.C221.S11

namespace SquarePacking.S11Opt.Split.U2P.C221
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨0, tris0, tgt0, cov0⟩,
  ⟨1, tris1, tgt1, cov1⟩,
  ⟨2, tris2, tgt2, cov2⟩,
  ⟨3, tris3, tgt3, cov3⟩,
  ⟨4, tris4, tgt4, cov4⟩,
  ⟨5, tris5, tgt5, cov5⟩,
  ⟨8, tris6, tgt6, cov6⟩,
  ⟨0, tris7, tgt7, cov7⟩,
  ⟨1, tris8, tgt8, cov8⟩,
  ⟨2, tris9, tgt9, cov9⟩,
  ⟨4, tris10, tgt10, cov10⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, tris11, cov11⟩

lemma hJ : J = maskAt 221 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 221) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C221
#print axioms SquarePacking.S11Opt.Split.U2P.C221.excluded
