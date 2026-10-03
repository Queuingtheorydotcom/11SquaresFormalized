import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B002
import Sqpack.S11Opt.Split.U2R.C2135.S16

namespace SquarePacking.S11Opt.Split.U2R.C2135
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨1, tris0, tgt0, cov0⟩,
  ⟨2, tris1, tgt1, cov1⟩,
  ⟨3, tris2, tgt2, cov2⟩,
  ⟨5, tris3, tgt3, cov3⟩,
  ⟨7, tris4, tgt4, cov4⟩,
  ⟨8, tris5, tgt5, cov5⟩,
  ⟨11, tris6, tgt6, cov6⟩,
  ⟨13, tris7, tgt7, cov7⟩,
  ⟨14, tris8, tgt8, cov8⟩,
  ⟨1, tris9, tgt9, cov9⟩,
  ⟨2, tris10, tgt10, cov10⟩,
  ⟨3, tris11, tgt11, cov11⟩,
  ⟨5, tris12, tgt12, cov12⟩,
  ⟨7, tris13, tgt13, cov13⟩,
  ⟨8, tris14, tgt14, cov14⟩,
  ⟨9, tris15, tgt15, cov15⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris16, cov16⟩

lemma hJ : J = maskAt 2135 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2135) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C2135
#print axioms SquarePacking.S11Opt.Split.U2R.C2135.excluded
