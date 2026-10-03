import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C2174.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2176.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.B001
import Sqpack.S11Opt.Split.U2P.C2174.S18

namespace SquarePacking.S11Opt.Split.U2P.C2174
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨1, tris0, tgt0,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov0 (by decide +kernel))⟩,
  ⟨3, tris1, tgt1, cov1⟩,
  ⟨4, tris2, tgt2, cov2⟩,
  ⟨5, tris3, tgt3, cov3⟩,
  ⟨7, tris4, tgt4, cov4⟩,
  ⟨8, tris5, tgt5, cov5⟩,
  ⟨9, tris6, tgt6, cov6⟩,
  ⟨10, tris7, tgt7, cov7⟩,
  ⟨11, tris8, tgt8, cov8⟩,
  ⟨12, tris9, tgt9, cov9⟩,
  ⟨13, tris10, tgt10, cov10⟩,
  ⟨1, tris11, tgt11, cov11⟩,
  ⟨3, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov7 (by decide +kernel))⟩,
  ⟨4, tris13, tgt13, cov13⟩,
  ⟨5, tris14, tgt14, cov14⟩,
  ⟨7, tris15, tgt15, cov15⟩,
  ⟨8, tris16, tgt16, cov16⟩,
  ⟨9, tris17, tgt17, cov17⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris18, cov18⟩

lemma hJ : J = maskAt 2174 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2174) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C2174
#print axioms SquarePacking.S11Opt.Split.U2P.C2174.excluded
