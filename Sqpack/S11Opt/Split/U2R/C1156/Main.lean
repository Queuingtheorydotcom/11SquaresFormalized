import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1156.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C958.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.B001
import Sqpack.S11Opt.Split.U2P.C763.S9
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1156.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1156.B000
import Sqpack.S11Opt.Split.U2R.C1156.S21

namespace SquarePacking.S11Opt.Split.U2R.C1156
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨0, tris0, tgt0,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov0 (by decide +kernel))⟩,
  ⟨1, tris1, tgt1,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov1 (by decide +kernel))⟩,
  ⟨2, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov2 (by decide +kernel))⟩,
  ⟨6, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C958.cov4 (by decide +kernel))⟩,
  ⟨8, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨10, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov6 (by decide +kernel))⟩,
  ⟨11, tris6, tgt6, cov6⟩,
  ⟨12, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨13, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov8 (by decide +kernel))⟩,
  ⟨15, tris9, tgt9, cov9⟩,
  ⟨0, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov9 (by decide +kernel))⟩,
  ⟨1, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov10 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12, cov12⟩,
  ⟨6, tris13, tgt13, cov13⟩,
  ⟨8, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov15 (by decide +kernel))⟩,
  ⟨9, tris15, tgt15, cov15⟩,
  ⟨10, tris16, tgt16, cov16⟩,
  ⟨11, tris17, tgt17, cov17⟩,
  ⟨0, tris18, tgt18, cov18⟩,
  ⟨1, tris19, tgt19, cov19⟩,
  ⟨2, tris20, tgt20, cov20⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨6, tris21, cov21⟩

lemma hJ : J = maskAt 1156 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1156) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1156
#print axioms SquarePacking.S11Opt.Split.U2R.C1156.excluded
