import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C955.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C919.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C926.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C955.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C955.B000
import Sqpack.S11Opt.Split.U2P.C955.S18

namespace SquarePacking.S11Opt.Split.U2P.C955
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
  ⟨4, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov4 (by decide +kernel))⟩,
  ⟨5, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov5 (by decide +kernel))⟩,
  ⟨9, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C919.cov6 (by decide +kernel))⟩,
  ⟨10, tris6, tgt6, cov6⟩,
  ⟨11, tris7, tgt7, cov7⟩,
  ⟨12, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C919.cov9 (by decide +kernel))⟩,
  ⟨13, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C926.cov9 (by decide +kernel))⟩,
  ⟨15, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov7 (by decide +kernel))⟩,
  ⟨1, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov8 (by decide +kernel))⟩,
  ⟨2, tris13, tgt13, cov13⟩,
  ⟨4, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C919.cov14 (by decide +kernel))⟩,
  ⟨5, tris15, tgt15, cov15⟩,
  ⟨9, tris16, tgt16, cov16⟩,
  ⟨10, tris17, tgt17, cov17⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨13, tris18, cov18⟩

lemma hJ : J = maskAt 955 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 955) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C955
#print axioms SquarePacking.S11Opt.Split.U2P.C955.excluded
