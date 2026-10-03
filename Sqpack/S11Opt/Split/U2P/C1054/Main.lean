import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C1054.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C647.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1049.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1049.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C647.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C650.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C647.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1054.B000
import Sqpack.S11Opt.Split.U2P.C1054.S17

namespace SquarePacking.S11Opt.Split.U2P.C1054
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
  ⟨5, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C647.cov4 (by decide +kernel))⟩,
  ⟨6, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1049.cov4 (by decide +kernel))⟩,
  ⟨7, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1049.cov5 (by decide +kernel))⟩,
  ⟨8, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C647.cov5 (by decide +kernel))⟩,
  ⟨9, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1049.cov7 (by decide +kernel))⟩,
  ⟨10, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1049.cov8 (by decide +kernel))⟩,
  ⟨12, tris9, tgt9, cov9⟩,
  ⟨14, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C650.cov9 (by decide +kernel))⟩,
  ⟨1, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C647.cov12 (by decide +kernel))⟩,
  ⟨2, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1049.cov12 (by decide +kernel))⟩,
  ⟨5, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1049.cov13 (by decide +kernel))⟩,
  ⟨6, tris15, tgt15, cov15⟩,
  ⟨8, tris16, tgt16, cov16⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨9, tris17, cov17⟩

lemma hJ : J = maskAt 1054 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1054) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C1054
#print axioms SquarePacking.S11Opt.Split.U2P.C1054.excluded
