import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C2133.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B001
import Sqpack.S11Opt.Split.U2P.C2176.S6
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B002
import Sqpack.S11Opt.Split.U2R.C2133.S14
import Sqpack.S11Opt.Split.U2R.C2133.S15
import Sqpack.S11Opt.Split.U2R.C2133.S16

namespace SquarePacking.S11Opt.Split.U2R.C2133
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨1, tris0, tgt0,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov0 (by decide +kernel))⟩,
  ⟨2, tris1, tgt1,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov1 (by decide +kernel))⟩,
  ⟨3, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov2 (by decide +kernel))⟩,
  ⟨5, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov3 (by decide +kernel))⟩,
  ⟨7, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov4 (by decide +kernel))⟩,
  ⟨8, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov5 (by decide +kernel))⟩,
  ⟨11, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov6 (by decide +kernel))⟩,
  ⟨12, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨13, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov6 (by decide +kernel))⟩,
  ⟨1, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov9 (by decide +kernel))⟩,
  ⟨2, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov10 (by decide +kernel))⟩,
  ⟨3, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov11 (by decide +kernel))⟩,
  ⟨5, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov12 (by decide +kernel))⟩,
  ⟨7, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov13 (by decide +kernel))⟩,
  ⟨8, tris14, tgt14, cov14⟩,
  ⟨9, tris15, tgt15, cov15⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris16, cov16⟩

lemma hJ : J = maskAt 2133 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2133) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C2133
#print axioms SquarePacking.S11Opt.Split.U2R.C2133.excluded
