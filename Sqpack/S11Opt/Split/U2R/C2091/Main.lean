import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C2091.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B004
import Sqpack.S11Opt.Split.U2R.C2084.S4
import Sqpack.S11Opt.Split.U2R.C2084.S5
import Sqpack.S11Opt.Split.U2R.C2084.S7
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C2095.B000
import Sqpack.S11Opt.Split.U2R.C2084.S14
import Sqpack.S11Opt.Split.U2R.C2084.S17
import Sqpack.S11Opt.Split.U2R.C2091.S8
import Sqpack.S11Opt.Split.U2R.C2091.S14
import Sqpack.S11Opt.Split.U2R.C2091.S16

namespace SquarePacking.S11Opt.Split.U2R.C2091
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
  ⟨4, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov2 (by decide +kernel))⟩,
  ⟨6, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2084.cov4 (by decide +kernel))⟩,
  ⟨7, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2084.cov5 (by decide +kernel))⟩,
  ⟨8, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov5 (by decide +kernel))⟩,
  ⟨9, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2084.cov7 (by decide +kernel))⟩,
  ⟨11, tris8, tgt8, cov8⟩,
  ⟨12, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov9 (by decide +kernel))⟩,
  ⟨14, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2G.C2095.cov6 (by decide +kernel))⟩,
  ⟨1, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2G.C2095.cov7 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2G.C2095.cov8 (by decide +kernel))⟩,
  ⟨4, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2084.cov14 (by decide +kernel))⟩,
  ⟨6, tris14, tgt14, cov14⟩,
  ⟨8, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2084.cov17 (by decide +kernel))⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨9, tris16, cov16⟩

lemma hJ : J = maskAt 2091 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2091) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C2091
#print axioms SquarePacking.S11Opt.Split.U2R.C2091.excluded
