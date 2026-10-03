import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1492.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.B001
import Sqpack.S11Opt.Split.U2P.C763.S9
import Sqpack.S11Opt.Split.U2P.C2176.S6
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2176.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1335.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1347.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1484.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1484.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1492.B000
import Sqpack.S11Opt.Split.U2R.C1492.S19

namespace SquarePacking.S11Opt.Split.U2R.C1492
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
  ⟨3, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1235.cov2 (by decide +kernel))⟩,
  ⟨7, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov4 (by decide +kernel))⟩,
  ⟨8, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨11, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1347.cov7 (by decide +kernel))⟩,
  ⟨12, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨13, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov6 (by decide +kernel))⟩,
  ⟨14, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1478.cov9 (by decide +kernel))⟩,
  ⟨0, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov9 (by decide +kernel))⟩,
  ⟨1, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1484.cov9 (by decide +kernel))⟩,
  ⟨3, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1484.cov10 (by decide +kernel))⟩,
  ⟨6, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1484.cov11 (by decide +kernel))⟩,
  ⟨7, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1484.cov12 (by decide +kernel))⟩,
  ⟨8, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov10 (by decide +kernel))⟩,
  ⟨9, tris15, tgt15, cov15⟩,
  ⟨11, tris16, tgt16, cov16⟩,
  ⟨12, tris17, tgt17,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov13 (by decide +kernel))⟩,
  ⟨13, tris18, tgt18, cov18⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨14, tris19, cov19⟩

lemma hJ : J = maskAt 1492 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1492) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1492
#print axioms SquarePacking.S11Opt.Split.U2R.C1492.excluded
