import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1374.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B014
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B018
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1335.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1365.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1335.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1347.B000
import Sqpack.S11Opt.Split.U2R.C1365.S11
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1365.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1365.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1374.B000
import Sqpack.S11Opt.Split.U2R.C1374.S19

namespace SquarePacking.S11Opt.Split.U2R.C1374
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
  ⟨4, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov4 (by decide +kernel))⟩,
  ⟨7, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov4 (by decide +kernel))⟩,
  ⟨11, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1347.cov7 (by decide +kernel))⟩,
  ⟨12, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov6 (by decide +kernel))⟩,
  ⟨13, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov7 (by decide +kernel))⟩,
  ⟨14, tris8, tgt8, cov8⟩,
  ⟨0, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov9 (by decide +kernel))⟩,
  ⟨1, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1365.cov9 (by decide +kernel))⟩,
  ⟨3, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov12 (by decide +kernel))⟩,
  ⟨4, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1365.cov11 (by decide +kernel))⟩,
  ⟨6, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1365.cov12 (by decide +kernel))⟩,
  ⟨7, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1365.cov13 (by decide +kernel))⟩,
  ⟨9, tris15, tgt15, cov15⟩,
  ⟨11, tris16, tgt16, cov16⟩,
  ⟨12, tris17, tgt17, cov17⟩,
  ⟨13, tris18, tgt18, cov18⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨14, tris19, cov19⟩

lemma hJ : J = maskAt 1374 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1374) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1374
#print axioms SquarePacking.S11Opt.Split.U2R.C1374.excluded
