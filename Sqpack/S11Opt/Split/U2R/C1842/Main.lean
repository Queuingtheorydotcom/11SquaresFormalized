import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1842.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.B001
import Sqpack.S11Opt.Split.U2P.C2176.S6
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1716.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1716.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1842.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1842.B000
import Sqpack.S11Opt.Split.U2R.C1842.S17

namespace SquarePacking.S11Opt.Split.U2R.C1842
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨0, tris0, tgt0,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov0 (by decide +kernel))⟩,
  ⟨2, tris1, tgt1,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov0 (by decide +kernel))⟩,
  ⟨3, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2178.cov1 (by decide +kernel))⟩,
  ⟨5, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov3 (by decide +kernel))⟩,
  ⟨7, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1716.cov5 (by decide +kernel))⟩,
  ⟨8, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨11, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1716.cov7 (by decide +kernel))⟩,
  ⟨12, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨13, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov6 (by decide +kernel))⟩,
  ⟨0, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov9 (by decide +kernel))⟩,
  ⟨2, tris10, tgt10, cov10⟩,
  ⟨3, tris11, tgt11, cov11⟩,
  ⟨5, tris12, tgt12, cov12⟩,
  ⟨7, tris13, tgt13, cov13⟩,
  ⟨8, tris14, tgt14, cov14⟩,
  ⟨9, tris15, tgt15, cov15⟩,
  ⟨10, tris16, tgt16, cov16⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨11, tris17, cov17⟩

lemma hJ : J = maskAt 1842 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1842) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1842
#print axioms SquarePacking.S11Opt.Split.U2R.C1842.excluded
