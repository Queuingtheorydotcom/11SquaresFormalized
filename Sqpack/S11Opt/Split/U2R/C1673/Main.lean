import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1673.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.B001
import Sqpack.S11Opt.Split.U2R.C1673.S22

namespace SquarePacking.S11Opt.Split.U2R.C1673
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
  ⟨4, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov3 (by decide +kernel))⟩,
  ⟨5, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov4 (by decide +kernel))⟩,
  ⟨6, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov5 (by decide +kernel))⟩,
  ⟨8, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov7 (by decide +kernel))⟩,
  ⟨9, tris7, tgt7, cov7⟩,
  ⟨11, tris8, tgt8, cov8⟩,
  ⟨13, tris9, tgt9, cov9⟩,
  ⟨14, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12, cov12⟩,
  ⟨3, tris13, tgt13, cov13⟩,
  ⟨4, tris14, tgt14, cov14⟩,
  ⟨5, tris15, tgt15, cov15⟩,
  ⟨6, tris16, tgt16, cov16⟩,
  ⟨8, tris17, tgt17, cov17⟩,
  ⟨9, tris18, tgt18, cov18⟩,
  ⟨0, tris19, tgt19, cov19⟩,
  ⟨2, tris20, tgt20, cov20⟩,
  ⟨4, tris21, tgt21, cov21⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, tris22, cov22⟩

lemma hJ : J = maskAt 1673 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1673) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1673
#print axioms SquarePacking.S11Opt.Split.U2R.C1673.excluded
