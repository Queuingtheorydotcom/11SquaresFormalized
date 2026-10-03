import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1582.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B014
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B018
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1365.B002
import Sqpack.S11Opt.Split.U2R.C1365.S11
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1574.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1574.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1582.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1582.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1582.B000
import Sqpack.S11Opt.Split.U2R.C1582.S22

namespace SquarePacking.S11Opt.Split.U2R.C1582
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
  ⟨4, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov4 (by decide +kernel))⟩,
  ⟨7, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1574.cov3 (by decide +kernel))⟩,
  ⟨11, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1574.cov6 (by decide +kernel))⟩,
  ⟨12, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov6 (by decide +kernel))⟩,
  ⟨13, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov7 (by decide +kernel))⟩,
  ⟨15, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1574.cov8 (by decide +kernel))⟩,
  ⟨0, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov9 (by decide +kernel))⟩,
  ⟨1, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1365.cov9 (by decide +kernel))⟩,
  ⟨4, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1365.cov11 (by decide +kernel))⟩,
  ⟨6, tris11, tgt11, cov11⟩,
  ⟨7, tris12, tgt12, cov12⟩,
  ⟨9, tris13, tgt13, cov13⟩,
  ⟨10, tris14, tgt14, cov14⟩,
  ⟨11, tris15, tgt15, cov15⟩,
  ⟨12, tris16, tgt16, cov16⟩,
  ⟨13, tris17, tgt17, cov17⟩,
  ⟨15, tris18, tgt18, cov18⟩,
  ⟨4, tris19, tgt19, cov19⟩,
  ⟨6, tris20, tgt20, cov20⟩,
  ⟨9, tris21, tgt21, cov21⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris22, cov22⟩

lemma hJ : J = maskAt 1582 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1582) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1582
#print axioms SquarePacking.S11Opt.Split.U2R.C1582.excluded
