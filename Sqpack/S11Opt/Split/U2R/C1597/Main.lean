import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1597.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1411.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1478.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1574.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1574.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1597.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1597.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1597.B001
import Sqpack.S11Opt.Split.U2R.C1597.S24

namespace SquarePacking.S11Opt.Split.U2R.C1597
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
  ⟨5, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov3 (by decide +kernel))⟩,
  ⟨7, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1574.cov3 (by decide +kernel))⟩,
  ⟨8, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov6 (by decide +kernel))⟩,
  ⟨11, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1574.cov6 (by decide +kernel))⟩,
  ⟨12, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov8 (by decide +kernel))⟩,
  ⟨13, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov9 (by decide +kernel))⟩,
  ⟨15, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1574.cov8 (by decide +kernel))⟩,
  ⟨0, tris9, tgt9, cov9⟩,
  ⟨1, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov12 (by decide +kernel))⟩,
  ⟨5, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1478.cov13 (by decide +kernel))⟩,
  ⟨6, tris12, tgt12, cov12⟩,
  ⟨7, tris13, tgt13, cov13⟩,
  ⟨8, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1478.cov15 (by decide +kernel))⟩,
  ⟨10, tris15, tgt15, cov15⟩,
  ⟨11, tris16, tgt16, cov16⟩,
  ⟨12, tris17, tgt17,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1478.cov18 (by decide +kernel))⟩,
  ⟨13, tris18, tgt18, cov18⟩,
  ⟨15, tris19, tgt19, cov19⟩,
  ⟨5, tris20, tgt20, cov20⟩,
  ⟨6, tris21, tgt21, cov21⟩,
  ⟨7, tris22, tgt22, cov22⟩,
  ⟨10, tris23, tgt23, cov23⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨11, tris24, cov24⟩

lemma hJ : J = maskAt 1597 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1597) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1597
#print axioms SquarePacking.S11Opt.Split.U2R.C1597.excluded
