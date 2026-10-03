import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1476.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1335.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1347.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1411.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1597.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1416.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1430.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1476.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1476.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1476.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1476.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1476.B003
import Sqpack.S11Opt.Split.U2R.C1476.S32

namespace SquarePacking.S11Opt.Split.U2R.C1476
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
  ⟨5, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov3 (by decide +kernel))⟩,
  ⟨7, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1335.cov4 (by decide +kernel))⟩,
  ⟨8, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1411.cov6 (by decide +kernel))⟩,
  ⟨9, tris6, tgt6, cov6⟩,
  ⟨11, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1347.cov7 (by decide +kernel))⟩,
  ⟨12, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1430.cov8 (by decide +kernel))⟩,
  ⟨13, tris9, tgt9, cov9⟩,
  ⟨14, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1597.cov9 (by decide +kernel))⟩,
  ⟨1, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1416.cov12 (by decide +kernel))⟩,
  ⟨3, tris13, tgt13, cov13⟩,
  ⟨5, tris14, tgt14, cov14⟩,
  ⟨7, tris15, tgt15, cov15⟩,
  ⟨8, tris16, tgt16, cov16⟩,
  ⟨9, tris17, tgt17, cov17⟩,
  ⟨11, tris18, tgt18, cov18⟩,
  ⟨12, tris19, tgt19, cov19⟩,
  ⟨13, tris20, tgt20, cov20⟩,
  ⟨14, tris21, tgt21, cov21⟩,
  ⟨0, tris22, tgt22, cov22⟩,
  ⟨1, tris23, tgt23, cov23⟩,
  ⟨3, tris24, tgt24, cov24⟩,
  ⟨5, tris25, tgt25, cov25⟩,
  ⟨7, tris26, tgt26, cov26⟩,
  ⟨8, tris27, tgt27, cov27⟩,
  ⟨9, tris28, tgt28, cov28⟩,
  ⟨11, tris29, tgt29, cov29⟩,
  ⟨12, tris30, tgt30, cov30⟩,
  ⟨13, tris31, tgt31, cov31⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨14, tris32, cov32⟩

lemma hJ : J = maskAt 1476 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1476) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1476
#print axioms SquarePacking.S11Opt.Split.U2R.C1476.excluded
