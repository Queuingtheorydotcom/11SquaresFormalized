import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2G.C1681.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1673.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1674.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1680.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1680.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C1681.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C1681.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C1681.B002
import Sqpack.S11Opt.Split.U2G.C1681.S30

namespace SquarePacking.S11Opt.Split.U2G.C1681
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
  ⟨11, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1673.cov8 (by decide +kernel))⟩,
  ⟨13, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov9 (by decide +kernel))⟩,
  ⟨15, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1674.cov9 (by decide +kernel))⟩,
  ⟨0, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1673.cov12 (by decide +kernel))⟩,
  ⟨3, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1673.cov13 (by decide +kernel))⟩,
  ⟨4, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov13 (by decide +kernel))⟩,
  ⟨5, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1680.cov14 (by decide +kernel))⟩,
  ⟨6, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1680.cov15 (by decide +kernel))⟩,
  ⟨8, tris16, tgt16,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1680.cov16 (by decide +kernel))⟩,
  ⟨10, tris17, tgt17, cov17⟩,
  ⟨11, tris18, tgt18, cov18⟩,
  ⟨13, tris19, tgt19, cov19⟩,
  ⟨0, tris20, tgt20,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1680.cov18 (by decide +kernel))⟩,
  ⟨2, tris21, tgt21,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1680.cov19 (by decide +kernel))⟩,
  ⟨3, tris22, tgt22, cov22⟩,
  ⟨4, tris23, tgt23,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1680.cov20 (by decide +kernel))⟩,
  ⟨5, tris24, tgt24, cov24⟩,
  ⟨6, tris25, tgt25, cov25⟩,
  ⟨8, tris26, tgt26, cov26⟩,
  ⟨0, tris27, tgt27, cov27⟩,
  ⟨2, tris28, tgt28, cov28⟩,
  ⟨4, tris29, tgt29, cov29⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, tris30, cov30⟩

lemma hJ : J = maskAt 1681 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1681) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2G.C1681
#print axioms SquarePacking.S11Opt.Split.U2G.C1681.excluded
