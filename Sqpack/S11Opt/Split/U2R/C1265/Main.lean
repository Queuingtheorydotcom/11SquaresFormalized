import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1265.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1261.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1538.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1248.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1257.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1257.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1262.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1258.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1259.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1259.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1265.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1265.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1265.B000
import Sqpack.S11Opt.Split.U2R.C1265.S31

namespace SquarePacking.S11Opt.Split.U2R.C1265
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
  ⟨5, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1235.cov4 (by decide +kernel))⟩,
  ⟨6, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1235.cov5 (by decide +kernel))⟩,
  ⟨9, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1257.cov6 (by decide +kernel))⟩,
  ⟨10, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1257.cov7 (by decide +kernel))⟩,
  ⟨12, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1257.cov8 (by decide +kernel))⟩,
  ⟨14, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1262.cov9 (by decide +kernel))⟩,
  ⟨15, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1261.cov9 (by decide +kernel))⟩,
  ⟨1, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1538.cov9 (by decide +kernel))⟩,
  ⟨3, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1248.cov13 (by decide +kernel))⟩,
  ⟨4, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1257.cov12 (by decide +kernel))⟩,
  ⟨5, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1257.cov13 (by decide +kernel))⟩,
  ⟨6, tris16, tgt16, cov16⟩,
  ⟨9, tris17, tgt17,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1258.cov17 (by decide +kernel))⟩,
  ⟨10, tris18, tgt18, cov18⟩,
  ⟨12, tris19, tgt19, cov19⟩,
  ⟨14, tris20, tgt20, cov20⟩,
  ⟨0, tris21, tgt21,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1259.cov22 (by decide +kernel))⟩,
  ⟨1, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1259.cov23 (by decide +kernel))⟩,
  ⟨3, tris23, tgt23, cov23⟩,
  ⟨4, tris24, tgt24, cov24⟩,
  ⟨5, tris25, tgt25, cov25⟩,
  ⟨6, tris26, tgt26, cov26⟩,
  ⟨9, tris27, tgt27, cov27⟩,
  ⟨0, tris28, tgt28, cov28⟩,
  ⟨1, tris29, tgt29, cov29⟩,
  ⟨4, tris30, tgt30, cov30⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨5, tris31, cov31⟩

lemma hJ : J = maskAt 1265 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1265) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1265
#print axioms SquarePacking.S11Opt.Split.U2R.C1265.excluded
