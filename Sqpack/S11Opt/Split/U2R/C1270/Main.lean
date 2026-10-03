import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1270.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1235.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1248.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1248.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1261.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1538.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1249.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1269.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1269.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1270.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1270.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1270.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1270.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1270.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1270.B005

namespace SquarePacking.S11Opt.Split.U2R.C1270
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
  ⟨10, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1248.cov7 (by decide +kernel))⟩,
  ⟨11, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1248.cov8 (by decide +kernel))⟩,
  ⟨12, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov6 (by decide +kernel))⟩,
  ⟨13, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1269.cov9 (by decide +kernel))⟩,
  ⟨15, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1249.cov10 (by decide +kernel))⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1261.cov9 (by decide +kernel))⟩,
  ⟨1, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1538.cov9 (by decide +kernel))⟩,
  ⟨3, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1248.cov13 (by decide +kernel))⟩,
  ⟨4, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1269.cov14 (by decide +kernel))⟩,
  ⟨5, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1269.cov15 (by decide +kernel))⟩,
  ⟨6, tris16, tgt16,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1269.cov16 (by decide +kernel))⟩,
  ⟨10, tris17, tgt17, cov17⟩,
  ⟨11, tris18, tgt18, cov18⟩,
  ⟨12, tris19, tgt19, cov19⟩,
  ⟨13, tris20, tgt20, cov20⟩,
  ⟨15, tris21, tgt21, cov21⟩,
  ⟨0, tris22, tgt22, cov22⟩,
  ⟨1, tris23, tgt23, cov23⟩,
  ⟨3, tris24, tgt24, cov24⟩,
  ⟨4, tris25, tgt25, cov25⟩,
  ⟨5, tris26, tgt26, cov26⟩,
  ⟨6, tris27, tgt27, cov27⟩,
  ⟨10, tris28, tgt28, cov28⟩,
  ⟨11, tris29, tgt29, cov29⟩,
  ⟨12, tris30, tgt30, cov30⟩,
  ⟨13, tris31, tgt31, cov31⟩,
  ⟨15, tris32, tgt32, cov32⟩,
  ⟨0, tris33, tgt33, cov33⟩,
  ⟨1, tris34, tgt34, cov34⟩,
  ⟨3, tris35, tgt35, cov35⟩,
  ⟨4, tris36, tgt36, cov36⟩,
  ⟨5, tris37, tgt37, cov37⟩,
  ⟨6, tris38, tgt38, cov38⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris39, cov39⟩

lemma hJ : J = maskAt 1270 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1270) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1270
#print axioms SquarePacking.S11Opt.Split.U2R.C1270.excluded
