import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1823.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.B001
import Sqpack.S11Opt.Split.U2P.C2176.S6
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1810.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1810.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1810.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1810.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1822.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1822.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1823.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1823.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1823.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1823.B000
import Sqpack.S11Opt.Split.U2R.C1823.S38
import Sqpack.S11Opt.Split.U2R.C1823.S39

namespace SquarePacking.S11Opt.Split.U2R.C1823
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
  ⟨6, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov4 (by decide +kernel))⟩,
  ⟨7, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov5 (by decide +kernel))⟩,
  ⟨8, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨11, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1810.cov7 (by decide +kernel))⟩,
  ⟨12, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨13, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2176.cov6 (by decide +kernel))⟩,
  ⟨14, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov9 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov10 (by decide +kernel))⟩,
  ⟨3, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov11 (by decide +kernel))⟩,
  ⟨5, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov12 (by decide +kernel))⟩,
  ⟨6, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1810.cov14 (by decide +kernel))⟩,
  ⟨7, tris16, tgt16,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1810.cov15 (by decide +kernel))⟩,
  ⟨8, tris17, tgt17,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1822.cov16 (by decide +kernel))⟩,
  ⟨11, tris18, tgt18, cov18⟩,
  ⟨12, tris19, tgt19,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1822.cov18 (by decide +kernel))⟩,
  ⟨13, tris20, tgt20, cov20⟩,
  ⟨14, tris21, tgt21, cov21⟩,
  ⟨0, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1810.cov21 (by decide +kernel))⟩,
  ⟨2, tris23, tgt23,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1810.cov22 (by decide +kernel))⟩,
  ⟨3, tris24, tgt24,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1810.cov23 (by decide +kernel))⟩,
  ⟨5, tris25, tgt25, cov25⟩,
  ⟨6, tris26, tgt26, cov26⟩,
  ⟨7, tris27, tgt27, cov27⟩,
  ⟨8, tris28, tgt28, cov28⟩,
  ⟨11, tris29, tgt29, cov29⟩,
  ⟨12, tris30, tgt30, cov30⟩,
  ⟨13, tris31, tgt31, cov31⟩,
  ⟨14, tris32, tgt32, cov32⟩,
  ⟨0, tris33, tgt33, cov33⟩,
  ⟨2, tris34, tgt34, cov34⟩,
  ⟨5, tris35, tgt35, cov35⟩,
  ⟨6, tris36, tgt36, cov36⟩,
  ⟨8, tris37, tgt37, cov37⟩,
  ⟨12, tris38, tgt38, cov38⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨13, tris39, cov39⟩

lemma hJ : J = maskAt 1823 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1823) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1823
#print axioms SquarePacking.S11Opt.Split.U2R.C1823.excluded
