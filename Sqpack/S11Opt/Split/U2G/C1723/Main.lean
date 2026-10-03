import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2G.C1723.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1716.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1716.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1722.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1722.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1722.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1722.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C1723.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C1723.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C1723.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C1723.B000
import Sqpack.S11Opt.Split.U2G.C1723.S33
import Sqpack.S11Opt.Split.U2G.C1723.S40

namespace SquarePacking.S11Opt.Split.U2G.C1723
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
  ⟨7, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1716.cov5 (by decide +kernel))⟩,
  ⟨9, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov6 (by decide +kernel))⟩,
  ⟨10, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov7 (by decide +kernel))⟩,
  ⟨11, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov8 (by decide +kernel))⟩,
  ⟨12, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov9 (by decide +kernel))⟩,
  ⟨14, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1716.cov11 (by decide +kernel))⟩,
  ⟨3, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1716.cov12 (by decide +kernel))⟩,
  ⟨4, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov14 (by decide +kernel))⟩,
  ⟨5, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov15 (by decide +kernel))⟩,
  ⟨7, tris16, tgt16,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov16 (by decide +kernel))⟩,
  ⟨9, tris17, tgt17, cov17⟩,
  ⟨10, tris18, tgt18, cov18⟩,
  ⟨11, tris19, tgt19, cov19⟩,
  ⟨12, tris20, tgt20, cov20⟩,
  ⟨14, tris21, tgt21, cov21⟩,
  ⟨0, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov22 (by decide +kernel))⟩,
  ⟨2, tris23, tgt23,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov23 (by decide +kernel))⟩,
  ⟨3, tris24, tgt24,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov24 (by decide +kernel))⟩,
  ⟨4, tris25, tgt25, cov25⟩,
  ⟨5, tris26, tgt26, cov26⟩,
  ⟨7, tris27, tgt27, cov27⟩,
  ⟨9, tris28, tgt28, cov28⟩,
  ⟨10, tris29, tgt29, cov29⟩,
  ⟨11, tris30, tgt30, cov30⟩,
  ⟨12, tris31, tgt31, cov31⟩,
  ⟨14, tris32, tgt32, cov32⟩,
  ⟨0, tris33, tgt33, cov33⟩,
  ⟨2, tris34, tgt34, cov34⟩,
  ⟨3, tris35, tgt35, cov35⟩,
  ⟨4, tris36, tgt36, cov36⟩,
  ⟨5, tris37, tgt37, cov37⟩,
  ⟨7, tris38, tgt38, cov38⟩,
  ⟨9, tris39, tgt39, cov39⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris40, cov40⟩

lemma hJ : J = maskAt 1723 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1723) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2G.C1723
#print axioms SquarePacking.S11Opt.Split.U2G.C1723.excluded
