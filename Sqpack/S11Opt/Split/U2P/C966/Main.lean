import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C966.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C958.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C958.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B014
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C439.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C439.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C958.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C965.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C965.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C966.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C966.B000
import Sqpack.S11Opt.Split.U2P.C966.S27

namespace SquarePacking.S11Opt.Split.U2P.C966
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
  ⟨2, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov2 (by decide +kernel))⟩,
  ⟨4, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov4 (by decide +kernel))⟩,
  ⟨6, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C958.cov4 (by decide +kernel))⟩,
  ⟨7, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C958.cov5 (by decide +kernel))⟩,
  ⟨8, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C439.cov5 (by decide +kernel))⟩,
  ⟨9, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C958.cov7 (by decide +kernel))⟩,
  ⟨10, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C958.cov8 (by decide +kernel))⟩,
  ⟨14, tris9, tgt9, cov9⟩,
  ⟨15, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov9 (by decide +kernel))⟩,
  ⟨1, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C439.cov11 (by decide +kernel))⟩,
  ⟨2, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C958.cov13 (by decide +kernel))⟩,
  ⟨4, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C958.cov14 (by decide +kernel))⟩,
  ⟨6, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C965.cov15 (by decide +kernel))⟩,
  ⟨7, tris16, tgt16,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C965.cov16 (by decide +kernel))⟩,
  ⟨8, tris17, tgt17, cov17⟩,
  ⟨9, tris18, tgt18, cov18⟩,
  ⟨10, tris19, tgt19, cov19⟩,
  ⟨14, tris20, tgt20, cov20⟩,
  ⟨0, tris21, tgt21,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C965.cov20 (by decide +kernel))⟩,
  ⟨1, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C965.cov21 (by decide +kernel))⟩,
  ⟨2, tris23, tgt23,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C965.cov22 (by decide +kernel))⟩,
  ⟨4, tris24, tgt24, cov24⟩,
  ⟨6, tris25, tgt25, cov25⟩,
  ⟨8, tris26, tgt26, cov26⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨9, tris27, cov27⟩

lemma hJ : J = maskAt 966 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 966) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C966
#print axioms SquarePacking.S11Opt.Split.U2P.C966.excluded
