import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1145.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C958.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C958.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.B001
import Sqpack.S11Opt.Split.U2P.C763.S9
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C1143.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1145.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1145.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1145.B000
import Sqpack.S11Opt.Split.U2R.C1145.S25

namespace SquarePacking.S11Opt.Split.U2R.C1145
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
  ⟨6, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C958.cov4 (by decide +kernel))⟩,
  ⟨7, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C958.cov5 (by decide +kernel))⟩,
  ⟨8, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov4 (by decide +kernel))⟩,
  ⟨10, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov6 (by decide +kernel))⟩,
  ⟨12, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov7 (by decide +kernel))⟩,
  ⟨14, tris8, tgt8, cov8⟩,
  ⟨15, tris9, tgt9, cov9⟩,
  ⟨0, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov9 (by decide +kernel))⟩,
  ⟨1, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C763.cov10 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov12 (by decide +kernel))⟩,
  ⟨6, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov13 (by decide +kernel))⟩,
  ⟨7, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C1143.cov14 (by decide +kernel))⟩,
  ⟨8, tris15, tgt15, cov15⟩,
  ⟨9, tris16, tgt16, cov16⟩,
  ⟨10, tris17, tgt17, cov17⟩,
  ⟨12, tris18, tgt18, cov18⟩,
  ⟨14, tris19, tgt19, cov19⟩,
  ⟨0, tris20, tgt20, cov20⟩,
  ⟨1, tris21, tgt21, cov21⟩,
  ⟨2, tris22, tgt22, cov22⟩,
  ⟨6, tris23, tgt23, cov23⟩,
  ⟨8, tris24, tgt24, cov24⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨9, tris25, cov25⟩

lemma hJ : J = maskAt 1145 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1145) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1145
#print axioms SquarePacking.S11Opt.Split.U2R.C1145.excluded
