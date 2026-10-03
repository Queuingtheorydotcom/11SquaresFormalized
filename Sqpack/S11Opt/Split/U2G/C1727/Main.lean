import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2G.C1727.Data
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
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1728.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1722.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1728.B004
import Sqpack.S11Opt.Split.U2G.C1727.S10
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C1727.B000
import Sqpack.S11Opt.Split.U2G.C1727.S25

namespace SquarePacking.S11Opt.Split.U2G.C1727
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
  ⟨12, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov9 (by decide +kernel))⟩,
  ⟨13, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1728.cov9 (by decide +kernel))⟩,
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
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1728.cov16 (by decide +kernel))⟩,
  ⟨9, tris17, tgt17,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov17 (by decide +kernel))⟩,
  ⟨10, tris18, tgt18, cov18⟩,
  ⟨12, tris19, tgt19,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov20 (by decide +kernel))⟩,
  ⟨13, tris20, tgt20, cov20⟩,
  ⟨0, tris21, tgt21,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov22 (by decide +kernel))⟩,
  ⟨2, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1728.cov23 (by decide +kernel))⟩,
  ⟨4, tris23, tgt23,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1722.cov25 (by decide +kernel))⟩,
  ⟨5, tris24, tgt24, cov24⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨9, tris25, cov25⟩

lemma hJ : J = maskAt 1727 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1727) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2G.C1727
#print axioms SquarePacking.S11Opt.Split.U2G.C1727.excluded
