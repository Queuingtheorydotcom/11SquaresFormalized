import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C656.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C647.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C647.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C650.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C647.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C654.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1438.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C439.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C654.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C654.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C656.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C656.B000
import Sqpack.S11Opt.Split.U2P.C656.S24

namespace SquarePacking.S11Opt.Split.U2P.C656
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
  ⟨3, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov3 (by decide +kernel))⟩,
  ⟨5, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C647.cov4 (by decide +kernel))⟩,
  ⟨8, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C647.cov5 (by decide +kernel))⟩,
  ⟨11, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov5 (by decide +kernel))⟩,
  ⟨12, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C654.cov7 (by decide +kernel))⟩,
  ⟨14, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1438.cov8 (by decide +kernel))⟩,
  ⟨15, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C439.cov9 (by decide +kernel))⟩,
  ⟨0, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C650.cov9 (by decide +kernel))⟩,
  ⟨1, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C647.cov12 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C647.cov13 (by decide +kernel))⟩,
  ⟨3, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C647.cov14 (by decide +kernel))⟩,
  ⟨5, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C654.cov14 (by decide +kernel))⟩,
  ⟨8, tris15, tgt15, cov15⟩,
  ⟨10, tris16, tgt16, cov16⟩,
  ⟨11, tris17, tgt17, cov17⟩,
  ⟨14, tris18, tgt18, cov18⟩,
  ⟨15, tris19, tgt19, cov19⟩,
  ⟨0, tris20, tgt20,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C654.cov19 (by decide +kernel))⟩,
  ⟨1, tris21, tgt21,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C654.cov20 (by decide +kernel))⟩,
  ⟨2, tris22, tgt22, cov22⟩,
  ⟨5, tris23, tgt23, cov23⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨10, tris24, cov24⟩

lemma hJ : J = maskAt 656 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 656) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C656
#print axioms SquarePacking.S11Opt.Split.U2P.C656.excluded
