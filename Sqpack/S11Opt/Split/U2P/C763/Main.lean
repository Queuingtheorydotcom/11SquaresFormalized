import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C763.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C647.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.B002
import Sqpack.S11Opt.Split.U2P.C763.S9
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C763.B001
import Sqpack.S11Opt.Split.U2P.C763.S29

namespace SquarePacking.S11Opt.Split.U2P.C763
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
  ⟨8, tris4, tgt4, cov4⟩,
  ⟨11, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov5 (by decide +kernel))⟩,
  ⟨13, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov7 (by decide +kernel))⟩,
  ⟨14, tris7, tgt7, cov7⟩,
  ⟨15, tris8, tgt8, cov8⟩,
  ⟨0, tris9, tgt9, cov9⟩,
  ⟨1, tris10, tgt10, cov10⟩,
  ⟨2, tris11, tgt11, cov11⟩,
  ⟨3, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C647.cov14 (by decide +kernel))⟩,
  ⟨8, tris13, tgt13, cov13⟩,
  ⟨9, tris14, tgt14, cov14⟩,
  ⟨10, tris15, tgt15, cov15⟩,
  ⟨11, tris16, tgt16, cov16⟩,
  ⟨13, tris17, tgt17, cov17⟩,
  ⟨14, tris18, tgt18, cov18⟩,
  ⟨15, tris19, tgt19, cov19⟩,
  ⟨0, tris20, tgt20, cov20⟩,
  ⟨1, tris21, tgt21, cov21⟩,
  ⟨2, tris22, tgt22, cov22⟩,
  ⟨3, tris23, tgt23, cov23⟩,
  ⟨8, tris24, tgt24, cov24⟩,
  ⟨9, tris25, tgt25, cov25⟩,
  ⟨10, tris26, tgt26, cov26⟩,
  ⟨0, tris27, tgt27, cov27⟩,
  ⟨1, tris28, tgt28, cov28⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨2, tris29, cov29⟩

lemma hJ : J = maskAt 763 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 763) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C763
#print axioms SquarePacking.S11Opt.Split.U2P.C763.excluded
