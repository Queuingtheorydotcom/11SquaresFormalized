import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1866.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1621.B001
import Sqpack.S11Opt.Split.U2R.C1864.S4
import Sqpack.S11Opt.Split.U2R.C1864.S5
import Sqpack.S11Opt.Split.U2R.C1864.S7
import Sqpack.S11Opt.Split.U2R.C1864.S8
import Sqpack.S11Opt.Split.U2R.C1864.S9
import Sqpack.S11Opt.Split.U2R.C1864.S12
import Sqpack.S11Opt.Split.U2R.C1864.S13
import Sqpack.S11Opt.Split.U2R.C1864.S14
import Sqpack.S11Opt.Split.U2R.C1864.S15
import Sqpack.S11Opt.Split.U2R.C1866.S10
import Sqpack.S11Opt.Split.U2R.C1866.S16
import Sqpack.S11Opt.Split.U2R.C1866.S17
import Sqpack.S11Opt.Split.U2R.C1866.S18
import Sqpack.S11Opt.Split.U2R.C1866.S19
import Sqpack.S11Opt.Split.U2R.C1866.S20
import Sqpack.S11Opt.Split.U2R.C1866.S21
import Sqpack.S11Opt.Split.U2R.C1866.S22
import Sqpack.S11Opt.Split.U2R.C1866.S23
import Sqpack.S11Opt.Split.U2R.C1866.S24
import Sqpack.S11Opt.Split.U2R.C1866.S25

namespace SquarePacking.S11Opt.Split.U2R.C1866
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
  ⟨4, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov3 (by decide +kernel))⟩,
  ⟨5, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov4 (by decide +kernel))⟩,
  ⟨6, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov4 (by decide +kernel))⟩,
  ⟨7, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov5 (by decide +kernel))⟩,
  ⟨8, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov7 (by decide +kernel))⟩,
  ⟨9, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov7 (by decide +kernel))⟩,
  ⟨10, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov8 (by decide +kernel))⟩,
  ⟨11, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov9 (by decide +kernel))⟩,
  ⟨15, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1621.cov10 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov12 (by decide +kernel))⟩,
  ⟨4, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov13 (by decide +kernel))⟩,
  ⟨5, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov14 (by decide +kernel))⟩,
  ⟨6, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1864.cov15 (by decide +kernel))⟩,
  ⟨7, tris16, tgt16, cov16⟩,
  ⟨8, tris17, tgt17, cov17⟩,
  ⟨9, tris18, tgt18, cov18⟩,
  ⟨10, tris19, tgt19, cov19⟩,
  ⟨11, tris20, tgt20, cov20⟩,
  ⟨0, tris21, tgt21, cov21⟩,
  ⟨2, tris22, tgt22, cov22⟩,
  ⟨4, tris23, tgt23, cov23⟩,
  ⟨5, tris24, tgt24, cov24⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨6, tris25, cov25⟩

lemma hJ : J = maskAt 1866 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1866) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1866
#print axioms SquarePacking.S11Opt.Split.U2R.C1866.excluded
