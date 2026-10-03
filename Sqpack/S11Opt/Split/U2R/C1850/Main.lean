import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C1850.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2178.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C455.B018
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1696.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1716.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1716.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1731.B007
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1805.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1842.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1842.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C1848.B001
import Sqpack.S11Opt.Split.U2R.C1850.S12
import Sqpack.S11Opt.Split.U2R.C1850.S14
import Sqpack.S11Opt.Split.U2R.C1850.S15
import Sqpack.S11Opt.Split.U2R.C1850.S17
import Sqpack.S11Opt.Split.U2R.C1850.S18
import Sqpack.S11Opt.Split.U2R.C1850.S20
import Sqpack.S11Opt.Split.U2R.C1850.S21
import Sqpack.S11Opt.Split.U2R.C1850.S22
import Sqpack.S11Opt.Split.U2R.C1850.S23
import Sqpack.S11Opt.Split.U2R.C1850.S24
import Sqpack.S11Opt.Split.U2R.C1850.S25
import Sqpack.S11Opt.Split.U2R.C1850.S26
import Sqpack.S11Opt.Split.U2R.C1850.S27
import Sqpack.S11Opt.Split.U2R.C1850.S28
import Sqpack.S11Opt.Split.U2R.C1850.S29

namespace SquarePacking.S11Opt.Split.U2R.C1850
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
  ⟨7, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1716.cov5 (by decide +kernel))⟩,
  ⟨11, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1716.cov7 (by decide +kernel))⟩,
  ⟨12, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov6 (by decide +kernel))⟩,
  ⟨13, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C455.cov7 (by decide +kernel))⟩,
  ⟨14, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1731.cov9 (by decide +kernel))⟩,
  ⟨0, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1805.cov9 (by decide +kernel))⟩,
  ⟨2, tris10, tgt10,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1842.cov10 (by decide +kernel))⟩,
  ⟨3, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1842.cov11 (by decide +kernel))⟩,
  ⟨5, tris12, tgt12, cov12⟩,
  ⟨7, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1842.cov13 (by decide +kernel))⟩,
  ⟨10, tris14, tgt14, cov14⟩,
  ⟨11, tris15, tgt15, cov15⟩,
  ⟨12, tris16, tgt16,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1696.cov18 (by decide +kernel))⟩,
  ⟨13, tris17, tgt17, cov17⟩,
  ⟨14, tris18, tgt18, cov18⟩,
  ⟨0, tris19, tgt19,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C1848.cov21 (by decide +kernel))⟩,
  ⟨2, tris20, tgt20, cov20⟩,
  ⟨3, tris21, tgt21, cov21⟩,
  ⟨5, tris22, tgt22, cov22⟩,
  ⟨7, tris23, tgt23, cov23⟩,
  ⟨9, tris24, tgt24, cov24⟩,
  ⟨10, tris25, tgt25, cov25⟩,
  ⟨11, tris26, tgt26, cov26⟩,
  ⟨12, tris27, tgt27, cov27⟩,
  ⟨13, tris28, tgt28, cov28⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨14, tris29, cov29⟩

lemma hJ : J = maskAt 1850 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 1850) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C1850
#print axioms SquarePacking.S11Opt.Split.U2R.C1850.excluded
