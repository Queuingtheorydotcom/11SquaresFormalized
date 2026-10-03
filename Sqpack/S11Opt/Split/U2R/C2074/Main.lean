import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2R.C2074.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C2174.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B004
import Sqpack.S11Opt.Split.U2R.C2047.S4
import Sqpack.S11Opt.Simplified.StageBundles.U2G.C2143.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2R.C2135.B005
import Sqpack.S11Opt.Split.U2R.C2068.S12
import Sqpack.S11Opt.Split.U2R.C2068.S13
import Sqpack.S11Opt.Split.U2R.C2073.S6
import Sqpack.S11Opt.Split.U2R.C2073.S7
import Sqpack.S11Opt.Split.U2R.C2073.S8
import Sqpack.S11Opt.Split.U2R.C2073.S9
import Sqpack.S11Opt.Split.U2R.C2073.S14
import Sqpack.S11Opt.Split.U2R.C2073.S15
import Sqpack.S11Opt.Split.U2R.C2073.S16
import Sqpack.S11Opt.Split.U2R.C2073.S19
import Sqpack.S11Opt.Split.U2R.C2073.S20
import Sqpack.S11Opt.Split.U2R.C2074.S10
import Sqpack.S11Opt.Split.U2R.C2074.S17
import Sqpack.S11Opt.Split.U2R.C2074.S18
import Sqpack.S11Opt.Split.U2R.C2074.S19
import Sqpack.S11Opt.Split.U2R.C2074.S20
import Sqpack.S11Opt.Split.U2R.C2074.S21
import Sqpack.S11Opt.Split.U2R.C2074.S24
import Sqpack.S11Opt.Split.U2R.C2074.S25
import Sqpack.S11Opt.Split.U2R.C2074.S26

namespace SquarePacking.S11Opt.Split.U2R.C2074
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.OwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The original geometric promotions, interpreted by one ownership induction. -/
private def ownedTraceProgram : List Promotion := [
  ⟨1, tris0, tgt0,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov0 (by decide +kernel))⟩,
  ⟨2, tris1, tgt1,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov1 (by decide +kernel))⟩,
  ⟨3, tris2, tgt2,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov2 (by decide +kernel))⟩,
  ⟨4, tris3, tgt3,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C2174.cov2 (by decide +kernel))⟩,
  ⟨5, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2047.cov4 (by decide +kernel))⟩,
  ⟨7, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2135.cov4 (by decide +kernel))⟩,
  ⟨9, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2073.cov6 (by decide +kernel))⟩,
  ⟨10, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2073.cov7 (by decide +kernel))⟩,
  ⟨11, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2073.cov8 (by decide +kernel))⟩,
  ⟨12, tris9, tgt9,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2073.cov9 (by decide +kernel))⟩,
  ⟨14, tris10, tgt10, cov10⟩,
  ⟨1, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2G.C2143.cov9 (by decide +kernel))⟩,
  ⟨2, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2068.cov12 (by decide +kernel))⟩,
  ⟨3, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2068.cov13 (by decide +kernel))⟩,
  ⟨4, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2073.cov14 (by decide +kernel))⟩,
  ⟨5, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2073.cov15 (by decide +kernel))⟩,
  ⟨7, tris16, tgt16,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2073.cov16 (by decide +kernel))⟩,
  ⟨9, tris17, tgt17, cov17⟩,
  ⟨10, tris18, tgt18, cov18⟩,
  ⟨11, tris19, tgt19, cov19⟩,
  ⟨12, tris20, tgt20, cov20⟩,
  ⟨14, tris21, tgt21, cov21⟩,
  ⟨1, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2073.cov19 (by decide +kernel))⟩,
  ⟨2, tris23, tgt23,
    (CovF.weaken SquarePacking.S11Opt.Split.U2R.C2073.cov20 (by decide +kernel))⟩,
  ⟨4, tris24, tgt24, cov24⟩,
  ⟨5, tris25, tgt25, cov25⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨9, tris26, cov26⟩

lemma hJ : J = maskAt 2074 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 2074) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2R.C2074
#print axioms SquarePacking.S11Opt.Split.U2R.C2074.excluded
