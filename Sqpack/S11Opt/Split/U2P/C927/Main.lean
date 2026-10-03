import Sqpack.S11Opt.Simplified.OwnedTrace
import Sqpack.S11Opt.Simplified.CoverageMonotone
import Sqpack.S11Opt.Split.U2P.C927.Data
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C221.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C894.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C919.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C919.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C926.B000
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C926.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C927.B011
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C927.B003
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C927.B001
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C927.B010
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C927.B009
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C927.B008
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C927.B002
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C927.B007
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C927.B004
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C927.B006
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C927.B005
import Sqpack.S11Opt.Simplified.StageBundles.U2P.C927.B000

namespace SquarePacking.S11Opt.Split.U2P.C927
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
  ⟨5, tris4, tgt4,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov5 (by decide +kernel))⟩,
  ⟨7, tris5, tgt5,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C894.cov5 (by decide +kernel))⟩,
  ⟨9, tris6, tgt6,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C919.cov6 (by decide +kernel))⟩,
  ⟨10, tris7, tgt7,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C919.cov7 (by decide +kernel))⟩,
  ⟨12, tris8, tgt8,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C919.cov9 (by decide +kernel))⟩,
  ⟨14, tris9, tgt9, cov9⟩,
  ⟨15, tris10, tgt10, cov10⟩,
  ⟨0, tris11, tgt11,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov7 (by decide +kernel))⟩,
  ⟨1, tris12, tgt12,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C221.cov8 (by decide +kernel))⟩,
  ⟨2, tris13, tgt13,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C919.cov13 (by decide +kernel))⟩,
  ⟨4, tris14, tgt14,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C919.cov14 (by decide +kernel))⟩,
  ⟨5, tris15, tgt15,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C919.cov15 (by decide +kernel))⟩,
  ⟨7, tris16, tgt16,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C926.cov16 (by decide +kernel))⟩,
  ⟨9, tris17, tgt17, cov17⟩,
  ⟨10, tris18, tgt18, cov18⟩,
  ⟨12, tris19, tgt19, cov19⟩,
  ⟨14, tris20, tgt20, cov20⟩,
  ⟨15, tris21, tgt21, cov21⟩,
  ⟨0, tris22, tgt22,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C926.cov19 (by decide +kernel))⟩,
  ⟨1, tris23, tgt23,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C926.cov20 (by decide +kernel))⟩,
  ⟨2, tris24, tgt24,
    (CovF.weaken SquarePacking.S11Opt.Split.U2P.C926.cov21 (by decide +kernel))⟩,
  ⟨4, tris25, tgt25, cov25⟩,
  ⟨5, tris26, tgt26, cov26⟩,
  ⟨7, tris27, tgt27, cov27⟩,
  ⟨9, tris28, tgt28, cov28⟩,
  ⟨10, tris29, tgt29, cov29⟩,
  ⟨12, tris30, tgt30, cov30⟩,
  ⟨14, tris31, tgt31, cov31⟩,
  ⟨15, tris32, tgt32, cov32⟩,
  ⟨0, tris33, tgt33, cov33⟩,
  ⟨1, tris34, tgt34, cov34⟩,
  ⟨2, tris35, tgt35, cov35⟩,
  ⟨4, tris36, tgt36, cov36⟩,
  ⟨5, tris37, tgt37, cov37⟩,
  ⟨7, tris38, tgt38, cov38⟩,
  ⟨9, tris39, tgt39, cov39⟩,
  ⟨10, tris40, tgt40, cov40⟩,
  ⟨12, tris41, tgt41, cov41⟩,
  ⟨14, tris42, tgt42, cov42⟩,
  ⟨15, tris43, tgt43, cov43⟩,
  ⟨0, tris44, tgt44, cov44⟩,
  ⟨1, tris45, tgt45, cov45⟩,
  ⟨2, tris46, tgt46, cov46⟩,
  ⟨4, tris47, tgt47, cov47⟩,
  ⟨5, tris48, tgt48, cov48⟩,
  ⟨7, tris49, tgt49, cov49⟩,
  ⟨9, tris50, tgt50, cov50⟩,
  ⟨10, tris51, tgt51, cov51⟩,
  ⟨12, tris52, tgt52, cov52⟩,
  ⟨14, tris53, tgt53, cov53⟩,
  ⟨15, tris54, tgt54, cov54⟩,
  ⟨0, tris55, tgt55, cov55⟩,
  ⟨1, tris56, tgt56, cov56⟩,
  ⟨2, tris57, tgt57, cov57⟩,
  ⟨4, tris58, tgt58, cov58⟩,
  ⟨5, tris59, tgt59, cov59⟩,
  ⟨7, tris60, tgt60, cov60⟩,
  ⟨9, tris61, tgt61, cov61⟩,
  ⟨10, tris62, tgt62, cov62⟩,
  ⟨12, tris63, tgt63, cov63⟩,
  ⟨14, tris64, tgt64, cov64⟩,
  ⟨0, tris65, tgt65, cov65⟩,
  ⟨1, tris66, tgt66, cov66⟩,
  ⟨2, tris67, tgt67, cov67⟩,
  ⟨4, tris68, tgt68, cov68⟩,
  ⟨5, tris69, tgt69, cov69⟩
]

private def ownedTraceTerminal : Terminal :=
  ⟨9, tris70, cov70⟩

lemma hJ : J = maskAt 927 := by decide +kernel

theorem notIn : ¬ RealizesIn Ux J :=
  check_sound le_rfl (by norm_num [Ux]) ownedTraceTerminal ownedTraceProgram
    (batchesOwned_nil Ux J) (by decide +kernel)

theorem excluded : CaseExcluded (maskAt 927) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Split.U2P.C927
#print axioms SquarePacking.S11Opt.Split.U2P.C927.excluded
