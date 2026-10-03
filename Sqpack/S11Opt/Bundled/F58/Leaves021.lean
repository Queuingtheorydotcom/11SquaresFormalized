import Sqpack.S11Opt.Simplified.ComplementaryTree
import Sqpack.S11Opt.F58.Data

namespace SquarePacking.S11Opt.Bundled.F58
section
open SquarePacking.S11Opt.F58
open FieldTree
open SquarePacking.S11Opt.Simplified

theorem cov5p195_1 : CovF G.Q G.M G.R G.hps5 opts5 6374579625 6407102990 4780934718 4813458084 2949120 3014656 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 3218816844321293833220031395045346921014979802227222625160904339794535447704045084486134916151850120028189936296229817607719863650062704367858803144998821897 G.Q_pos G.R_pos G.hps5 opts5 (by decide +kernel)

theorem cov5p196_1 : CovF G.Q G.M G.R G.hps5 opts5 6407102990 6439626356 4748411353 4813458084 2949120 3014656 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 184565762 G.Q_pos G.R_pos G.hps5 opts5 (by decide +kernel)

theorem cov5p197_1 : CovF G.Q G.M G.R G.hps5 opts5 6439626356 6504673087 4683364623 4813458084 2883584 3014656 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 184565762 G.Q_pos G.R_pos G.hps5 opts5 (by decide +kernel)

theorem cov5p198_1 : CovF G.Q G.M G.R G.hps5 opts5 6374579625 6439626356 4683364623 4748411353 3014656 3145728 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 3218816844321293833220031395045346921014979802227222625160904339794535447704045084486134916151850120028189936296229817607719863650062704367858803144998821897 G.Q_pos G.R_pos G.hps5 opts5 (by decide +kernel)

end
end SquarePacking.S11Opt.Bundled.F58

#print axioms SquarePacking.S11Opt.Bundled.F58.cov5p195_1
#print axioms SquarePacking.S11Opt.Bundled.F58.cov5p196_1
#print axioms SquarePacking.S11Opt.Bundled.F58.cov5p197_1
#print axioms SquarePacking.S11Opt.Bundled.F58.cov5p198_1
