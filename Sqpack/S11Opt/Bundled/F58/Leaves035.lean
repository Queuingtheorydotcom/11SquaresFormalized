import Sqpack.S11Opt.Simplified.ComplementaryTree
import Sqpack.S11Opt.F58.Data

namespace SquarePacking.S11Opt.Bundled.F58
section
open SquarePacking.S11Opt.F58
open FieldTree
open SquarePacking.S11Opt.Simplified

theorem cov5p44_1 : CovF G.Q G.M G.R G.hps5 opts5 6179439433 6244486164 5203738470 5268785200 3014656 3145728 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 3218816844321293833220031395045346921014979802227222625160904339794535447704045084486134916151850120028189936296229817607719863650062704367858803144998821897 G.Q_pos G.R_pos G.hps5 opts5 (by decide +kernel)

theorem cov5p45_1 : CovF G.Q G.M G.R G.hps5 opts5 6179439433 6244486164 5268785200 5333831931 3014656 3145728 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 3218816844321293833220031395045346921014979802227222625160904339794535447704045084486134916151850120028189936296229817607719863650062704367858803144998821897 G.Q_pos G.R_pos G.hps5 opts5 (by decide +kernel)

theorem cov5p46_1 : CovF G.Q G.M G.R G.hps5 opts5 6114392702 6146916067 5333831931 5398878662 2883584 2949120 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 16818178 G.Q_pos G.R_pos G.hps5 opts5 (by decide +kernel)

end
end SquarePacking.S11Opt.Bundled.F58

#print axioms SquarePacking.S11Opt.Bundled.F58.cov5p44_1
#print axioms SquarePacking.S11Opt.Bundled.F58.cov5p45_1
#print axioms SquarePacking.S11Opt.Bundled.F58.cov5p46_1
