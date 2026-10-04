import Sqpack.S11Opt.Simplified.ComplementaryTree
import Sqpack.S11Opt.F25.Data

namespace SquarePacking.S11Opt.Bundled.F25
section
open SquarePacking.S11Opt.F25
open FieldTree
open SquarePacking.S11Opt.Simplified

theorem cov10p106_1 : CovF G.Q G.M G.R G.hps10 opts10 10082243285 10147290016 12228785404 12293832135 3080192 3145728 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1600662175771308139373959567440463053158609541354793020771006809991029716012668565663367334930570258032754157867971867620630430888224410720309753778322700137447980873063177752798660681415371682225302431069777678213017984679708218098311063670793 G.Q_pos G.R_pos G.hps10 opts10 (by native_decide)

theorem cov10p107_1 : CovF G.Q G.M G.R G.hps10 opts10 10082243285 10147290016 12293832135 12358878866 3014656 3145728 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 53249 G.Q_pos G.R_pos G.hps10 opts10 (by native_decide)

theorem cov10p108_1 : CovF G.Q G.M G.R G.hps10 opts10 9887103093 10147290016 12358878866 12488972328 2883584 3145728 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 53249 G.Q_pos G.R_pos G.hps10 opts10 (by native_decide)

end
end SquarePacking.S11Opt.Bundled.F25

#print axioms SquarePacking.S11Opt.Bundled.F25.cov10p106_1
#print axioms SquarePacking.S11Opt.Bundled.F25.cov10p107_1
#print axioms SquarePacking.S11Opt.Bundled.F25.cov10p108_1
