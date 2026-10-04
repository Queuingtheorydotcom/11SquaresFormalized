import Sqpack.S11Opt.F50.Data

namespace SquarePacking.S11Opt.Bundled.F50
section
open SquarePacking.S11Opt.F50
open FieldTree

theorem cov5p13_1 : CovF G.Q G.M G.R G.hps5 opts5 6179439433 6244486164 5073645008 5138691739 2883584 3014656 :=
  soundDec G.Q G.M G.R 4096 200 16809986 G.Q_pos G.R_pos G.hps5 opts5 (by native_decide)

end
end SquarePacking.S11Opt.Bundled.F50

#print axioms SquarePacking.S11Opt.Bundled.F50.cov5p13_1
