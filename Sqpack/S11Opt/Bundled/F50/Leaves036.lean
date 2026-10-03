import Sqpack.S11Opt.F50.Data

namespace SquarePacking.S11Opt.Bundled.F50
section
open SquarePacking.S11Opt.F50
open FieldTree

theorem cov5p146_1 : CovF G.Q G.M G.R G.hps5 opts5 6309532894 6374579625 5008598277 5073645008 2883584 3014656 :=
  soundDec G.Q G.M G.R 4096 200 157608024785578336903807727561144816860735672221921610420096722630511380816051087225941124774599159760304262902452226 G.Q_pos G.R_pos G.hps5 opts5 (by decide +kernel)

end
end SquarePacking.S11Opt.Bundled.F50

#print axioms SquarePacking.S11Opt.Bundled.F50.cov5p146_1
