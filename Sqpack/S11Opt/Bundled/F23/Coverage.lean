import Sqpack.S11Opt.Bundled.F23.Leaves000
import Sqpack.S11Opt.Bundled.F23.Leaves001

namespace SquarePacking.S11Opt.Bundled.F23
section
open SquarePacking.S11Opt.F23
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F23

namespace SquarePacking.S11Opt.Bundled.F23
section
open SquarePacking.S11Opt.F23
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F23

namespace SquarePacking.S11Opt.Bundled.F23
section
open SquarePacking.S11Opt.F23
open FieldTree

theorem cov5g1 : CovF G.Q G.M G.R G.hps5 opts5 0 8325981552 0 8325981552 0 16777216 :=
  CovF.splitU 8388608 cov5p0_1 cov5p1_1

theorem cov5g2 : CovF G.Q G.M G.R G.hps5 opts5 0 8325981552 0 16651963104 0 16777216 :=
  CovF.splitY 8325981552 cov5g1 cov5p2_1

theorem cov5g3 : CovF G.Q G.M G.R G.hps5 opts5 0 16651963104 0 16651963104 0 16777216 :=
  CovF.splitX 8325981552 cov5g2 cov5p3_1

end
end SquarePacking.S11Opt.Bundled.F23

namespace SquarePacking.S11Opt.Bundled.F23
section
open SquarePacking.S11Opt.F23
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F23

#print axioms SquarePacking.S11Opt.Bundled.F23.cov5g3
