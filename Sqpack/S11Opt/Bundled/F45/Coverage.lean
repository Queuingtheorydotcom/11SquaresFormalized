import Sqpack.S11Opt.Bundled.F45.Leaves000
import Sqpack.S11Opt.Bundled.F45.Leaves001

namespace SquarePacking.S11Opt.Bundled.F45
section
open SquarePacking.S11Opt.F45
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F45

namespace SquarePacking.S11Opt.Bundled.F45
section
open SquarePacking.S11Opt.F45
open FieldTree

theorem cov6g1 : CovF G.Q G.M G.R G.hps6 opts6 8325981552 16651963104 0 8325981552 0 16777216 :=
  CovF.splitU 8388608 cov6p1_1 cov6p2_1

theorem cov6g2 : CovF G.Q G.M G.R G.hps6 opts6 8325981552 16651963104 0 16651963104 0 16777216 :=
  CovF.splitY 8325981552 cov6g1 cov6p3_1

theorem cov6g3 : CovF G.Q G.M G.R G.hps6 opts6 0 16651963104 0 16651963104 0 16777216 :=
  CovF.splitX 8325981552 cov6p0_1 cov6g2

end
end SquarePacking.S11Opt.Bundled.F45

namespace SquarePacking.S11Opt.Bundled.F45
section
open SquarePacking.S11Opt.F45
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F45

namespace SquarePacking.S11Opt.Bundled.F45
section
open SquarePacking.S11Opt.F45
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F45

#print axioms SquarePacking.S11Opt.Bundled.F45.cov6g3
