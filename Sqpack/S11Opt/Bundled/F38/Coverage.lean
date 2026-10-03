import Sqpack.S11Opt.Bundled.F38.Leaves000

namespace SquarePacking.S11Opt.Bundled.F38
section
open SquarePacking.S11Opt.F38
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F38

namespace SquarePacking.S11Opt.Bundled.F38
section
open SquarePacking.S11Opt.F38
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F38

namespace SquarePacking.S11Opt.Bundled.F38
section
open SquarePacking.S11Opt.F38
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F38

namespace SquarePacking.S11Opt.Bundled.F38
section
open SquarePacking.S11Opt.F38
open FieldTree

theorem cov9g1 : CovF G.Q G.M G.R G.hps9 opts9 0 8325981552 8325981552 16651963104 0 16777216 :=
  CovF.splitU 8388608 cov9p1_1 cov9p2_1

theorem cov9g2 : CovF G.Q G.M G.R G.hps9 opts9 0 8325981552 0 16651963104 0 16777216 :=
  CovF.splitY 8325981552 cov9p0_1 cov9g1

theorem cov9g3 : CovF G.Q G.M G.R G.hps9 opts9 0 16651963104 0 16651963104 0 16777216 :=
  CovF.splitX 8325981552 cov9g2 cov9p3_1

end
end SquarePacking.S11Opt.Bundled.F38

#print axioms SquarePacking.S11Opt.Bundled.F38.cov9g3
