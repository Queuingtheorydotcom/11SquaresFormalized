import Sqpack.S11Opt.Bundled.F36.Leaves000
import Sqpack.S11Opt.Bundled.F36.Leaves001
import Sqpack.S11Opt.Bundled.F36.Leaves002
import Sqpack.S11Opt.Bundled.F36.Leaves003

namespace SquarePacking.S11Opt.Bundled.F36
section
open SquarePacking.S11Opt.F36
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F36

namespace SquarePacking.S11Opt.Bundled.F36
section
open SquarePacking.S11Opt.F36
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F36

namespace SquarePacking.S11Opt.Bundled.F36
section
open SquarePacking.S11Opt.F36
open FieldTree

theorem cov11g1 : CovF G.Q G.M G.R G.hps11 opts11 8325981552 16651963104 8325981552 16651963104 8388608 16777216 :=
  CovF.splitX 12488972328 cov11p3_1 cov11p4_1

theorem cov11g2 : CovF G.Q G.M G.R G.hps11 opts11 8325981552 16651963104 8325981552 16651963104 0 16777216 :=
  CovF.splitU 8388608 cov11p2_1 cov11g1

theorem cov11g3 : CovF G.Q G.M G.R G.hps11 opts11 8325981552 16651963104 0 16651963104 0 16777216 :=
  CovF.splitY 8325981552 cov11p1_1 cov11g2

theorem cov11g4 : CovF G.Q G.M G.R G.hps11 opts11 0 16651963104 0 16651963104 0 16777216 :=
  CovF.splitX 8325981552 cov11p0_1 cov11g3

end
end SquarePacking.S11Opt.Bundled.F36

namespace SquarePacking.S11Opt.Bundled.F36
section
open SquarePacking.S11Opt.F36
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F36

namespace SquarePacking.S11Opt.Bundled.F36
section
open SquarePacking.S11Opt.F36
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F36

namespace SquarePacking.S11Opt.Bundled.F36
section
open SquarePacking.S11Opt.F36
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F36

#print axioms SquarePacking.S11Opt.Bundled.F36.cov11g4
