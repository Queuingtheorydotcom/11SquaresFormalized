import Sqpack.S11Opt.Bundled.F41.Leaves000
import Sqpack.S11Opt.Bundled.F41.Leaves001

namespace SquarePacking.S11Opt.Bundled.F41
section
open SquarePacking.S11Opt.F41
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F41

namespace SquarePacking.S11Opt.Bundled.F41
section
open SquarePacking.S11Opt.F41
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F41

namespace SquarePacking.S11Opt.Bundled.F41
section
open SquarePacking.S11Opt.F41
open FieldTree

theorem cov11g1 : CovF G.Q G.M G.R G.hps11 opts11 12488972328 14570467716 8325981552 10407476940 0 2097152 :=
  CovF.splitX 13529720022 cov11p3_1 cov11p4_1

theorem cov11g2 : CovF G.Q G.M G.R G.hps11 opts11 12488972328 14570467716 8325981552 10407476940 0 4194304 :=
  CovF.splitU 2097152 cov11g1 cov11p5_1

theorem cov11g3 : CovF G.Q G.M G.R G.hps11 opts11 12488972328 14570467716 8325981552 12488972328 0 4194304 :=
  CovF.splitY 10407476940 cov11g2 cov11p6_1

theorem cov11g4 : CovF G.Q G.M G.R G.hps11 opts11 12488972328 16651963104 8325981552 12488972328 0 4194304 :=
  CovF.splitX 14570467716 cov11g3 cov11p7_1

theorem cov11g5 : CovF G.Q G.M G.R G.hps11 opts11 12488972328 16651963104 8325981552 12488972328 0 8388608 :=
  CovF.splitU 4194304 cov11g4 cov11p8_1

theorem cov11g6 : CovF G.Q G.M G.R G.hps11 opts11 12488972328 16651963104 8325981552 16651963104 0 8388608 :=
  CovF.splitY 12488972328 cov11g5 cov11p9_1

theorem cov11g7 : CovF G.Q G.M G.R G.hps11 opts11 8325981552 16651963104 8325981552 16651963104 0 8388608 :=
  CovF.splitX 12488972328 cov11p2_1 cov11g6

theorem cov11g8 : CovF G.Q G.M G.R G.hps11 opts11 8325981552 16651963104 8325981552 16651963104 0 16777216 :=
  CovF.splitU 8388608 cov11g7 cov11p10_1

theorem cov11g9 : CovF G.Q G.M G.R G.hps11 opts11 8325981552 16651963104 0 16651963104 0 16777216 :=
  CovF.splitY 8325981552 cov11p1_1 cov11g8

theorem cov11g10 : CovF G.Q G.M G.R G.hps11 opts11 0 16651963104 0 16651963104 0 16777216 :=
  CovF.splitX 8325981552 cov11p0_1 cov11g9

end
end SquarePacking.S11Opt.Bundled.F41

namespace SquarePacking.S11Opt.Bundled.F41
section
open SquarePacking.S11Opt.F41
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F41

namespace SquarePacking.S11Opt.Bundled.F41
section
open SquarePacking.S11Opt.F41
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F41

namespace SquarePacking.S11Opt.Bundled.F41
section
open SquarePacking.S11Opt.F41
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F41

namespace SquarePacking.S11Opt.Bundled.F41
section
open SquarePacking.S11Opt.F41
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F41

#print axioms SquarePacking.S11Opt.Bundled.F41.cov11g10
