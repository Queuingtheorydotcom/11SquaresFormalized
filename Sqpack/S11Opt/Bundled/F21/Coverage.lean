import Sqpack.S11Opt.Bundled.F21.Leaves000

namespace SquarePacking.S11Opt.Bundled.F21
section
open SquarePacking.S11Opt.F21
open FieldTree

theorem cov10g1 : CovF G.Q G.M G.R G.hps10 opts10 8325981552 10407476940 8325981552 12488972328 8388608 12582912 :=
  CovF.splitY 10407476940 cov10p3_1 cov10p4_1

theorem cov10g2 : CovF G.Q G.M G.R G.hps10 opts10 8325981552 12488972328 8325981552 12488972328 8388608 12582912 :=
  CovF.splitX 10407476940 cov10g1 cov10p5_1

theorem cov10g3 : CovF G.Q G.M G.R G.hps10 opts10 8325981552 12488972328 8325981552 12488972328 8388608 16777216 :=
  CovF.splitU 12582912 cov10g2 cov10p6_1

theorem cov10g4 : CovF G.Q G.M G.R G.hps10 opts10 8325981552 12488972328 8325981552 16651963104 8388608 16777216 :=
  CovF.splitY 12488972328 cov10g3 cov10p7_1

theorem cov10g5 : CovF G.Q G.M G.R G.hps10 opts10 8325981552 16651963104 8325981552 16651963104 8388608 16777216 :=
  CovF.splitX 12488972328 cov10g4 cov10p8_1

theorem cov10g6 : CovF G.Q G.M G.R G.hps10 opts10 8325981552 16651963104 8325981552 16651963104 0 16777216 :=
  CovF.splitU 8388608 cov10p2_1 cov10g5

theorem cov10g7 : CovF G.Q G.M G.R G.hps10 opts10 8325981552 16651963104 0 16651963104 0 16777216 :=
  CovF.splitY 8325981552 cov10p1_1 cov10g6

theorem cov10g8 : CovF G.Q G.M G.R G.hps10 opts10 0 16651963104 0 16651963104 0 16777216 :=
  CovF.splitX 8325981552 cov10p0_1 cov10g7

end
end SquarePacking.S11Opt.Bundled.F21

namespace SquarePacking.S11Opt.Bundled.F21
section
open SquarePacking.S11Opt.F21
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F21

namespace SquarePacking.S11Opt.Bundled.F21
section
open SquarePacking.S11Opt.F21
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F21

namespace SquarePacking.S11Opt.Bundled.F21
section
open SquarePacking.S11Opt.F21
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F21

#print axioms SquarePacking.S11Opt.Bundled.F21.cov10g8
