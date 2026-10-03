import Sqpack.S11Opt.Bundled.F35.Leaves000

namespace SquarePacking.S11Opt.Bundled.F35
section
open SquarePacking.S11Opt.F35
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F35

namespace SquarePacking.S11Opt.Bundled.F35
section
open SquarePacking.S11Opt.F35
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F35

namespace SquarePacking.S11Opt.Bundled.F35
section
open SquarePacking.S11Opt.F35
open FieldTree

theorem cov5g1 : CovF G.Q G.M G.R G.hps5 opts5 4162990776 6244486164 4162990776 8325981552 8388608 12582912 :=
  CovF.splitY 6244486164 cov5p3_1 cov5p4_1

theorem cov5g2 : CovF G.Q G.M G.R G.hps5 opts5 4162990776 8325981552 4162990776 8325981552 8388608 12582912 :=
  CovF.splitX 6244486164 cov5g1 cov5p5_1

theorem cov5g3 : CovF G.Q G.M G.R G.hps5 opts5 4162990776 8325981552 4162990776 8325981552 8388608 16777216 :=
  CovF.splitU 12582912 cov5g2 cov5p6_1

theorem cov5g4 : CovF G.Q G.M G.R G.hps5 opts5 4162990776 8325981552 0 8325981552 8388608 16777216 :=
  CovF.splitY 4162990776 cov5p2_1 cov5g3

theorem cov5g5 : CovF G.Q G.M G.R G.hps5 opts5 0 8325981552 0 8325981552 8388608 16777216 :=
  CovF.splitX 4162990776 cov5p1_1 cov5g4

theorem cov5g6 : CovF G.Q G.M G.R G.hps5 opts5 0 8325981552 0 8325981552 0 16777216 :=
  CovF.splitU 8388608 cov5p0_1 cov5g5

theorem cov5g7 : CovF G.Q G.M G.R G.hps5 opts5 0 8325981552 0 16651963104 0 16777216 :=
  CovF.splitY 8325981552 cov5g6 cov5p7_1

theorem cov5g8 : CovF G.Q G.M G.R G.hps5 opts5 0 16651963104 0 16651963104 0 16777216 :=
  CovF.splitX 8325981552 cov5g7 cov5p8_1

end
end SquarePacking.S11Opt.Bundled.F35

namespace SquarePacking.S11Opt.Bundled.F35
section
open SquarePacking.S11Opt.F35
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F35

namespace SquarePacking.S11Opt.Bundled.F35
section
open SquarePacking.S11Opt.F35
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F35

#print axioms SquarePacking.S11Opt.Bundled.F35.cov5g8
