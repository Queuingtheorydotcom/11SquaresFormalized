import Sqpack.S11Opt.Bundled.F18.Leaves000
import Sqpack.S11Opt.Bundled.F18.Leaves001

namespace SquarePacking.S11Opt.Bundled.F18
section
open SquarePacking.S11Opt.F18
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F18

namespace SquarePacking.S11Opt.Bundled.F18
section
open SquarePacking.S11Opt.F18
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F18

namespace SquarePacking.S11Opt.Bundled.F18
section
open SquarePacking.S11Opt.F18
open FieldTree

theorem cov5g1 : CovF G.Q G.M G.R G.hps5 opts5 6244486164 6764860011 6244486164 7285233858 13631488 14680064 :=
  CovF.splitY 6764860011 cov5p7_1 cov5p8_1

theorem cov5g2 : CovF G.Q G.M G.R G.hps5 opts5 6244486164 7285233858 6244486164 7285233858 13631488 14680064 :=
  CovF.splitX 6764860011 cov5g1 cov5p9_1

theorem cov5g3 : CovF G.Q G.M G.R G.hps5 opts5 6244486164 7285233858 6244486164 7285233858 12582912 14680064 :=
  CovF.splitU 13631488 cov5p6_1 cov5g2

theorem cov5g4 : CovF G.Q G.M G.R G.hps5 opts5 6244486164 7285233858 6244486164 8325981552 12582912 14680064 :=
  CovF.splitY 7285233858 cov5g3 cov5p10_1

theorem cov5g5 : CovF G.Q G.M G.R G.hps5 opts5 6244486164 8325981552 6244486164 8325981552 12582912 14680064 :=
  CovF.splitX 7285233858 cov5g4 cov5p11_1

theorem cov5g6 : CovF G.Q G.M G.R G.hps5 opts5 6244486164 7285233858 6244486164 7285233858 14680064 16777216 :=
  CovF.splitU 15728640 cov5p12_1 cov5p13_1

theorem cov5g7 : CovF G.Q G.M G.R G.hps5 opts5 6244486164 7285233858 6244486164 8325981552 14680064 16777216 :=
  CovF.splitY 7285233858 cov5g6 cov5p14_1

theorem cov5g8 : CovF G.Q G.M G.R G.hps5 opts5 6244486164 8325981552 6244486164 8325981552 14680064 16777216 :=
  CovF.splitX 7285233858 cov5g7 cov5p15_1

theorem cov5g9 : CovF G.Q G.M G.R G.hps5 opts5 6244486164 8325981552 6244486164 8325981552 12582912 16777216 :=
  CovF.splitU 14680064 cov5g5 cov5g8

theorem cov5g10 : CovF G.Q G.M G.R G.hps5 opts5 6244486164 8325981552 4162990776 8325981552 12582912 16777216 :=
  CovF.splitY 6244486164 cov5p5_1 cov5g9

theorem cov5g11 : CovF G.Q G.M G.R G.hps5 opts5 4162990776 8325981552 4162990776 8325981552 12582912 16777216 :=
  CovF.splitX 6244486164 cov5p4_1 cov5g10

theorem cov5g12 : CovF G.Q G.M G.R G.hps5 opts5 4162990776 8325981552 4162990776 8325981552 8388608 16777216 :=
  CovF.splitU 12582912 cov5p3_1 cov5g11

theorem cov5g13 : CovF G.Q G.M G.R G.hps5 opts5 4162990776 8325981552 0 8325981552 8388608 16777216 :=
  CovF.splitY 4162990776 cov5p2_1 cov5g12

theorem cov5g14 : CovF G.Q G.M G.R G.hps5 opts5 0 8325981552 0 8325981552 8388608 16777216 :=
  CovF.splitX 4162990776 cov5p1_1 cov5g13

theorem cov5g15 : CovF G.Q G.M G.R G.hps5 opts5 0 8325981552 0 8325981552 0 16777216 :=
  CovF.splitU 8388608 cov5p0_1 cov5g14

theorem cov5g16 : CovF G.Q G.M G.R G.hps5 opts5 0 8325981552 0 16651963104 0 16777216 :=
  CovF.splitY 8325981552 cov5g15 cov5p16_1

theorem cov5g17 : CovF G.Q G.M G.R G.hps5 opts5 0 16651963104 0 16651963104 0 16777216 :=
  CovF.splitX 8325981552 cov5g16 cov5p17_1

end
end SquarePacking.S11Opt.Bundled.F18

namespace SquarePacking.S11Opt.Bundled.F18
section
open SquarePacking.S11Opt.F18
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F18

#print axioms SquarePacking.S11Opt.Bundled.F18.cov5g17
