import Sqpack.S11Opt.Bundled.F37.Leaves000
import Sqpack.S11Opt.Bundled.F37.Leaves001
import Sqpack.S11Opt.Bundled.F37.Leaves002

namespace SquarePacking.S11Opt.Bundled.F37
section
open SquarePacking.S11Opt.F37
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F37

namespace SquarePacking.S11Opt.Bundled.F37
section
open SquarePacking.S11Opt.F37
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F37

namespace SquarePacking.S11Opt.Bundled.F37
section
open SquarePacking.S11Opt.F37
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F37

namespace SquarePacking.S11Opt.Bundled.F37
section
open SquarePacking.S11Opt.F37
open FieldTree


end
end SquarePacking.S11Opt.Bundled.F37

namespace SquarePacking.S11Opt.Bundled.F37
section
open SquarePacking.S11Opt.F37
open FieldTree

theorem cov7g1 : CovF G.Q G.M G.R G.hps7 opts7 11448224634 12488972328 6244486164 7285233858 12582912 14680064 :=
  CovF.splitU 13631488 cov7p7_1 cov7p8_1

theorem cov7g2 : CovF G.Q G.M G.R G.hps7 opts7 11448224634 12488972328 6244486164 8325981552 12582912 14680064 :=
  CovF.splitY 7285233858 cov7g1 cov7p9_1

theorem cov7g3 : CovF G.Q G.M G.R G.hps7 opts7 10407476940 12488972328 6244486164 8325981552 12582912 14680064 :=
  CovF.splitX 11448224634 cov7p6_1 cov7g2

theorem cov7g4 : CovF G.Q G.M G.R G.hps7 opts7 10407476940 12488972328 6244486164 8325981552 12582912 16777216 :=
  CovF.splitU 14680064 cov7g3 cov7p10_1

theorem cov7g5 : CovF G.Q G.M G.R G.hps7 opts7 10407476940 12488972328 4162990776 8325981552 12582912 16777216 :=
  CovF.splitY 6244486164 cov7p5_1 cov7g4

theorem cov7g6 : CovF G.Q G.M G.R G.hps7 opts7 8325981552 12488972328 4162990776 8325981552 12582912 16777216 :=
  CovF.splitX 10407476940 cov7p4_1 cov7g5

theorem cov7g7 : CovF G.Q G.M G.R G.hps7 opts7 8325981552 12488972328 4162990776 8325981552 8388608 16777216 :=
  CovF.splitU 12582912 cov7p3_1 cov7g6

theorem cov7g8 : CovF G.Q G.M G.R G.hps7 opts7 8325981552 12488972328 0 8325981552 8388608 16777216 :=
  CovF.splitY 4162990776 cov7p2_1 cov7g7

theorem cov7g9 : CovF G.Q G.M G.R G.hps7 opts7 12488972328 13529720022 6244486164 7285233858 13631488 14680064 :=
  CovF.splitX 13009346175 cov7p15_1 cov7p16_1

theorem cov7g10 : CovF G.Q G.M G.R G.hps7 opts7 12488972328 13529720022 6244486164 7285233858 12582912 14680064 :=
  CovF.splitU 13631488 cov7p14_1 cov7g9

theorem cov7g11 : CovF G.Q G.M G.R G.hps7 opts7 12488972328 13529720022 6244486164 8325981552 12582912 14680064 :=
  CovF.splitY 7285233858 cov7g10 cov7p17_1

theorem cov7g12 : CovF G.Q G.M G.R G.hps7 opts7 13529720022 14570467716 6244486164 7285233858 13631488 14680064 :=
  CovF.splitX 14050093869 cov7p19_1 cov7p20_1

theorem cov7g13 : CovF G.Q G.M G.R G.hps7 opts7 13529720022 14570467716 6244486164 7285233858 12582912 14680064 :=
  CovF.splitU 13631488 cov7p18_1 cov7g12

theorem cov7g14 : CovF G.Q G.M G.R G.hps7 opts7 13529720022 14570467716 6244486164 8325981552 12582912 14680064 :=
  CovF.splitY 7285233858 cov7g13 cov7p21_1

theorem cov7g15 : CovF G.Q G.M G.R G.hps7 opts7 12488972328 14570467716 6244486164 8325981552 12582912 14680064 :=
  CovF.splitX 13529720022 cov7g11 cov7g14

theorem cov7g16 : CovF G.Q G.M G.R G.hps7 opts7 12488972328 14570467716 6244486164 8325981552 12582912 16777216 :=
  CovF.splitU 14680064 cov7g15 cov7p22_1

theorem cov7g17 : CovF G.Q G.M G.R G.hps7 opts7 12488972328 14570467716 4162990776 8325981552 12582912 16777216 :=
  CovF.splitY 6244486164 cov7p13_1 cov7g16

theorem cov7g18 : CovF G.Q G.M G.R G.hps7 opts7 12488972328 16651963104 4162990776 8325981552 12582912 16777216 :=
  CovF.splitX 14570467716 cov7g17 cov7p23_1

theorem cov7g19 : CovF G.Q G.M G.R G.hps7 opts7 12488972328 16651963104 4162990776 8325981552 8388608 16777216 :=
  CovF.splitU 12582912 cov7p12_1 cov7g18

theorem cov7g20 : CovF G.Q G.M G.R G.hps7 opts7 12488972328 16651963104 0 8325981552 8388608 16777216 :=
  CovF.splitY 4162990776 cov7p11_1 cov7g19

theorem cov7g21 : CovF G.Q G.M G.R G.hps7 opts7 8325981552 16651963104 0 8325981552 8388608 16777216 :=
  CovF.splitX 12488972328 cov7g8 cov7g20

theorem cov7g22 : CovF G.Q G.M G.R G.hps7 opts7 8325981552 16651963104 0 8325981552 0 16777216 :=
  CovF.splitU 8388608 cov7p1_1 cov7g21

theorem cov7g23 : CovF G.Q G.M G.R G.hps7 opts7 8325981552 16651963104 0 16651963104 0 16777216 :=
  CovF.splitY 8325981552 cov7g22 cov7p24_1

theorem cov7g24 : CovF G.Q G.M G.R G.hps7 opts7 0 16651963104 0 16651963104 0 16777216 :=
  CovF.splitX 8325981552 cov7p0_1 cov7g23

end
end SquarePacking.S11Opt.Bundled.F37

#print axioms SquarePacking.S11Opt.Bundled.F37.cov7g24
