import Sqpack.S11Opt.Simplified.ComplementaryTree
import Sqpack.S11Opt.F50.Data

namespace SquarePacking.S11Opt.Bundled.F50
section
open SquarePacking.S11Opt.F50
open FieldTree
open SquarePacking.S11Opt.Simplified

theorem cov5p29_1 : CovF G.Q G.M G.R G.hps5 opts5 6472149721 6504673087 4455701064 4488224430 2883584 2949120 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 2127818087381183699439426151953444293431686379780713521882008298775751690318125039065961834433880823291455648620669481759243703430119477975236181063118036996393482315878106209723518704459281794019722113627339543020167262735975293451419702848112182270232271096449866486393639829513 G.Q_pos G.R_pos G.hps5 opts5 (by native_decide)

theorem cov5p3_1 : CovF G.Q G.M G.R G.hps5 opts5 4162990776 5203738470 4162990776 6244486164 2097152 4194304 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 16809986 G.Q_pos G.R_pos G.hps5 opts5 (by native_decide)

theorem cov5p30_1 : CovF G.Q G.M G.R G.hps5 opts5 6439626356 6472149721 4423177699 4488224430 2949120 3014656 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 16809986 G.Q_pos G.R_pos G.hps5 opts5 (by native_decide)

end
end SquarePacking.S11Opt.Bundled.F50

#print axioms SquarePacking.S11Opt.Bundled.F50.cov5p29_1
#print axioms SquarePacking.S11Opt.Bundled.F50.cov5p3_1
#print axioms SquarePacking.S11Opt.Bundled.F50.cov5p30_1
