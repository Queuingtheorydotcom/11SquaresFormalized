import Sqpack.S11Opt.Simplified.ComplementaryTree
import Sqpack.S11Opt.F50.Data

namespace SquarePacking.S11Opt.Bundled.F50
section
open SquarePacking.S11Opt.F50
open FieldTree
open SquarePacking.S11Opt.Simplified

theorem cov5p66_1 : CovF G.Q G.M G.R G.hps5 opts5 6504673087 6764860011 4162990776 4423177699 2621440 2883584 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 2127818087348165291242966592979379556059269186878711916149698710647563713328260555630847535814834528320967853634734405764055703010636094961931440044292813933811026826829473398237885824076775525781428812677216981294550517744384760766412731339827056796764473162356591096774629818377 G.Q_pos G.R_pos G.hps5 opts5 (by decide +kernel)

theorem cov5p67_1 : CovF G.Q G.M G.R G.hps5 opts5 6504673087 6634766549 4162990776 4293084237 2883584 3145728 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 4097 G.Q_pos G.R_pos G.hps5 opts5 (by decide +kernel)

theorem cov5p68_1 : CovF G.Q G.M G.R G.hps5 opts5 6504673087 6569719818 4293084237 4358130968 2883584 3014656 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 4097 G.Q_pos G.R_pos G.hps5 opts5 (by decide +kernel)

end
end SquarePacking.S11Opt.Bundled.F50

#print axioms SquarePacking.S11Opt.Bundled.F50.cov5p66_1
#print axioms SquarePacking.S11Opt.Bundled.F50.cov5p67_1
#print axioms SquarePacking.S11Opt.Bundled.F50.cov5p68_1
