import Sqpack.S11Opt.Simplified.ComplementaryTree
import Sqpack.S11Opt.F40.Data

namespace SquarePacking.S11Opt.Bundled.F40
section
open SquarePacking.S11Opt.F40
open FieldTree
open SquarePacking.S11Opt.Simplified

theorem cov0p36_1 : CovF G.Q G.M G.R G.hps0 opts0 2341682311 2406729042 2081495388 2211588849 16646144 16777216 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1370559285551500599306254775375503397835457433608 G.Q_pos G.R_pos G.hps0 opts0 (by decide +kernel)

theorem cov0p37_1 : CovF G.Q G.M G.R G.hps0 opts0 2406729042 2471775773 2081495388 2211588849 16646144 16777216 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1370559285551500599306254775375503397835457433608 G.Q_pos G.R_pos G.hps0 opts0 (by decide +kernel)

theorem cov0p38_1 : CovF G.Q G.M G.R G.hps0 opts0 2341682311 2471775773 2211588849 2341682311 16515072 16777216 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1688849910599682 G.Q_pos G.R_pos G.hps0 opts0 (by decide +kernel)

theorem cov0p39_1 : CovF G.Q G.M G.R G.hps0 opts0 2471775773 2601869235 2081495388 2341682311 16515072 16777216 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1370559285551500599306254775375503397835457433608 G.Q_pos G.R_pos G.hps0 opts0 (by decide +kernel)

theorem cov0p4_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 4162990776 2081495388 4162990776 12582912 14680064 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694884226328857176002444040084228021424136 G.Q_pos G.R_pos G.hps0 opts0 (by decide +kernel)

theorem cov0p40_1 : CovF G.Q G.M G.R G.hps0 opts0 2341682311 2601869235 2341682311 2601869235 16252928 16777216 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1407374933889026 G.Q_pos G.R_pos G.hps0 opts0 (by decide +kernel)

theorem cov0p41_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 2601869235 2601869235 3122243082 15728640 16777216 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 844424980467714 G.Q_pos G.R_pos G.hps0 opts0 (by decide +kernel)

theorem cov0p42_1 : CovF G.Q G.M G.R G.hps0 opts0 2601869235 3122243082 2081495388 2601869235 15728640 16252928 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1370559285551500599306254775375503397835457433608 G.Q_pos G.R_pos G.hps0 opts0 (by decide +kernel)

theorem cov0p43_1 : CovF G.Q G.M G.R G.hps0 opts0 2601869235 2862056158 2081495388 2341682311 16252928 16515072 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1370559285551500599306254775375503397835457433608 G.Q_pos G.R_pos G.hps0 opts0 (by decide +kernel)

theorem cov0p44_1 : CovF G.Q G.M G.R G.hps0 opts0 2601869235 2731962696 2081495388 2341682311 16515072 16777216 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1370559285551500599306254775375503397835457433608 G.Q_pos G.R_pos G.hps0 opts0 (by decide +kernel)

theorem cov0p45_1 : CovF G.Q G.M G.R G.hps0 opts0 2731962696 2862056158 2081495388 2341682311 16515072 16777216 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1370559285551500599306254775375503397835457433608 G.Q_pos G.R_pos G.hps0 opts0 (by decide +kernel)

theorem cov0p46_1 : CovF G.Q G.M G.R G.hps0 opts0 2601869235 2862056158 2341682311 2601869235 16252928 16777216 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1407374933889026 G.Q_pos G.R_pos G.hps0 opts0 (by decide +kernel)

end
end SquarePacking.S11Opt.Bundled.F40

#print axioms SquarePacking.S11Opt.Bundled.F40.cov0p36_1
#print axioms SquarePacking.S11Opt.Bundled.F40.cov0p37_1
#print axioms SquarePacking.S11Opt.Bundled.F40.cov0p38_1
#print axioms SquarePacking.S11Opt.Bundled.F40.cov0p39_1
#print axioms SquarePacking.S11Opt.Bundled.F40.cov0p4_1
#print axioms SquarePacking.S11Opt.Bundled.F40.cov0p40_1
#print axioms SquarePacking.S11Opt.Bundled.F40.cov0p41_1
#print axioms SquarePacking.S11Opt.Bundled.F40.cov0p42_1
#print axioms SquarePacking.S11Opt.Bundled.F40.cov0p43_1
#print axioms SquarePacking.S11Opt.Bundled.F40.cov0p44_1
#print axioms SquarePacking.S11Opt.Bundled.F40.cov0p45_1
#print axioms SquarePacking.S11Opt.Bundled.F40.cov0p46_1
