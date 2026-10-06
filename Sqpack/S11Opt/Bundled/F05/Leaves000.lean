import Sqpack.S11Opt.Simplified.ComplementaryTree
import Sqpack.S11Opt.F05.Data

namespace SquarePacking.S11Opt.Bundled.F05
section
open SquarePacking.S11Opt.F05
open FieldTree
open SquarePacking.S11Opt.Simplified

theorem cov0p0_1 : CovF G.Q G.M G.R G.hps0 opts0 0 2081495388 0 4162990776 0 4194304 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1031060586503 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p1_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 4162990776 0 2081495388 0 4194304 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1168533094407 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p10_1 : CovF G.Q G.M G.R G.hps0 opts0 2146542118 2211588849 2146542118 2211588849 65536 131072 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694884226328857176002444038395378161156104 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p11_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 2211588849 2081495388 2211588849 131072 262144 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694884226328857176002444038395378161156104 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p12_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 2211588849 2211588849 2276635580 0 131072 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694878909416873958967699967830869858582536 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p13_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 2211588849 2276635580 2341682311 0 131072 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694878909416873958967699967830869858582536 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p14_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 2211588849 2211588849 2341682311 131072 262144 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694878909416873958967699967830869858582536 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p15_1 : CovF G.Q G.M G.R G.hps0 opts0 2211588849 2341682311 2081495388 2341682311 0 262144 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1370559285551500599306254775375501708985597165576 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p16_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 2341682311 2081495388 2341682311 262144 524288 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694884226328857176002444038395378161156104 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p17_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 2341682311 2341682311 2471775773 0 262144 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694878909416873958967699967830869858582536 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p18_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 2341682311 2471775773 2601869235 0 262144 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694878909416873958967699967830869858582536 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p19_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 2341682311 2341682311 2601869235 262144 524288 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694878909416873958967699967830869858582536 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p2_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 2146542118 2081495388 2211588849 0 131072 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 0 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p20_1 : CovF G.Q G.M G.R G.hps0 opts0 2341682311 2601869235 2081495388 2601869235 0 524288 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 50331650 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p21_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 2601869235 2081495388 2601869235 524288 1048576 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694884226328857176002444038395378161156104 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p22_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 2601869235 2601869235 3122243082 0 1048576 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694878909416873958967699967830869858582536 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p23_1 : CovF G.Q G.M G.R G.hps0 opts0 2601869235 3122243082 2081495388 3122243082 0 1048576 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 68769808386 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p24_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 3122243082 2081495388 3122243082 1048576 2097152 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694884226328857176002444038395378161156104 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p25_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 3122243082 3122243082 4162990776 0 2097152 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694878909416873958967699967830869858582536 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p26_1 : CovF G.Q G.M G.R G.hps0 opts0 3122243082 4162990776 2081495388 4162990776 0 2097152 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 206208761858 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p27_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 4162990776 2081495388 4162990776 2097152 4194304 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694884226328857176002444038395378161156104 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p28_1 : CovF G.Q G.M G.R G.hps0 opts0 0 4162990776 0 4162990776 4194304 8388608 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 8603140069752278957741369841987405226131905475687827545274230898266435390970996279591455602913837961969670 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p29_1 : CovF G.Q G.M G.R G.hps0 opts0 0 4162990776 4162990776 8325981552 0 8388608 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 929618905413683524468061263315710593862011857165885080622590587800306348326639667632089881898761018514121870250526668141617149316323513665436730843573635194752800147463005528446094524835450471855889607970392203284712681409718650754684657750778282677957320041164657920915156195785816068016549777419992870689437558229931339865636989381928482027815468179008682779190306684191991920006544559051188281397781954693536537527962958363806076989104430353446328537922271543670026960109945599264147261739642106870444543099293416825040901 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p3_1 : CovF G.Q G.M G.R G.hps0 opts0 2146542118 2211588849 2081495388 2146542118 0 131072 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 0 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p30_1 : CovF G.Q G.M G.R G.hps0 opts0 4162990776 8325981552 0 8325981552 0 8388608 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 8601039762243777544080150681361994987882352984802460795986673572359320101829057346124012474339546076545030 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p31_1 : CovF G.Q G.M G.R G.hps0 opts0 0 4162990776 0 4162990776 8388608 12582912 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694884226328857176002444038395378161156104 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p32_1 : CovF G.Q G.M G.R G.hps0 opts0 0 2081495388 0 4162990776 12582912 16777216 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1031060586503 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p33_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 4162990776 0 2081495388 12582912 16777216 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1168533094407 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

theorem cov0p34_1 : CovF G.Q G.M G.R G.hps0 opts0 2081495388 4162990776 2081495388 4162990776 12582912 14680064 :=
  ComplementaryTree.soundDec G.Q G.M G.R 4096 200 1735934694884226328857176002444038395378161156104 G.Q_pos G.R_pos G.hps0 opts0 (by native_decide)

end
end SquarePacking.S11Opt.Bundled.F05

#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p0_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p1_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p10_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p11_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p12_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p13_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p14_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p15_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p16_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p17_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p18_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p19_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p2_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p20_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p21_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p22_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p23_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p24_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p25_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p26_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p27_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p28_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p29_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p3_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p30_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p31_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p32_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p33_1
#print axioms SquarePacking.S11Opt.Bundled.F05.cov0p34_1
