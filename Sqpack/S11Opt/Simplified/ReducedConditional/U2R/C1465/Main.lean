import Sqpack.S11Opt.Simplified.ConditionalOwnedTrace
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages000
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages010
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages019
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages036
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages046
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages047
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages048
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages049
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages050
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages001
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages003
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages004
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages005
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages006
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages007
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages008
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages009
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages011
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages012
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages013
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages014
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages015
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages016
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages017
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages018
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages020
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages021
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages023
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages025
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages026
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages029
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages031
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages032
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages034
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages038
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages041
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages043
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages045
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages051
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages002
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages022
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages024
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages027
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages028
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages030
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages033
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages035
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages037
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages039
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages040
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages042
import Sqpack.S11Opt.Simplified.ReducedConditional.U2R.C1465.SharedStages044

namespace SquarePacking.S11Opt.Simplified.ReducedConditional.U2R.C1465
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.ConditionalOwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- One record per promotion; branch conditions remain in the program type. -/
private def program_rLL : Program cs_rLL :=
  .promote ⟨15, tris136, tgt136, [21, 8, 4], cov136⟩ <|
  .promote ⟨10, tris137, tgt137, [22, 11, 9, 2, 0], cov137⟩ <|
  .promote ⟨11, tris138, tgt138, [12, 1, 0], cov138⟩ <|
  .promote ⟨5, tris139, tgt139, [20, 13, 6, 3, 1], cov139⟩ <|
  .promote ⟨6, tris140, tgt140, [9, 4, 2, 1, 0], cov140⟩ <|
  .promote ⟨8, tris141, tgt141, [26, 19, 1], cov141⟩ <|
  .promote ⟨10, tris142, tgt142, [27, 5, 3, 2, 1], cov142⟩ <|
  .promote ⟨11, tris143, tgt143, [6, 2, 0], cov143⟩ <|
  .promote ⟨15, tris144, tgt144, [29, 21, 1, 0], cov144⟩ <|
  .promote ⟨1, tris145, tgt145, [12, 5, 4], cov145⟩ <|
  .promote ⟨3, tris146, tgt146, [5], cov146⟩ <|
  .promote ⟨5, tris147, tgt147, [14, 6, 5, 4, 1], cov147⟩ <|
  .promote ⟨6, tris148, tgt148, [9, 5, 4, 2, 1, 0], cov148⟩ <|
  .promote ⟨8, tris149, tgt149, [34, 27, 1], cov149⟩ <|
  .promote ⟨10, tris150, tgt150, [35, 6, 5, 2, 1], cov150⟩ <|
  .promote ⟨11, tris151, tgt151, [6, 2, 0], cov151⟩ <|
  .promote ⟨13, tris152, tgt152, [30, 23, 2, 1], cov152⟩ <|
  .promote ⟨0, tris153, tgt153, [7], cov153⟩ <|
  .promote ⟨1, tris154, tgt154, [6, 5, 0], cov154⟩ <|
  .promote ⟨3, tris155, tgt155, [6], cov155⟩ <|
  .promote ⟨5, tris156, tgt156, [7, 6, 5, 2, 1], cov156⟩ <|
  .promote ⟨6, tris157, tgt157, [18, 6, 5, 2, 1, 0], cov157⟩ <|
  .promote ⟨11, tris158, tgt158, [13, 7, 0], cov158⟩ <|
  .promote ⟨12, tris159, tgt159, [9, 6], cov159⟩ <|
  .promote ⟨13, tris160, tgt160, [10, 9, 0], cov160⟩ <|
  .promote ⟨15, tris161, tgt161, [10, 8, 2], cov161⟩ <|
  .promote ⟨0, tris162, tgt162, [7], cov162⟩ <|
  .promote ⟨1, tris163, tgt163, [6, 5, 0], cov163⟩ <|
  .promote ⟨5, tris164, tgt164, [14, 13, 6, 1, 0], cov164⟩ <|
  .promote ⟨8, tris165, tgt165, [12, 5, 0], cov165⟩ <|
  .promote ⟨10, tris166, tgt166, [13, 8, 7, 4, 1], cov166⟩ <|
  .promote ⟨11, tris167, tgt167, [9, 5, 0], cov167⟩ <|
  .promote ⟨15, tris168, tgt168, [15, 7, 1, 0], cov168⟩ <|
  .promote ⟨0, tris169, tgt169, [5], cov169⟩ <|
  .promote ⟨1, tris170, tgt170, [12, 5, 0], cov170⟩ <|
  .promote ⟨5, tris171, tgt171, [13, 5, 4, 1, 0], cov171⟩ <|
  .promote ⟨6, tris172, tgt172, [16, 5, 4, 1, 0], cov172⟩ <|
  .promote ⟨10, tris173, tgt173, [20, 5, 4, 1, 0], cov173⟩ <|
  .promote ⟨11, tris174, tgt174, [5, 1, 0], cov174⟩ <|
  .promote ⟨13, tris175, tgt175, [15, 9, 1], cov175⟩ <|
  .promote ⟨15, tris176, tgt176, [2, 1, 0], cov176⟩ <|
  .promote ⟨0, tris177, tgt177, [6], cov177⟩ <|
  .promote ⟨1, tris178, tgt178, [6, 5, 0], cov178⟩ <|
  .promote ⟨5, tris179, tgt179, [13, 6, 5, 1, 0], cov179⟩ <|
  .promote ⟨8, tris180, tgt180, [20, 4, 0], cov180⟩ <|
  .promote ⟨10, tris181, tgt181, [8, 6, 5, 4, 1], cov181⟩ <|
  .promote ⟨11, tris182, tgt182, [9, 5, 0], cov182⟩ <|
  .promote ⟨13, tris183, tgt183, [23, 2, 1], cov183⟩ <|
  .promote ⟨15, tris184, tgt184, [8, 2, 1, 0], cov184⟩ <|
  .promote ⟨0, tris185, tgt185, [6], cov185⟩ <|
  .promote ⟨1, tris186, tgt186, [13, 6, 0], cov186⟩ <|
  .promote ⟨5, tris187, tgt187, [14, 6, 5, 1, 0], cov187⟩ <|
  .promote ⟨6, tris188, tgt188, [32, 6, 5, 1, 0], cov188⟩ <|
  .promote ⟨8, tris189, tgt189, [29, 13, 7, 1], cov189⟩ <|
  .promote ⟨10, tris190, tgt190, [14, 7, 5, 2, 1], cov190⟩ <|
  .promote ⟨11, tris191, tgt191, [6, 2, 0], cov191⟩ <|
  .promote ⟨12, tris192, tgt192, [16, 8, 2], cov192⟩ <|
  .promote ⟨13, tris193, tgt193, [3, 2, 0], cov193⟩ <|
  .promote ⟨15, tris194, tgt194, [3, 2, 0], cov194⟩ <|
  .promote ⟨0, tris195, tgt195, [8, 7], cov195⟩ <|
  .promote ⟨1, tris196, tgt196, [8, 7, 0], cov196⟩ <|
  .promote ⟨3, tris197, tgt197, [8, 0], cov197⟩ <|
  .promote ⟨5, tris198, tgt198, [9, 8, 7, 2, 1], cov198⟩ <|
  .promote ⟨6, tris199, tgt199, [8, 7, 2, 1, 0], cov199⟩ <|
  .promote ⟨10, tris200, tgt200, [8, 6, 5, 1, 0], cov200⟩ <|
  .stop ⟨11, tris201, [6, 1, 0], cov201⟩

private def program_rLRL : Program cs_rLRL :=
  .promote ⟨10, tris253, tgt253, [14, 5, 0], cov253⟩ <|
  .promote ⟨5, tris254, tgt254, [6, 5, 3, 2, 0], cov254⟩ <|
  .promote ⟨6, tris255, tgt255, [17, 10, 9, 3, 1, 0], cov255⟩ <|
  .promote ⟨0, tris256, tgt256, [11, 4, 1], cov256⟩ <|
  .stop ⟨1, tris257, [2, 1, 0], cov257⟩

private def program_rLRRLL : Program cs_rLRRLL :=
  .promote ⟨5, tris304, tgt304, [15, 9, 3, 1, 0], cov304⟩ <|
  .promote ⟨6, tris305, tgt305, [16, 8, 6, 1, 0], cov305⟩ <|
  .promote ⟨8, tris306, tgt306, [15, 4, 1], cov306⟩ <|
  .promote ⟨10, tris307, tgt307, [16, 15, 10, 2, 1], cov307⟩ <|
  .promote ⟨11, tris308, tgt308, [95, 16, 2, 0], cov308⟩ <|
  .promote ⟨12, tris309, tgt309, [2], cov309⟩ <|
  .promote ⟨13, tris310, tgt310, [3, 2, 0], cov310⟩ <|
  .promote ⟨15, tris311, tgt311, [2], cov311⟩ <|
  .promote ⟨0, tris312, tgt312, [8], cov312⟩ <|
  .promote ⟨1, tris313, tgt313, [8, 7, 0], cov313⟩ <|
  .promote ⟨3, tris314, tgt314, [8], cov314⟩ <|
  .promote ⟨5, tris315, tgt315, [9, 8, 7, 2, 1], cov315⟩ <|
  .promote ⟨6, tris316, tgt316, [8, 7, 2, 1, 0], cov316⟩ <|
  .promote ⟨8, tris317, tgt317, [7, 6, 1], cov317⟩ <|
  .promote ⟨10, tris318, tgt318, [9, 7, 6, 2, 1], cov318⟩ <|
  .promote ⟨13, tris320, tgt320, [9, 1, 0], cov320⟩ <|
  .promote ⟨0, tris321, tgt321, [6], cov321⟩ <|
  .promote ⟨1, tris322, tgt322, [5, 4, 0], cov322⟩ <|
  .promote ⟨3, tris323, tgt323, [5], cov323⟩ <|
  .promote ⟨5, tris324, tgt324, [6, 5, 4, 2, 1], cov324⟩ <|
  .promote ⟨6, tris325, tgt325, [15, 5, 2, 1, 0], cov325⟩ <|
  .promote ⟨8, tris326, tgt326, [15, 5, 1], cov326⟩ <|
  .promote ⟨10, tris327, tgt327, [17, 14, 6, 2, 1], cov327⟩ <|
  .promote ⟨11, tris328, tgt328, [15, 2, 0], cov328⟩ <|
  .promote ⟨15, tris329, tgt329, [0], cov329⟩ <|
  .promote ⟨0, tris330, tgt330, [7], cov330⟩ <|
  .promote ⟨1, tris331, tgt331, [6, 5, 0], cov331⟩ <|
  .promote ⟨3, tris332, tgt332, [6], cov332⟩ <|
  .promote ⟨5, tris333, tgt333, [7, 6, 5, 2, 1], cov333⟩ <|
  .promote ⟨6, tris334, tgt334, [6, 5, 2, 1, 0], cov334⟩ <|
  .stop ⟨10, tris335, [14, 6, 5, 1, 0], cov335⟩

private def program_rLRRLR : Program cs_rLRRLR :=
  .promote ⟨5, tris336, tgt336, [15, 9, 3], cov336⟩ <|
  .promote ⟨6, tris337, tgt337, [16, 8, 6, 1, 0], cov337⟩ <|
  .stop ⟨10, tris338, [15, 14, 9, 1, 0], cov338⟩

private def program_rLRRL : Program cs_rLRRL :=
  .promote ⟨12, tris274, tgt274, [20], cov274⟩ <|
  .promote ⟨13, tris275, tgt275, [21, 16, 0], cov275⟩ <|
  .promote ⟨8, tris276, tgt276, [15, 7, 1], cov276⟩ <|
  .promote ⟨5, tris277, tgt277, [18, 7, 4, 3, 0], cov277⟩ <|
  .promote ⟨6, tris278, tgt278, [27, 19, 7, 4, 0], cov278⟩ <|
  .promote ⟨8, tris279, tgt279, [18, 4, 1], cov279⟩ <|
  .promote ⟨11, tris280, tgt280, [71, 21, 18, 8, 1], cov280⟩ <|
  .promote ⟨15, tris281, tgt281, [0], cov281⟩ <|
  .promote ⟨1, tris282, tgt282, [12, 9, 4, 3], cov282⟩ <|
  .promote ⟨3, tris283, tgt283, [4], cov283⟩ <|
  .promote ⟨10, tris285, tgt285, [23, 8, 6, 5, 3, 2], cov285⟩ <|
  .promote ⟨11, tris286, tgt286, [6, 3, 0], cov286⟩ <|
  .promote ⟨13, tris287, tgt287, [11, 6, 1], cov287⟩ <|
  .promote ⟨15, tris288, tgt288, [1], cov288⟩ <|
  .promote ⟨0, tris289, tgt289, [5], cov289⟩ <|
  .promote ⟨5, tris290, tgt290, [19, 10, 9, 6, 4, 0], cov290⟩ <|
  .promote ⟨6, tris291, tgt291, [9, 7, 6, 5, 4, 0], cov291⟩ <|
  .promote ⟨8, tris292, tgt292, [16, 4, 1], cov292⟩ <|
  .promote ⟨11, tris293, tgt293, [83, 7, 4, 1], cov293⟩ <|
  .promote ⟨1, tris296, tgt296, [4, 3, 2], cov296⟩ <|
  .promote ⟨3, tris297, tgt297, [3], cov297⟩ <|
  .promote ⟨5, tris298, tgt298, [10, 6, 4, 3, 1], cov298⟩ <|
  .promote ⟨8, tris299, tgt299, [21, 9, 0], cov299⟩ <|
  .promote ⟨12, tris300, tgt300, [0], cov300⟩ <|
  .promote ⟨0, tris301, tgt301, [4], cov301⟩ <|
  .promote ⟨1, tris302, tgt302, [8, 3, 0], cov302⟩ <|
  .split 5 (0) (1) (7350280588) program_rLRRLL program_rLRRLR

private def program_rLRRR : Program cs_rLRRR :=
  .promote ⟨12, tris339, tgt339, [20, 13, 8], cov339⟩ <|
  .promote ⟨13, tris340, tgt340, [21, 16, 0], cov340⟩ <|
  .promote ⟨10, tris341, tgt341, [14, 7, 6, 5, 4, 0], cov341⟩ <|
  .promote ⟨11, tris342, tgt342, [68, 15, 7, 5, 0], cov342⟩ <|
  .promote ⟨5, tris343, tgt343, [24, 8, 5, 4, 1], cov343⟩ <|
  .promote ⟨6, tris344, tgt344, [28, 5, 2, 1, 0], cov344⟩ <|
  .promote ⟨0, tris345, tgt345, [6, 1], cov345⟩ <|
  .stop ⟨1, tris346, [2, 1, 0], cov346⟩

private def program_rLRR : Program cs_rLRR :=
  .promote ⟨10, tris258, tgt258, [19, 15, 14, 13, 5, 0], cov258⟩ <|
  .promote ⟨11, tris259, tgt259, [50, 20, 14, 6, 0], cov259⟩ <|
  .promote ⟨13, tris260, tgt260, [11, 6, 5, 1], cov260⟩ <|
  .promote ⟨15, tris261, tgt261, [1], cov261⟩ <|
  .promote ⟨6, tris262, tgt262, [12, 11, 5, 4, 3, 2], cov262⟩ <|
  .promote ⟨11, tris263, tgt263, [54, 4, 1, 0], cov263⟩ <|
  .promote ⟨12, tris264, tgt264, [10, 3], cov264⟩ <|
  .promote ⟨13, tris265, tgt265, [11, 6, 0], cov265⟩ <|
  .promote ⟨15, tris266, tgt266, [2], cov266⟩ <|
  .promote ⟨1, tris267, tgt267, [11, 9, 4], cov267⟩ <|
  .promote ⟨5, tris268, tgt268, [14, 12, 9, 5, 0], cov268⟩ <|
  .promote ⟨6, tris269, tgt269, [18, 10, 9, 5, 1, 0], cov269⟩ <|
  .promote ⟨11, tris270, tgt270, [11, 3, 0], cov270⟩ <|
  .promote ⟨15, tris271, tgt271, [0], cov271⟩ <|
  .promote ⟨0, tris272, tgt272, [4], cov272⟩ <|
  .promote ⟨1, tris273, tgt273, [4, 3, 0], cov273⟩ <|
  .split 12 (1) (0) (2666915965) program_rLRRL program_rLRRR

private def program_rLR : Program cs_rLR :=
  .promote ⟨15, tris202, tgt202, [8], cov202⟩ <|
  .promote ⟨10, tris203, tgt203, [22, 11, 9, 2, 0], cov203⟩ <|
  .promote ⟨11, tris204, tgt204, [12, 1, 0], cov204⟩ <|
  .promote ⟨6, tris205, tgt205, [8, 4, 3, 1, 0], cov205⟩ <|
  .promote ⟨11, tris206, tgt206, [3, 2, 0], cov206⟩ <|
  .promote ⟨15, tris207, tgt207, [0], cov207⟩ <|
  .promote ⟨1, tris208, tgt208, [9, 7, 2], cov208⟩ <|
  .promote ⟨5, tris209, tgt209, [24, 10, 5, 3, 0], cov209⟩ <|
  .promote ⟨8, tris210, tgt210, [29, 22, 0], cov210⟩ <|
  .promote ⟨10, tris211, tgt211, [30, 5, 4, 3, 1], cov211⟩ <|
  .promote ⟨11, tris212, tgt212, [9, 6, 4, 0], cov212⟩ <|
  .promote ⟨13, tris213, tgt213, [25, 18, 2, 1], cov213⟩ <|
  .promote ⟨0, tris214, tgt214, [5], cov214⟩ <|
  .promote ⟨1, tris215, tgt215, [9, 5, 0], cov215⟩ <|
  .promote ⟨5, tris216, tgt216, [10, 5, 4, 1, 0], cov216⟩ <|
  .promote ⟨6, tris217, tgt217, [20, 5, 4, 1, 0], cov217⟩ <|
  .promote ⟨8, tris218, tgt218, [30, 4, 1], cov218⟩ <|
  .promote ⟨10, tris219, tgt219, [11, 6, 5, 2, 1], cov219⟩ <|
  .promote ⟨11, tris220, tgt220, [17, 12, 2, 0], cov220⟩ <|
  .promote ⟨13, tris221, tgt221, [33, 26, 2, 1], cov221⟩ <|
  .promote ⟨15, tris222, tgt222, [1], cov222⟩ <|
  .promote ⟨0, tris223, tgt223, [7], cov223⟩ <|
  .promote ⟨1, tris224, tgt224, [7, 6, 0], cov224⟩ <|
  .promote ⟨5, tris225, tgt225, [7, 6, 5, 1, 0], cov225⟩ <|
  .promote ⟨6, tris226, tgt226, [29, 6, 5, 1, 0], cov226⟩ <|
  .promote ⟨8, tris227, tgt227, [39, 5, 1], cov227⟩ <|
  .promote ⟨10, tris228, tgt228, [7, 6, 5, 2, 1], cov228⟩ <|
  .promote ⟨11, tris229, tgt229, [26, 6, 2, 0], cov229⟩ <|
  .promote ⟨12, tris230, tgt230, [8, 2], cov230⟩ <|
  .promote ⟨13, tris231, tgt231, [3, 2, 0], cov231⟩ <|
  .promote ⟨15, tris232, tgt232, [2], cov232⟩ <|
  .promote ⟨0, tris233, tgt233, [8], cov233⟩ <|
  .promote ⟨6, tris234, tgt234, [37, 9, 8, 5, 4], cov234⟩ <|
  .promote ⟨10, tris235, tgt235, [9, 5, 3, 2, 0], cov235⟩ <|
  .promote ⟨11, tris236, tgt236, [33, 3, 1, 0], cov236⟩ <|
  .promote ⟨13, tris237, tgt237, [9, 6, 1], cov237⟩ <|
  .promote ⟨15, tris238, tgt238, [1], cov238⟩ <|
  .promote ⟨5, tris239, tgt239, [14, 11, 5, 4, 3], cov239⟩ <|
  .promote ⟨6, tris240, tgt240, [43, 15, 4, 3, 0], cov240⟩ <|
  .promote ⟨8, tris241, tgt241, [10, 3, 1], cov241⟩ <|
  .promote ⟨12, tris242, tgt242, [4, 0], cov242⟩ <|
  .promote ⟨1, tris243, tgt243, [9, 3, 2], cov243⟩ <|
  .promote ⟨3, tris244, tgt244, [3], cov244⟩ <|
  .promote ⟨5, tris245, tgt245, [11, 9, 4, 3, 1], cov245⟩ <|
  .promote ⟨6, tris246, tgt246, [10, 9, 2, 1, 0], cov246⟩ <|
  .promote ⟨8, tris247, tgt247, [9, 4, 1], cov247⟩ <|
  .promote ⟨12, tris248, tgt248, [10, 0], cov248⟩ <|
  .promote ⟨0, tris249, tgt249, [5], cov249⟩ <|
  .promote ⟨1, tris250, tgt250, [4, 3, 0], cov250⟩ <|
  .promote ⟨5, tris251, tgt251, [15, 4, 3, 1, 0], cov251⟩ <|
  .split 10 (1) (0) (8927663811) program_rLRL program_rLRR

private def program_rL : Program cs_rL :=
  .promote ⟨0, tris105, tgt105, [0], cov105⟩ <|
  .promote ⟨1, tris106, tgt106, [9, 4, 0], cov106⟩ <|
  .promote ⟨5, tris107, tgt107, [15, 10, 9, 4, 1, 0], cov107⟩ <|
  .promote ⟨6, tris108, tgt108, [16, 10, 9, 7, 1, 0], cov108⟩ <|
  .promote ⟨10, tris109, tgt109, [34, 24, 10, 1, 0], cov109⟩ <|
  .promote ⟨11, tris110, tgt110, [35, 24, 1, 0], cov110⟩ <|
  .promote ⟨13, tris111, tgt111, [8, 7, 1], cov111⟩ <|
  .promote ⟨15, tris112, tgt112, [2, 1, 0], cov112⟩ <|
  .promote ⟨1, tris113, tgt113, [11, 7, 5, 4], cov113⟩ <|
  .promote ⟨5, tris114, tgt114, [11, 8, 5, 4, 0], cov114⟩ <|
  .promote ⟨8, tris115, tgt115, [11, 3, 0], cov115⟩ <|
  .promote ⟨10, tris116, tgt116, [7, 5, 4, 3, 1], cov116⟩ <|
  .promote ⟨11, tris117, tgt117, [8, 4, 0], cov117⟩ <|
  .promote ⟨12, tris118, tgt118, [6, 2], cov118⟩ <|
  .promote ⟨13, tris119, tgt119, [3, 2, 0], cov119⟩ <|
  .promote ⟨0, tris121, tgt121, [6], cov121⟩ <|
  .promote ⟨5, tris122, tgt122, [12, 7, 5, 4, 0], cov122⟩ <|
  .promote ⟨6, tris123, tgt123, [21, 11, 8, 7, 5, 4, 0], cov123⟩ <|
  .promote ⟨8, tris124, tgt124, [11, 8, 4], cov124⟩ <|
  .promote ⟨11, tris125, tgt125, [11, 7, 1], cov125⟩ <|
  .promote ⟨12, tris126, tgt126, [13, 9, 5, 1], cov126⟩ <|
  .promote ⟨1, tris128, tgt128, [11, 5, 4, 3], cov128⟩ <|
  .promote ⟨3, tris129, tgt129, [4], cov129⟩ <|
  .promote ⟨10, tris130, tgt130, [16, 15, 13, 5, 3], cov130⟩ <|
  .promote ⟨0, tris131, tgt131, [2], cov131⟩ <|
  .promote ⟨1, tris132, tgt132, [15, 8, 7, 0], cov132⟩ <|
  .promote ⟨5, tris133, tgt133, [15, 8, 2, 1, 0], cov133⟩ <|
  .promote ⟨1, tris134, tgt134, [9, 2, 0], cov134⟩ <|
  .split 15 (1) (0) (13724860214) program_rLL program_rLR

private def program_rRL : Program cs_rRL :=
  .promote ⟨15, tris404, tgt404, [13, 12, 10], cov404⟩ <|
  .promote ⟨10, tris405, tgt405, [13, 11, 2, 1, 0], cov405⟩ <|
  .promote ⟨11, tris406, tgt406, [2, 1, 0], cov406⟩ <|
  .promote ⟨5, tris407, tgt407, [17, 7, 6, 3, 1], cov407⟩ <|
  .promote ⟨6, tris408, tgt408, [7, 6, 2, 1, 0], cov408⟩ <|
  .promote ⟨0, tris409, tgt409, [8, 1], cov409⟩ <|
  .stop ⟨1, tris410, [2, 1, 0], cov410⟩

private def program_rRRL : Program cs_rRRL :=
  .promote ⟨0, tris428, tgt428, [2], cov428⟩ <|
  .promote ⟨1, tris429, tgt429, [13, 11, 0], cov429⟩ <|
  .promote ⟨6, tris430, tgt430, [20, 12, 10, 9, 0], cov430⟩ <|
  .promote ⟨10, tris431, tgt431, [16, 13, 10, 8, 7, 0], cov431⟩ <|
  .promote ⟨11, tris432, tgt432, [17, 8, 1, 0], cov432⟩ <|
  .promote ⟨13, tris433, tgt433, [14, 6, 1], cov433⟩ <|
  .promote ⟨15, tris434, tgt434, [1], cov434⟩ <|
  .promote ⟨10, tris436, tgt436, [17, 4, 2, 1, 0], cov436⟩ <|
  .promote ⟨11, tris437, tgt437, [5, 1, 0], cov437⟩ <|
  .promote ⟨5, tris438, tgt438, [18, 8, 7, 6, 1], cov438⟩ <|
  .promote ⟨6, tris439, tgt439, [28, 8, 2, 1, 0], cov439⟩ <|
  .promote ⟨0, tris440, tgt440, [9, 1], cov440⟩ <|
  .stop ⟨1, tris441, [2, 1, 0], cov441⟩

private def program_rRRR : Program cs_rRRR :=
  .promote ⟨0, tris442, tgt442, [10, 2, 0], cov442⟩ <|
  .promote ⟨1, tris443, tgt443, [13, 11, 0], cov443⟩ <|
  .promote ⟨5, tris444, tgt444, [14, 11, 10, 1, 0], cov444⟩ <|
  .promote ⟨6, tris445, tgt445, [21, 11, 10, 1, 0], cov445⟩ <|
  .promote ⟨8, tris446, tgt446, [9, 5, 1], cov446⟩ <|
  .promote ⟨10, tris447, tgt447, [18, 12, 10, 9, 2, 1], cov447⟩ <|
  .promote ⟨11, tris448, tgt448, [19, 2, 0], cov448⟩ <|
  .promote ⟨12, tris449, tgt449, [12, 2], cov449⟩ <|
  .promote ⟨13, tris450, tgt450, [3, 2, 0], cov450⟩ <|
  .promote ⟨15, tris451, tgt451, [3, 2], cov451⟩ <|
  .promote ⟨0, tris452, tgt452, [8, 7, 5], cov452⟩ <|
  .promote ⟨3, tris453, tgt453, [7], cov453⟩ <|
  .promote ⟨5, tris454, tgt454, [10, 8, 7, 6, 1], cov454⟩ <|
  .promote ⟨6, tris455, tgt455, [11, 7, 6, 1, 0], cov455⟩ <|
  .stop ⟨10, tris456, [7, 5, 4, 1, 0], cov456⟩

private def program_rRR : Program cs_rRR :=
  .promote ⟨15, tris411, tgt411, [12], cov411⟩ <|
  .promote ⟨11, tris412, tgt412, [14, 1, 0], cov412⟩ <|
  .promote ⟨15, tris413, tgt413, [0], cov413⟩ <|
  .promote ⟨6, tris414, tgt414, [16, 6, 5, 4, 1], cov414⟩ <|
  .promote ⟨1, tris415, tgt415, [8, 5, 0], cov415⟩ <|
  .promote ⟨5, tris416, tgt416, [19, 18, 9, 1, 0], cov416⟩ <|
  .promote ⟨8, tris417, tgt417, [17, 16, 0], cov417⟩ <|
  .promote ⟨10, tris418, tgt418, [17, 5, 4, 3, 1], cov418⟩ <|
  .promote ⟨11, tris419, tgt419, [5, 4, 0], cov419⟩ <|
  .promote ⟨12, tris420, tgt420, [19, 2], cov420⟩ <|
  .promote ⟨13, tris421, tgt421, [3, 2, 0], cov421⟩ <|
  .promote ⟨15, tris422, tgt422, [2], cov422⟩ <|
  .promote ⟨0, tris423, tgt423, [7, 6, 5], cov423⟩ <|
  .promote ⟨1, tris424, tgt424, [9, 7, 0], cov424⟩ <|
  .promote ⟨12, tris426, tgt426, [7, 3], cov426⟩ <|
  .promote ⟨8, tris427, tgt427, [9, 4, 0], cov427⟩ <|
  .split 0 (0) (1) (3610093563) program_rRRL program_rRRR

private def program_rR : Program cs_rR :=
  .promote ⟨0, tris347, tgt347, [3, 2, 0], cov347⟩ <|
  .promote ⟨1, tris348, tgt348, [9, 4, 0], cov348⟩ <|
  .promote ⟨5, tris349, tgt349, [15, 10, 9, 4, 1, 0], cov349⟩ <|
  .promote ⟨6, tris350, tgt350, [16, 10, 9, 7, 1, 0], cov350⟩ <|
  .promote ⟨10, tris351, tgt351, [34, 24, 10, 1, 0], cov351⟩ <|
  .promote ⟨11, tris352, tgt352, [35, 24, 1, 0], cov352⟩ <|
  .promote ⟨13, tris353, tgt353, [8, 7, 1], cov353⟩ <|
  .promote ⟨15, tris354, tgt354, [2, 1, 0], cov354⟩ <|
  .promote ⟨1, tris356, tgt356, [7, 5, 4], cov356⟩ <|
  .promote ⟨3, tris357, tgt357, [5], cov357⟩ <|
  .promote ⟨5, tris358, tgt358, [12, 9, 6, 5, 1], cov358⟩ <|
  .promote ⟨6, tris359, tgt359, [6, 5, 2, 1, 0], cov359⟩ <|
  .promote ⟨8, tris360, tgt360, [13, 5, 1], cov360⟩ <|
  .promote ⟨10, tris361, tgt361, [7, 6, 5, 2, 1], cov361⟩ <|
  .promote ⟨11, tris362, tgt362, [6, 2, 0], cov362⟩ <|
  .promote ⟨12, tris363, tgt363, [8, 2], cov363⟩ <|
  .promote ⟨13, tris364, tgt364, [3, 2, 0], cov364⟩ <|
  .promote ⟨15, tris365, tgt365, [3, 2, 0], cov365⟩ <|
  .promote ⟨0, tris366, tgt366, [9, 7, 5], cov366⟩ <|
  .promote ⟨1, tris367, tgt367, [8, 7, 0], cov367⟩ <|
  .promote ⟨3, tris368, tgt368, [8], cov368⟩ <|
  .promote ⟨5, tris369, tgt369, [9, 8, 7, 2, 1], cov369⟩ <|
  .promote ⟨6, tris370, tgt370, [8, 7, 2, 1, 0], cov370⟩ <|
  .promote ⟨8, tris371, tgt371, [7, 6, 1], cov371⟩ <|
  .promote ⟨11, tris372, tgt372, [10, 6, 1], cov372⟩ <|
  .promote ⟨12, tris373, tgt373, [8, 1], cov373⟩ <|
  .promote ⟨0, tris375, tgt375, [6, 4, 2], cov375⟩ <|
  .promote ⟨1, tris376, tgt376, [5, 4, 0], cov376⟩ <|
  .promote ⟨3, tris377, tgt377, [5], cov377⟩ <|
  .promote ⟨5, tris378, tgt378, [15, 6, 5, 2, 1], cov378⟩ <|
  .promote ⟨6, tris379, tgt379, [16, 5, 2, 1, 0], cov379⟩ <|
  .promote ⟨8, tris380, tgt380, [14, 5, 1], cov380⟩ <|
  .promote ⟨10, tris381, tgt381, [15, 14, 7, 2, 1], cov381⟩ <|
  .promote ⟨11, tris382, tgt382, [15, 2, 0], cov382⟩ <|
  .promote ⟨13, tris383, tgt383, [8, 2, 1], cov383⟩ <|
  .promote ⟨15, tris384, tgt384, [2, 1, 0], cov384⟩ <|
  .promote ⟨0, tris385, tgt385, [8, 6, 4], cov385⟩ <|
  .promote ⟨1, tris386, tgt386, [7, 6, 0], cov386⟩ <|
  .promote ⟨5, tris387, tgt387, [7, 6, 5, 1, 0], cov387⟩ <|
  .promote ⟨6, tris388, tgt388, [10, 6, 5, 1, 0], cov388⟩ <|
  .promote ⟨8, tris389, tgt389, [14, 5, 1], cov389⟩ <|
  .promote ⟨10, tris390, tgt390, [23, 7, 6, 2, 1], cov390⟩ <|
  .promote ⟨11, tris391, tgt391, [24, 6, 2, 0], cov391⟩ <|
  .promote ⟨12, tris392, tgt392, [8, 2], cov392⟩ <|
  .promote ⟨13, tris393, tgt393, [3, 2, 0], cov393⟩ <|
  .promote ⟨0, tris394, tgt394, [7, 6, 4], cov394⟩ <|
  .promote ⟨1, tris395, tgt395, [7, 6, 0], cov395⟩ <|
  .promote ⟨3, tris396, tgt396, [7], cov396⟩ <|
  .promote ⟨5, tris397, tgt397, [8, 7, 6, 2, 1], cov397⟩ <|
  .promote ⟨6, tris398, tgt398, [7, 6, 2, 1, 0], cov398⟩ <|
  .promote ⟨0, tris399, tgt399, [9, 3, 1], cov399⟩ <|
  .promote ⟨1, tris400, tgt400, [2, 1, 0], cov400⟩ <|
  .promote ⟨3, tris401, tgt401, [2], cov401⟩ <|
  .promote ⟨5, tris402, tgt402, [12, 11, 3, 2, 1], cov402⟩ <|
  .promote ⟨6, tris403, tgt403, [12, 11, 2, 1, 0], cov403⟩ <|
  .split 15 (1) (0) (13074392905) program_rRL program_rRR

private def program_r : Program cs_r :=
  .promote ⟨0, tris0, tgt0, [], cov0⟩ <|
  .promote ⟨1, tris1, tgt1, [0], cov1⟩ <|
  .promote ⟨3, tris2, tgt2, [0], cov2⟩ <|
  .promote ⟨5, tris3, tgt3, [2, 1], cov3⟩ <|
  .promote ⟨6, tris4, tgt4, [2, 1, 0], cov4⟩ <|
  .promote ⟨8, tris5, tgt5, [1], cov5⟩ <|
  .promote ⟨11, tris6, tgt6, [1], cov6⟩ <|
  .promote ⟨12, tris7, tgt7, [1], cov7⟩ <|
  .promote ⟨13, tris8, tgt8, [2, 0], cov8⟩ <|
  .promote ⟨15, tris9, tgt9, [2], cov9⟩ <|
  .promote ⟨0, tris10, tgt10, [8, 6], cov10⟩ <|
  .promote ⟨1, tris11, tgt11, [7, 0], cov11⟩ <|
  .promote ⟨3, tris12, tgt12, [7, 0], cov12⟩ <|
  .promote ⟨5, tris13, tgt13, [8, 7, 2, 1], cov13⟩ <|
  .promote ⟨6, tris14, tgt14, [7, 2, 1, 0], cov14⟩ <|
  .promote ⟨8, tris15, tgt15, [7, 6, 1], cov15⟩ <|
  .promote ⟨10, tris16, tgt16, [9, 7, 6, 2, 1], cov16⟩ <|
  .promote ⟨11, tris17, tgt17, [7, 2, 0], cov17⟩ <|
  .promote ⟨12, tris18, tgt18, [9, 2], cov18⟩ <|
  .promote ⟨13, tris19, tgt19, [3, 2, 0], cov19⟩ <|
  .promote ⟨15, tris20, tgt20, [3, 2, 0], cov20⟩ <|
  .promote ⟨0, tris21, tgt21, [9, 7, 5], cov21⟩ <|
  .promote ⟨5, tris22, tgt22, [10, 7, 6, 5, 0], cov22⟩ <|
  .promote ⟨6, tris23, tgt23, [11, 10, 6, 5, 0], cov23⟩ <|
  .promote ⟨8, tris24, tgt24, [5, 4, 1], cov24⟩ <|
  .promote ⟨10, tris25, tgt25, [7, 5, 4, 2, 1], cov25⟩ <|
  .promote ⟨11, tris26, tgt26, [5, 2, 0], cov26⟩ <|
  .promote ⟨12, tris27, tgt27, [7, 2], cov27⟩ <|
  .promote ⟨13, tris28, tgt28, [3, 2, 0], cov28⟩ <|
  .promote ⟨15, tris29, tgt29, [3, 2, 0], cov29⟩ <|
  .promote ⟨0, tris30, tgt30, [18, 7, 5], cov30⟩ <|
  .promote ⟨1, tris31, tgt31, [8, 7, 0], cov31⟩ <|
  .promote ⟨3, tris32, tgt32, [8], cov32⟩ <|
  .promote ⟨5, tris33, tgt33, [9, 8, 2, 1], cov33⟩ <|
  .promote ⟨6, tris34, tgt34, [8, 7, 2, 1, 0], cov34⟩ <|
  .promote ⟨8, tris35, tgt35, [7, 6, 1], cov35⟩ <|
  .promote ⟨10, tris36, tgt36, [9, 7, 6, 2, 1], cov36⟩ <|
  .promote ⟨11, tris37, tgt37, [7, 2, 0], cov37⟩ <|
  .promote ⟨12, tris38, tgt38, [9, 2], cov38⟩ <|
  .promote ⟨13, tris39, tgt39, [3, 2, 0], cov39⟩ <|
  .promote ⟨15, tris40, tgt40, [3, 2, 0], cov40⟩ <|
  .promote ⟨0, tris41, tgt41, [9, 7, 5], cov41⟩ <|
  .promote ⟨1, tris42, tgt42, [8, 7, 0], cov42⟩ <|
  .promote ⟨3, tris43, tgt43, [8], cov43⟩ <|
  .promote ⟨5, tris44, tgt44, [9, 8, 2, 1], cov44⟩ <|
  .promote ⟨6, tris45, tgt45, [8, 7, 2, 1, 0], cov45⟩ <|
  .promote ⟨8, tris46, tgt46, [7, 6, 1], cov46⟩ <|
  .promote ⟨10, tris47, tgt47, [9, 7, 6, 2, 1], cov47⟩ <|
  .promote ⟨11, tris48, tgt48, [7, 2, 0], cov48⟩ <|
  .promote ⟨12, tris49, tgt49, [9, 2], cov49⟩ <|
  .promote ⟨13, tris50, tgt50, [3, 2, 0], cov50⟩ <|
  .promote ⟨15, tris51, tgt51, [3, 2, 0], cov51⟩ <|
  .promote ⟨0, tris52, tgt52, [9, 7, 5], cov52⟩ <|
  .promote ⟨1, tris53, tgt53, [8, 7, 0], cov53⟩ <|
  .promote ⟨3, tris54, tgt54, [8], cov54⟩ <|
  .promote ⟨5, tris55, tgt55, [9, 8, 7, 2, 1], cov55⟩ <|
  .promote ⟨6, tris56, tgt56, [8, 7, 2, 1, 0], cov56⟩ <|
  .promote ⟨8, tris57, tgt57, [7, 6, 1], cov57⟩ <|
  .promote ⟨10, tris58, tgt58, [9, 7, 6, 2, 1], cov58⟩ <|
  .promote ⟨11, tris59, tgt59, [7, 2, 0], cov59⟩ <|
  .promote ⟨12, tris60, tgt60, [9, 2], cov60⟩ <|
  .promote ⟨13, tris61, tgt61, [3, 2, 0], cov61⟩ <|
  .promote ⟨15, tris62, tgt62, [3, 2, 0], cov62⟩ <|
  .promote ⟨0, tris63, tgt63, [9, 7, 5], cov63⟩ <|
  .promote ⟨1, tris64, tgt64, [8, 7, 0], cov64⟩ <|
  .promote ⟨3, tris65, tgt65, [8], cov65⟩ <|
  .promote ⟨5, tris66, tgt66, [9, 8, 7, 2, 1], cov66⟩ <|
  .promote ⟨6, tris67, tgt67, [8, 7, 2, 1, 0], cov67⟩ <|
  .promote ⟨8, tris68, tgt68, [7, 6, 1], cov68⟩ <|
  .promote ⟨10, tris69, tgt69, [17, 9, 7, 2, 1], cov69⟩ <|
  .promote ⟨11, tris70, tgt70, [18, 7, 2, 0], cov70⟩ <|
  .promote ⟨12, tris71, tgt71, [9, 2], cov71⟩ <|
  .promote ⟨13, tris72, tgt72, [3, 2, 0], cov72⟩ <|
  .promote ⟨15, tris73, tgt73, [3, 2, 0], cov73⟩ <|
  .promote ⟨0, tris74, tgt74, [9, 7, 5], cov74⟩ <|
  .promote ⟨1, tris75, tgt75, [8, 7, 0], cov75⟩ <|
  .promote ⟨3, tris76, tgt76, [8], cov76⟩ <|
  .promote ⟨5, tris77, tgt77, [9, 8, 7, 2, 1], cov77⟩ <|
  .promote ⟨6, tris78, tgt78, [8, 7, 2, 1, 0], cov78⟩ <|
  .promote ⟨8, tris79, tgt79, [7, 6, 1], cov79⟩ <|
  .promote ⟨10, tris80, tgt80, [9, 7, 6, 2, 1], cov80⟩ <|
  .promote ⟨11, tris81, tgt81, [7, 2, 0], cov81⟩ <|
  .promote ⟨12, tris82, tgt82, [9, 2], cov82⟩ <|
  .promote ⟨13, tris83, tgt83, [3, 2, 0], cov83⟩ <|
  .promote ⟨15, tris84, tgt84, [3, 2, 0], cov84⟩ <|
  .promote ⟨0, tris85, tgt85, [9, 7, 5], cov85⟩ <|
  .promote ⟨1, tris86, tgt86, [8, 7, 0], cov86⟩ <|
  .promote ⟨5, tris87, tgt87, [8, 7, 6, 1, 0], cov87⟩ <|
  .promote ⟨6, tris88, tgt88, [11, 7, 6, 1, 0], cov88⟩ <|
  .promote ⟨8, tris89, tgt89, [6, 5, 1], cov89⟩ <|
  .promote ⟨10, tris90, tgt90, [16, 8, 6, 2, 1], cov90⟩ <|
  .promote ⟨12, tris91, tgt91, [7, 1], cov91⟩ <|
  .promote ⟨0, tris93, tgt93, [5, 4, 2], cov93⟩ <|
  .promote ⟨1, tris94, tgt94, [5, 4, 0], cov94⟩ <|
  .promote ⟨5, tris95, tgt95, [5, 4, 3, 1, 0], cov95⟩ <|
  .promote ⟨6, tris96, tgt96, [18, 13, 4, 1, 0], cov96⟩ <|
  .promote ⟨10, tris97, tgt97, [22, 14, 12, 1, 0], cov97⟩ <|
  .promote ⟨11, tris98, tgt98, [23, 12, 1, 0], cov98⟩ <|
  .promote ⟨1, tris99, tgt99, [5, 3, 2], cov99⟩ <|
  .promote ⟨3, tris100, tgt100, [3], cov100⟩ <|
  .promote ⟨5, tris101, tgt101, [10, 9, 7, 4, 3, 1], cov101⟩ <|
  .promote ⟨8, tris102, tgt102, [17, 9, 0], cov102⟩ <|
  .promote ⟨12, tris103, tgt103, [18, 0], cov103⟩ <|
  .promote ⟨1, tris104, tgt104, [10, 7, 2], cov104⟩ <|
  .split 0 (0) (1) (3236074860) program_rL program_rR

lemma hJ : J = maskAt 1465 := by decide +kernel

theorem excl_r : Excl Ux J cs_r :=
  check_sound le_rfl (by norm_num [Ux]) program_r
    (batchesOwnedC_nil Ux J cs_r) (by decide +kernel)

theorem notIn : ¬ RealizesIn Ux J := not_in_of_excl excl_r

theorem excluded : CaseExcluded (maskAt 1465) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Simplified.ReducedConditional.U2R.C1465
#print axioms SquarePacking.S11Opt.Simplified.ReducedConditional.U2R.C1465.excluded
