import Sqpack.S11Opt.Simplified.ConditionalOwnedTrace
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages000
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages004
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages008
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages011
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages012
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages013
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages001
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages002
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages003
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages005
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages006
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages007
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages009
import Sqpack.S11Opt.Simplified.ReducedConditional.U2P.C655.SharedStages010

namespace SquarePacking.S11Opt.Simplified.ReducedConditional.U2P.C655
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P
open SquarePacking.S11Opt.Simplified.ConditionalOwnedTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- One record per promotion; branch conditions remain in the program type. -/
private def program_rLL : Program cs_rLL :=
  .promote ⟨0, tris134, tgt134, [3], cov134⟩ <|
  .promote ⟨1, tris135, tgt135, [3, 2, 0], cov135⟩ <|
  .promote ⟨2, tris136, tgt136, [60, 10, 3, 0], cov136⟩ <|
  .promote ⟨3, tris137, tgt137, [0], cov137⟩ <|
  .promote ⟨5, tris138, tgt138, [13, 3, 2, 1], cov138⟩ <|
  .promote ⟨8, tris139, tgt139, [11, 5, 0], cov139⟩ <|
  .promote ⟨10, tris140, tgt140, [13, 12, 11, 3, 1], cov140⟩ <|
  .promote ⟨11, tris141, tgt141, [12, 4, 0], cov141⟩ <|
  .promote ⟨12, tris142, tgt142, [14, 2], cov142⟩ <|
  .promote ⟨13, tris143, tgt143, [4, 3, 2, 0], cov143⟩ <|
  .promote ⟨15, tris144, tgt144, [3, 2], cov144⟩ <|
  .promote ⟨0, tris145, tgt145, [9], cov145⟩ <|
  .promote ⟨1, tris146, tgt146, [9, 7, 0], cov146⟩ <|
  .promote ⟨2, tris147, tgt147, [11, 9, 8, 6, 0], cov147⟩ <|
  .promote ⟨5, tris148, tgt148, [12, 8, 2, 1, 0], cov148⟩ <|
  .promote ⟨8, tris149, tgt149, [6, 5, 0], cov149⟩ <|
  .promote ⟨10, tris150, tgt150, [8, 6, 5, 2, 1], cov150⟩ <|
  .promote ⟨11, tris151, tgt151, [3, 0], cov151⟩ <|
  .promote ⟨12, tris152, tgt152, [8, 2], cov152⟩ <|
  .promote ⟨13, tris153, tgt153, [4, 3, 2, 0], cov153⟩ <|
  .promote ⟨15, tris154, tgt154, [3, 2], cov154⟩ <|
  .promote ⟨0, tris155, tgt155, [19, 8], cov155⟩ <|
  .promote ⟨1, tris156, tgt156, [8, 7, 0], cov156⟩ <|
  .promote ⟨2, tris157, tgt157, [19, 8, 6, 5, 0], cov157⟩ <|
  .promote ⟨5, tris158, tgt158, [8, 2, 1, 0], cov158⟩ <|
  .stop ⟨10, tris159, [7, 5, 4, 1, 0], cov159⟩

private def program_rLRL : Program cs_rLRL :=
  .promote ⟨11, tris182, tgt182, [5, 3], cov182⟩ <|
  .promote ⟨2, tris184, tgt184, [15, 7, 5, 4, 0], cov184⟩ <|
  .promote ⟨5, tris185, tgt185, [15, 8, 3, 0], cov185⟩ <|
  .promote ⟨8, tris186, tgt186, [5, 3, 0], cov186⟩ <|
  .promote ⟨10, tris187, tgt187, [27, 12, 6, 3, 2, 1], cov187⟩ <|
  .promote ⟨11, tris188, tgt188, [3, 0], cov188⟩ <|
  .promote ⟨12, tris189, tgt189, [8, 2], cov189⟩ <|
  .promote ⟨13, tris190, tgt190, [4, 3, 2, 0], cov190⟩ <|
  .promote ⟨15, tris191, tgt191, [3, 2], cov191⟩ <|
  .promote ⟨0, tris192, tgt192, [15, 6, 5], cov192⟩ <|
  .promote ⟨1, tris193, tgt193, [8, 7, 0], cov193⟩ <|
  .promote ⟨2, tris194, tgt194, [15, 8, 6, 5, 0], cov194⟩ <|
  .promote ⟨3, tris195, tgt195, [0], cov195⟩ <|
  .promote ⟨5, tris196, tgt196, [9, 3, 2, 1], cov196⟩ <|
  .promote ⟨8, tris197, tgt197, [7, 6, 0], cov197⟩ <|
  .promote ⟨10, tris198, tgt198, [9, 7, 6, 3, 1], cov198⟩ <|
  .promote ⟨11, tris199, tgt199, [4, 0], cov199⟩ <|
  .promote ⟨12, tris200, tgt200, [9, 2], cov200⟩ <|
  .promote ⟨13, tris201, tgt201, [4, 3, 2, 0], cov201⟩ <|
  .promote ⟨15, tris202, tgt202, [3, 2], cov202⟩ <|
  .promote ⟨0, tris203, tgt203, [9, 6, 5], cov203⟩ <|
  .promote ⟨1, tris204, tgt204, [9, 7, 0], cov204⟩ <|
  .promote ⟨2, tris205, tgt205, [9, 8, 6, 5, 0], cov205⟩ <|
  .promote ⟨5, tris207, tgt207, [8, 2, 1, 0], cov207⟩ <|
  .promote ⟨8, tris208, tgt208, [6, 5, 0], cov208⟩ <|
  .promote ⟨10, tris209, tgt209, [8, 6, 5, 2, 1], cov209⟩ <|
  .promote ⟨11, tris210, tgt210, [3, 0], cov210⟩ <|
  .promote ⟨12, tris211, tgt211, [8, 2], cov211⟩ <|
  .promote ⟨13, tris212, tgt212, [4, 3, 2, 0], cov212⟩ <|
  .promote ⟨15, tris213, tgt213, [3, 2], cov213⟩ <|
  .promote ⟨1, tris214, tgt214, [9, 7, 6], cov214⟩ <|
  .promote ⟨2, tris215, tgt215, [18, 7, 5, 4, 0], cov215⟩ <|
  .promote ⟨5, tris217, tgt217, [11, 7, 1, 0], cov217⟩ <|
  .promote ⟨8, tris218, tgt218, [5, 4, 0], cov218⟩ <|
  .promote ⟨10, tris219, tgt219, [7, 5, 4, 2, 1], cov219⟩ <|
  .promote ⟨11, tris220, tgt220, [3, 0], cov220⟩ <|
  .promote ⟨12, tris221, tgt221, [7, 2], cov221⟩ <|
  .promote ⟨15, tris222, tgt222, [2, 1], cov222⟩ <|
  .promote ⟨0, tris223, tgt223, [7, 5, 4], cov223⟩ <|
  .promote ⟨1, tris224, tgt224, [7, 6, 0], cov224⟩ <|
  .promote ⟨2, tris225, tgt225, [27, 7, 5, 4, 0], cov225⟩ <|
  .promote ⟨3, tris226, tgt226, [5, 0], cov226⟩ <|
  .promote ⟨5, tris227, tgt227, [8, 3, 2, 1], cov227⟩ <|
  .promote ⟨8, tris228, tgt228, [14, 6, 0], cov228⟩ <|
  .promote ⟨10, tris229, tgt229, [15, 8, 6, 3, 1], cov229⟩ <|
  .promote ⟨11, tris230, tgt230, [4, 0], cov230⟩ <|
  .promote ⟨12, tris231, tgt231, [17, 2], cov231⟩ <|
  .promote ⟨13, tris232, tgt232, [4, 3, 2, 0], cov232⟩ <|
  .promote ⟨15, tris233, tgt233, [3, 2], cov233⟩ <|
  .promote ⟨0, tris234, tgt234, [9, 6, 5], cov234⟩ <|
  .promote ⟨1, tris235, tgt235, [9, 7, 0], cov235⟩ <|
  .promote ⟨2, tris236, tgt236, [9, 8, 6, 5, 0], cov236⟩ <|
  .promote ⟨5, tris237, tgt237, [8, 2, 1, 0], cov237⟩ <|
  .stop ⟨10, tris238, [7, 5, 4, 1, 0], cov238⟩

private def program_rLRR : Program cs_rLRR :=
  .promote ⟨11, tris239, tgt239, [8, 5, 3], cov239⟩ <|
  .promote ⟨15, tris240, tgt240, [4, 0], cov240⟩ <|
  .stop ⟨10, tris241, [16, 7, 4, 1, 0], cov241⟩

private def program_rLR : Program cs_rLR :=
  .promote ⟨0, tris160, tgt160, [37, 9, 3, 1], cov160⟩ <|
  .promote ⟨1, tris161, tgt161, [3, 2, 0], cov161⟩ <|
  .promote ⟨2, tris162, tgt162, [60, 10, 3, 0], cov162⟩ <|
  .promote ⟨5, tris164, tgt164, [12, 2, 1, 0], cov164⟩ <|
  .promote ⟨8, tris165, tgt165, [10, 4, 0], cov165⟩ <|
  .promote ⟨10, tris166, tgt166, [12, 11, 10, 2, 1], cov166⟩ <|
  .promote ⟨11, tris167, tgt167, [11, 3, 0], cov167⟩ <|
  .promote ⟨12, tris168, tgt168, [13, 2], cov168⟩ <|
  .promote ⟨13, tris169, tgt169, [8, 4, 3, 2, 0], cov169⟩ <|
  .promote ⟨15, tris170, tgt170, [3, 2], cov170⟩ <|
  .promote ⟨0, tris171, tgt171, [8, 6, 5], cov171⟩ <|
  .promote ⟨1, tris172, tgt172, [8, 7, 0], cov172⟩ <|
  .promote ⟨2, tris173, tgt173, [70, 8, 6, 0], cov173⟩ <|
  .promote ⟨3, tris174, tgt174, [0], cov174⟩ <|
  .promote ⟨10, tris175, tgt175, [10, 7, 5, 4, 1], cov175⟩ <|
  .promote ⟨13, tris177, tgt177, [15, 11, 10, 7, 0], cov177⟩ <|
  .promote ⟨0, tris179, tgt179, [12, 11, 4], cov179⟩ <|
  .promote ⟨12, tris181, tgt181, [12, 1], cov181⟩ <|
  .split 11 (0) (1) (8781308668) program_rLRL program_rLRR

private def program_rL : Program cs_rL :=
  .promote ⟨15, tris111, tgt111, [5, 2], cov111⟩ <|
  .promote ⟨10, tris112, tgt112, [18, 17, 6, 1, 0], cov112⟩ <|
  .promote ⟨11, tris113, tgt113, [19, 10, 1, 0], cov113⟩ <|
  .promote ⟨13, tris114, tgt114, [19, 10, 4, 1], cov114⟩ <|
  .promote ⟨2, tris116, tgt116, [41, 20, 13, 2], cov116⟩ <|
  .promote ⟨5, tris117, tgt117, [24, 14, 12, 0], cov117⟩ <|
  .promote ⟨10, tris118, tgt118, [22, 5, 3, 2, 1], cov118⟩ <|
  .promote ⟨12, tris119, tgt119, [14, 3], cov119⟩ <|
  .promote ⟨13, tris120, tgt120, [15, 2, 1, 0], cov120⟩ <|
  .promote ⟨1, tris121, tgt121, [28, 4, 3], cov121⟩ <|
  .promote ⟨2, tris122, tgt122, [47, 26, 4, 3, 0], cov122⟩ <|
  .promote ⟨8, tris124, tgt124, [27, 7, 5, 3], cov124⟩ <|
  .promote ⟨10, tris125, tgt125, [29, 28, 11, 9, 8, 3, 1], cov125⟩ <|
  .promote ⟨11, tris126, tgt126, [30, 12, 2, 0], cov126⟩ <|
  .promote ⟨13, tris127, tgt127, [8, 6, 2, 1], cov127⟩ <|
  .promote ⟨15, tris128, tgt128, [2, 1], cov128⟩ <|
  .promote ⟨0, tris129, tgt129, [32, 10, 6, 4], cov129⟩ <|
  .promote ⟨1, tris130, tgt130, [11, 6, 0], cov130⟩ <|
  .promote ⟨2, tris131, tgt131, [55, 34, 12, 5, 0], cov131⟩ <|
  .promote ⟨5, tris132, tgt132, [7, 2, 1, 0], cov132⟩ <|
  .promote ⟨12, tris133, tgt133, [8, 5], cov133⟩ <|
  .split 0 (0) (1) (3317383274) program_rLL program_rLR

private def program_rRL : Program cs_rRL :=
  .promote ⟨11, tris244, tgt244, [19, 10, 0], cov244⟩ <|
  .promote ⟨15, tris245, tgt245, [1, 0], cov245⟩ <|
  .promote ⟨2, tris246, tgt246, [41, 20, 13, 1], cov246⟩ <|
  .promote ⟨5, tris247, tgt247, [24, 14, 12, 0], cov247⟩ <|
  .promote ⟨8, tris248, tgt248, [7, 6, 0], cov248⟩ <|
  .promote ⟨10, tris249, tgt249, [7, 4, 3, 2, 1], cov249⟩ <|
  .promote ⟨12, tris250, tgt250, [8, 1], cov250⟩ <|
  .promote ⟨13, tris251, tgt251, [3, 2, 1, 0], cov251⟩ <|
  .promote ⟨15, tris252, tgt252, [7, 2], cov252⟩ <|
  .promote ⟨0, tris253, tgt253, [20, 5, 4], cov253⟩ <|
  .promote ⟨1, tris254, tgt254, [7, 6, 0], cov254⟩ <|
  .promote ⟨2, tris255, tgt255, [50, 10, 7, 0], cov255⟩ <|
  .promote ⟨3, tris256, tgt256, [0], cov256⟩ <|
  .promote ⟨5, tris257, tgt257, [8, 3, 2, 1], cov257⟩ <|
  .promote ⟨8, tris258, tgt258, [7, 6, 0], cov258⟩ <|
  .promote ⟨10, tris259, tgt259, [14, 7, 6, 3, 1], cov259⟩ <|
  .promote ⟨11, tris260, tgt260, [4, 0], cov260⟩ <|
  .promote ⟨12, tris261, tgt261, [9, 2], cov261⟩ <|
  .promote ⟨13, tris262, tgt262, [4, 3, 2, 0], cov262⟩ <|
  .promote ⟨0, tris264, tgt264, [8, 5, 4], cov264⟩ <|
  .promote ⟨1, tris265, tgt265, [8, 6, 0], cov265⟩ <|
  .promote ⟨2, tris266, tgt266, [8, 7, 5, 4, 0], cov266⟩ <|
  .promote ⟨5, tris267, tgt267, [7, 2, 1, 0], cov267⟩ <|
  .promote ⟨8, tris268, tgt268, [5, 4, 0], cov268⟩ <|
  .promote ⟨10, tris269, tgt269, [15, 7, 5, 2, 1], cov269⟩ <|
  .promote ⟨11, tris270, tgt270, [3, 0], cov270⟩ <|
  .promote ⟨12, tris271, tgt271, [7, 2], cov271⟩ <|
  .promote ⟨13, tris272, tgt272, [4, 3, 2, 0], cov272⟩ <|
  .promote ⟨15, tris273, tgt273, [3, 2], cov273⟩ <|
  .promote ⟨0, tris274, tgt274, [8, 6, 5], cov274⟩ <|
  .promote ⟨1, tris275, tgt275, [8, 7, 0], cov275⟩ <|
  .promote ⟨2, tris276, tgt276, [18, 8, 6, 5, 0], cov276⟩ <|
  .promote ⟨5, tris277, tgt277, [8, 2, 1, 0], cov277⟩ <|
  .promote ⟨8, tris278, tgt278, [6, 5, 0], cov278⟩ <|
  .promote ⟨10, tris279, tgt279, [8, 6, 5, 2, 1], cov279⟩ <|
  .promote ⟨11, tris280, tgt280, [3, 0], cov280⟩ <|
  .promote ⟨12, tris281, tgt281, [8, 2], cov281⟩ <|
  .promote ⟨13, tris282, tgt282, [4, 3, 2, 0], cov282⟩ <|
  .promote ⟨15, tris283, tgt283, [3, 2], cov283⟩ <|
  .promote ⟨0, tris284, tgt284, [8, 6, 5], cov284⟩ <|
  .promote ⟨1, tris285, tgt285, [8, 7, 0], cov285⟩ <|
  .promote ⟨2, tris286, tgt286, [28, 8, 6, 5, 0], cov286⟩ <|
  .promote ⟨3, tris287, tgt287, [0], cov287⟩ <|
  .promote ⟨10, tris288, tgt288, [10, 7, 5, 4, 1], cov288⟩ <|
  .promote ⟨11, tris289, tgt289, [2, 0], cov289⟩ <|
  .promote ⟨12, tris290, tgt290, [11, 7], cov290⟩ <|
  .promote ⟨13, tris291, tgt291, [13, 12, 2, 0], cov291⟩ <|
  .promote ⟨0, tris293, tgt293, [14, 13, 6], cov293⟩ <|
  .promote ⟨1, tris294, tgt294, [15, 6, 0], cov294⟩ <|
  .promote ⟨2, tris295, tgt295, [16, 6, 5, 4, 0], cov295⟩ <|
  .promote ⟨3, tris296, tgt296, [0], cov296⟩ <|
  .promote ⟨5, tris297, tgt297, [17, 3, 2, 1], cov297⟩ <|
  .promote ⟨8, tris298, tgt298, [6, 5, 0], cov298⟩ <|
  .promote ⟨10, tris299, tgt299, [14, 8, 6, 3, 1], cov299⟩ <|
  .promote ⟨11, tris300, tgt300, [4, 0], cov300⟩ <|
  .promote ⟨12, tris301, tgt301, [8, 2], cov301⟩ <|
  .promote ⟨13, tris302, tgt302, [4, 3, 2, 0], cov302⟩ <|
  .promote ⟨15, tris303, tgt303, [3, 2], cov303⟩ <|
  .promote ⟨2, tris304, tgt304, [9, 7, 6, 4, 3], cov304⟩ <|
  .promote ⟨5, tris305, tgt305, [11, 10, 6, 0], cov305⟩ <|
  .promote ⟨8, tris306, tgt306, [4, 3, 0], cov306⟩ <|
  .promote ⟨10, tris307, tgt307, [6, 4, 3, 2, 1], cov307⟩ <|
  .promote ⟨11, tris308, tgt308, [3, 0], cov308⟩ <|
  .promote ⟨12, tris309, tgt309, [6, 2], cov309⟩ <|
  .promote ⟨1, tris311, tgt311, [16, 5, 4], cov311⟩ <|
  .promote ⟨10, tris313, tgt313, [8, 7, 6, 5, 2], cov313⟩ <|
  .promote ⟨11, tris314, tgt314, [7, 0], cov314⟩ <|
  .promote ⟨10, tris316, tgt316, [10, 9, 8, 7, 0], cov316⟩ <|
  .promote ⟨11, tris317, tgt317, [9, 0], cov317⟩ <|
  .promote ⟨15, tris318, tgt318, [1, 0], cov318⟩ <|
  .promote ⟨2, tris319, tgt319, [19, 10, 5, 1], cov319⟩ <|
  .promote ⟨5, tris320, tgt320, [23, 10, 6, 0], cov320⟩ <|
  .promote ⟨8, tris321, tgt321, [15, 8, 0], cov321⟩ <|
  .promote ⟨10, tris322, tgt322, [16, 4, 3, 2, 1], cov322⟩ <|
  .promote ⟨11, tris323, tgt323, [3, 0], cov323⟩ <|
  .promote ⟨12, tris324, tgt324, [18, 2], cov324⟩ <|
  .promote ⟨13, tris325, tgt325, [4, 3, 2, 0], cov325⟩ <|
  .promote ⟨15, tris326, tgt326, [3, 2], cov326⟩ <|
  .promote ⟨1, tris327, tgt327, [30, 7, 6], cov327⟩ <|
  .promote ⟨2, tris328, tgt328, [28, 7, 5, 4, 0], cov328⟩ <|
  .promote ⟨3, tris329, tgt329, [5, 0], cov329⟩ <|
  .promote ⟨5, tris330, tgt330, [33, 8, 2, 1], cov330⟩ <|
  .promote ⟨8, tris331, tgt331, [6, 5, 0], cov331⟩ <|
  .promote ⟨10, tris332, tgt332, [8, 6, 5, 3, 1], cov332⟩ <|
  .promote ⟨11, tris333, tgt333, [4, 0], cov333⟩ <|
  .promote ⟨12, tris334, tgt334, [8, 2], cov334⟩ <|
  .promote ⟨13, tris335, tgt335, [4, 3, 2, 0], cov335⟩ <|
  .promote ⟨15, tris336, tgt336, [3, 2], cov336⟩ <|
  .promote ⟨0, tris337, tgt337, [9, 6, 5], cov337⟩ <|
  .promote ⟨1, tris338, tgt338, [9, 7, 0], cov338⟩ <|
  .promote ⟨2, tris339, tgt339, [9, 8, 5, 0], cov339⟩ <|
  .promote ⟨3, tris340, tgt340, [6, 0], cov340⟩ <|
  .promote ⟨5, tris341, tgt341, [9, 3, 2, 1], cov341⟩ <|
  .promote ⟨8, tris342, tgt342, [7, 6, 0], cov342⟩ <|
  .promote ⟨10, tris343, tgt343, [9, 7, 6, 3, 1], cov343⟩ <|
  .promote ⟨11, tris344, tgt344, [4, 0], cov344⟩ <|
  .promote ⟨12, tris345, tgt345, [9, 2], cov345⟩ <|
  .promote ⟨13, tris346, tgt346, [3, 2, 0], cov346⟩ <|
  .promote ⟨15, tris347, tgt347, [3, 2], cov347⟩ <|
  .promote ⟨0, tris348, tgt348, [9, 6, 5], cov348⟩ <|
  .promote ⟨1, tris349, tgt349, [9, 7, 0], cov349⟩ <|
  .promote ⟨2, tris350, tgt350, [9, 8, 6, 5, 0], cov350⟩ <|
  .promote ⟨3, tris351, tgt351, [6, 0], cov351⟩ <|
  .promote ⟨5, tris352, tgt352, [9, 3, 2, 1], cov352⟩ <|
  .promote ⟨10, tris353, tgt353, [8, 6, 5, 2, 0], cov353⟩ <|
  .promote ⟨11, tris354, tgt354, [3, 0], cov354⟩ <|
  .promote ⟨0, tris355, tgt355, [5, 2], cov355⟩ <|
  .promote ⟨1, tris356, tgt356, [5, 3, 0], cov356⟩ <|
  .stop ⟨2, tris357, [5, 4, 3, 2, 0], cov357⟩

private def program_rRR : Program cs_rRR :=
  .promote ⟨11, tris358, tgt358, [19, 10, 1, 0], cov358⟩ <|
  .promote ⟨15, tris359, tgt359, [1, 0], cov359⟩ <|
  .stop ⟨10, tris360, [21, 20, 4, 1, 0], cov360⟩

private def program_rR : Program cs_rR :=
  .promote ⟨15, tris242, tgt242, [5, 2], cov242⟩ <|
  .promote ⟨10, tris243, tgt243, [18, 17, 6, 1, 0], cov243⟩ <|
  .split 11 (0) (1) (8781308668) program_rRL program_rRR

private def program_r : Program cs_r :=
  .promote ⟨0, tris0, tgt0, [], cov0⟩ <|
  .promote ⟨1, tris1, tgt1, [0], cov1⟩ <|
  .promote ⟨2, tris2, tgt2, [0], cov2⟩ <|
  .promote ⟨3, tris3, tgt3, [0], cov3⟩ <|
  .promote ⟨5, tris4, tgt4, [3, 2, 1], cov4⟩ <|
  .promote ⟨8, tris5, tgt5, [0], cov5⟩ <|
  .promote ⟨11, tris6, tgt6, [], cov6⟩ <|
  .promote ⟨12, tris7, tgt7, [1], cov7⟩ <|
  .promote ⟨13, tris8, tgt8, [2, 0], cov8⟩ <|
  .promote ⟨15, tris9, tgt9, [2], cov9⟩ <|
  .promote ⟨0, tris10, tgt10, [8, 5], cov10⟩ <|
  .promote ⟨1, tris11, tgt11, [8, 6, 0], cov11⟩ <|
  .promote ⟨2, tris12, tgt12, [8, 7, 0], cov12⟩ <|
  .promote ⟨3, tris13, tgt13, [0], cov13⟩ <|
  .promote ⟨5, tris14, tgt14, [8, 3, 2, 1], cov14⟩ <|
  .promote ⟨8, tris15, tgt15, [7, 6, 0], cov15⟩ <|
  .promote ⟨10, tris16, tgt16, [9, 7, 6, 3, 1], cov16⟩ <|
  .promote ⟨11, tris17, tgt17, [7, 4, 0], cov17⟩ <|
  .promote ⟨12, tris18, tgt18, [9, 2], cov18⟩ <|
  .promote ⟨13, tris19, tgt19, [4, 3, 2, 0], cov19⟩ <|
  .promote ⟨15, tris20, tgt20, [3, 2, 0], cov20⟩ <|
  .promote ⟨0, tris21, tgt21, [9, 6, 5], cov21⟩ <|
  .promote ⟨1, tris22, tgt22, [9, 7, 0], cov22⟩ <|
  .promote ⟨2, tris23, tgt23, [9, 8, 0], cov23⟩ <|
  .promote ⟨3, tris24, tgt24, [0], cov24⟩ <|
  .promote ⟨5, tris25, tgt25, [9, 3, 2, 1], cov25⟩ <|
  .promote ⟨8, tris26, tgt26, [7, 6, 0], cov26⟩ <|
  .promote ⟨10, tris27, tgt27, [9, 7, 6, 3, 1], cov27⟩ <|
  .promote ⟨11, tris28, tgt28, [7, 4, 0], cov28⟩ <|
  .promote ⟨12, tris29, tgt29, [9, 2], cov29⟩ <|
  .promote ⟨13, tris30, tgt30, [4, 3, 2, 0], cov30⟩ <|
  .promote ⟨15, tris31, tgt31, [3, 2], cov31⟩ <|
  .promote ⟨0, tris32, tgt32, [9, 6, 5], cov32⟩ <|
  .promote ⟨1, tris33, tgt33, [9, 7, 0], cov33⟩ <|
  .promote ⟨2, tris34, tgt34, [9, 8, 0], cov34⟩ <|
  .promote ⟨3, tris35, tgt35, [0], cov35⟩ <|
  .promote ⟨5, tris36, tgt36, [9, 3, 2, 1], cov36⟩ <|
  .promote ⟨8, tris37, tgt37, [7, 6, 0], cov37⟩ <|
  .promote ⟨10, tris38, tgt38, [9, 7, 6, 3, 1], cov38⟩ <|
  .promote ⟨11, tris39, tgt39, [7, 4, 0], cov39⟩ <|
  .promote ⟨12, tris40, tgt40, [9, 2], cov40⟩ <|
  .promote ⟨13, tris41, tgt41, [4, 3, 2, 0], cov41⟩ <|
  .promote ⟨15, tris42, tgt42, [3, 2], cov42⟩ <|
  .promote ⟨0, tris43, tgt43, [9, 6, 5], cov43⟩ <|
  .promote ⟨1, tris44, tgt44, [9, 7, 0], cov44⟩ <|
  .promote ⟨2, tris45, tgt45, [9, 8, 0], cov45⟩ <|
  .promote ⟨3, tris46, tgt46, [0], cov46⟩ <|
  .promote ⟨5, tris47, tgt47, [9, 3, 2, 1], cov47⟩ <|
  .promote ⟨8, tris48, tgt48, [7, 6, 0], cov48⟩ <|
  .promote ⟨10, tris49, tgt49, [9, 7, 6, 3, 1], cov49⟩ <|
  .promote ⟨11, tris50, tgt50, [7, 4, 0], cov50⟩ <|
  .promote ⟨12, tris51, tgt51, [9, 2], cov51⟩ <|
  .promote ⟨13, tris52, tgt52, [4, 3, 2, 0], cov52⟩ <|
  .promote ⟨15, tris53, tgt53, [3, 2], cov53⟩ <|
  .promote ⟨0, tris54, tgt54, [9, 6, 5], cov54⟩ <|
  .promote ⟨1, tris55, tgt55, [9, 7, 0], cov55⟩ <|
  .promote ⟨2, tris56, tgt56, [9, 8, 0], cov56⟩ <|
  .promote ⟨3, tris57, tgt57, [0], cov57⟩ <|
  .promote ⟨5, tris58, tgt58, [9, 3, 2, 1], cov58⟩ <|
  .promote ⟨8, tris59, tgt59, [7, 6, 0], cov59⟩ <|
  .promote ⟨10, tris60, tgt60, [9, 7, 6, 3, 1], cov60⟩ <|
  .promote ⟨11, tris61, tgt61, [7, 4, 0], cov61⟩ <|
  .promote ⟨12, tris62, tgt62, [9, 2], cov62⟩ <|
  .promote ⟨13, tris63, tgt63, [4, 3, 2, 0], cov63⟩ <|
  .promote ⟨15, tris64, tgt64, [3, 2], cov64⟩ <|
  .promote ⟨0, tris65, tgt65, [9, 6, 5], cov65⟩ <|
  .promote ⟨1, tris66, tgt66, [9, 7, 0], cov66⟩ <|
  .promote ⟨2, tris67, tgt67, [9, 8, 0], cov67⟩ <|
  .promote ⟨3, tris68, tgt68, [0], cov68⟩ <|
  .promote ⟨5, tris69, tgt69, [9, 3, 2, 1], cov69⟩ <|
  .promote ⟨8, tris70, tgt70, [7, 6, 0], cov70⟩ <|
  .promote ⟨10, tris71, tgt71, [9, 7, 6, 3, 1], cov71⟩ <|
  .promote ⟨11, tris72, tgt72, [7, 4, 0], cov72⟩ <|
  .promote ⟨12, tris73, tgt73, [9, 2], cov73⟩ <|
  .promote ⟨13, tris74, tgt74, [4, 3, 2, 0], cov74⟩ <|
  .promote ⟨15, tris75, tgt75, [3, 2], cov75⟩ <|
  .promote ⟨0, tris76, tgt76, [9, 6, 5], cov76⟩ <|
  .promote ⟨1, tris77, tgt77, [9, 7, 0], cov77⟩ <|
  .promote ⟨2, tris78, tgt78, [9, 8, 0], cov78⟩ <|
  .promote ⟨5, tris80, tgt80, [8, 2, 1, 0], cov80⟩ <|
  .promote ⟨8, tris81, tgt81, [6, 5, 0], cov81⟩ <|
  .promote ⟨10, tris82, tgt82, [8, 6, 5, 2, 1], cov82⟩ <|
  .promote ⟨11, tris83, tgt83, [6, 3, 0], cov83⟩ <|
  .promote ⟨12, tris84, tgt84, [8, 2], cov84⟩ <|
  .promote ⟨13, tris85, tgt85, [4, 3, 2, 0], cov85⟩ <|
  .promote ⟨15, tris86, tgt86, [3, 2], cov86⟩ <|
  .promote ⟨0, tris87, tgt87, [8, 6, 5], cov87⟩ <|
  .promote ⟨1, tris88, tgt88, [8, 7, 0], cov88⟩ <|
  .promote ⟨2, tris89, tgt89, [19, 8, 0], cov89⟩ <|
  .promote ⟨5, tris91, tgt91, [8, 2, 1, 0], cov91⟩ <|
  .promote ⟨8, tris92, tgt92, [6, 5, 0], cov92⟩ <|
  .promote ⟨10, tris93, tgt93, [8, 6, 5, 2, 1], cov93⟩ <|
  .promote ⟨11, tris94, tgt94, [6, 3, 0], cov94⟩ <|
  .promote ⟨12, tris95, tgt95, [8, 2], cov95⟩ <|
  .promote ⟨13, tris96, tgt96, [4, 3, 2, 0], cov96⟩ <|
  .promote ⟨15, tris97, tgt97, [3, 2], cov97⟩ <|
  .promote ⟨1, tris98, tgt98, [9, 7, 6], cov98⟩ <|
  .promote ⟨2, tris99, tgt99, [28, 7, 0], cov99⟩ <|
  .promote ⟨8, tris100, tgt100, [8, 4, 3], cov100⟩ <|
  .promote ⟨10, tris101, tgt101, [13, 10, 9, 6, 4], cov101⟩ <|
  .promote ⟨11, tris102, tgt102, [14, 11, 4, 2, 0], cov102⟩ <|
  .promote ⟨12, tris103, tgt103, [6, 2], cov103⟩ <|
  .promote ⟨13, tris104, tgt104, [12, 3, 2, 0], cov104⟩ <|
  .promote ⟨10, tris106, tgt106, [17, 14, 13, 2, 0], cov106⟩ <|
  .promote ⟨12, tris108, tgt108, [5, 1], cov108⟩ <|
  .promote ⟨13, tris109, tgt109, [15, 6, 1, 0], cov109⟩ <|
  .split 15 (1) (0) (13724860214) program_rL program_rR

lemma hJ : J = maskAt 655 := by decide +kernel

theorem excl_r : Excl Ux J cs_r :=
  check_sound le_rfl (by norm_num [Ux]) program_r
    (batchesOwnedC_nil Ux J cs_r) (by decide +kernel)

theorem notIn : ¬ RealizesIn Ux J := not_in_of_excl excl_r

theorem excluded : CaseExcluded (maskAt 655) := by
  rw [← hJ]
  exact caseExcluded_of_not_in notIn

end SquarePacking.S11Opt.Simplified.ReducedConditional.U2P.C655
#print axioms SquarePacking.S11Opt.Simplified.ReducedConditional.U2P.C655.excluded
