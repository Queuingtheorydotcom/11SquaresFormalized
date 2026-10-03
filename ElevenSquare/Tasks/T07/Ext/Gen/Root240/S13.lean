import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S13D

namespace ElevenSquare.Tasks.T07.Ext.Root240.S13
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem trace : ExtTrace prev next := ExtTrace.refl _

end ElevenSquare.Tasks.T07.Ext.Root240.S13
