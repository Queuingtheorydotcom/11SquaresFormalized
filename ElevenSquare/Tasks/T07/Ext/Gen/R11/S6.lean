import ElevenSquare.Tasks.T07.Ext.Gen.R11.S6D

namespace ElevenSquare.Tasks.T07.Ext.R11.S6
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem trace : ExtTrace prev next := ExtTrace.refl _

end ElevenSquare.Tasks.T07.Ext.R11.S6
