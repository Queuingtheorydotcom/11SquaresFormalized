import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S13D
import ElevenSquare.Tasks.T07.Ext.Compose

namespace ElevenSquare.Tasks.T07.Ext.R1
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def st0 : PoseState := cutYLower ElevenSquare.Tasks.T07.Ext.Root240.S13.next 1 physicalYCut

end ElevenSquare.Tasks.T07.Ext.R1
