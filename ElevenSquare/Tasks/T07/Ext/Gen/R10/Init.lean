import ElevenSquare.Tasks.T07.Ext.Gen.R1.S8D
import ElevenSquare.Tasks.T07.Ext.Compose

namespace ElevenSquare.Tasks.T07.Ext.R10
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def st0 : PoseState := cutAngleBelow ElevenSquare.Tasks.T07.Ext.R1.S8.next 10 (147/512)

end ElevenSquare.Tasks.T07.Ext.R10
