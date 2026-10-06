import ElevenSquare.Tasks.T07.Ext.Promote
import ElevenSquare.Tasks.T07.Ext.Gen.R11.S5D

namespace ElevenSquare.Tasks.T07.Ext.R11.S6
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.R11.S5.next

def next : PoseState := prev

end ElevenSquare.Tasks.T07.Ext.R11.S6
