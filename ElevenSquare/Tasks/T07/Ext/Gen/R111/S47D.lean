import ElevenSquare.Tasks.T07.Ext.Promote
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S46D

namespace ElevenSquare.Tasks.T07.Ext.R111.S47
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.R111.S46.next

def next : PoseState := prev

end ElevenSquare.Tasks.T07.Ext.R111.S47
