import ElevenSquare.Tasks.T07.Ext.Gen.Far15.S7C
import ElevenSquare.Tasks.T07.Ext.Gen.Far15.S6D

namespace ElevenSquare.Tasks.T07.Ext.Far15.S7
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Far15.S6.next

def mid : PoseState := replaceRows prev 2 rs

def next : PoseState := mid

end ElevenSquare.Tasks.T07.Ext.Far15.S7
