import ElevenSquare.Tasks.T07.Ext.Gen.R110.S10C
import ElevenSquare.Tasks.T07.Ext.Gen.R110.S9D

namespace ElevenSquare.Tasks.T07.Ext.R110.S10
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.R110.S9.next

def mid : PoseState := replaceRows prev 2 rs

def next : PoseState := mid

end ElevenSquare.Tasks.T07.Ext.R110.S10
