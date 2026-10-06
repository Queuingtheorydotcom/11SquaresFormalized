import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S23C
import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S22D

namespace ElevenSquare.Tasks.T07.Ext.Far13.S23
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Far13.S22.next

def mid : PoseState := replaceRows prev 9 rs

def next : PoseState := mid

end ElevenSquare.Tasks.T07.Ext.Far13.S23
