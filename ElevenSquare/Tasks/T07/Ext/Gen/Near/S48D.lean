import ElevenSquare.Tasks.T07.Ext.Gen.Near.S48C
import ElevenSquare.Tasks.T07.Ext.Gen.Near.S47D

namespace ElevenSquare.Tasks.T07.Ext.Near.S48
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Near.S47.next

def mid : PoseState := replaceRows prev 1 rs

def next : PoseState := replaceHull mid 1 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.Near.S48
