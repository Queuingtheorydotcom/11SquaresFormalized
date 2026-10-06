import ElevenSquare.Tasks.T07.Ext.Gen.Near.S110C
import ElevenSquare.Tasks.T07.Ext.Gen.Near.S109D

namespace ElevenSquare.Tasks.T07.Ext.Near.S110
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Near.S109.next

def mid : PoseState := replaceRows prev 10 rs

def next : PoseState := replaceHull mid 10 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.Near.S110
