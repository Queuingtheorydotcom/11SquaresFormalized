import ElevenSquare.Tasks.T07.Ext.Gen.P2.S99C
import ElevenSquare.Tasks.T07.Ext.Gen.P2.S98D

namespace ElevenSquare.Tasks.T07.Ext.P2.S99
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.P2.S98.next

def mid : PoseState := replaceRows prev 3 rs

def next : PoseState := replaceHull mid 3 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.P2.S99
