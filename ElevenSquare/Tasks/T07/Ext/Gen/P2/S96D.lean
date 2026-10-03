import ElevenSquare.Tasks.T07.Ext.Gen.P2.S96C
import ElevenSquare.Tasks.T07.Ext.Gen.P2.S95D

namespace ElevenSquare.Tasks.T07.Ext.P2.S96
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.P2.S95.next

def mid : PoseState := replaceRows prev 7 rs

def next : PoseState := replaceHull mid 7 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.P2.S96
