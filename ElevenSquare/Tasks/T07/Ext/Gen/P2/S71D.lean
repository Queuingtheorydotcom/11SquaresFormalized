import ElevenSquare.Tasks.T07.Ext.Gen.P2.S71C
import ElevenSquare.Tasks.T07.Ext.Gen.P2.S70D

namespace ElevenSquare.Tasks.T07.Ext.P2.S71
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.P2.S70.next

def mid : PoseState := replaceRows prev 2 rs

def next : PoseState := replaceHull mid 2 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.P2.S71
