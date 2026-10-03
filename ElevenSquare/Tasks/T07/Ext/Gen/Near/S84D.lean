import ElevenSquare.Tasks.T07.Ext.Gen.Near.S84C
import ElevenSquare.Tasks.T07.Ext.Gen.Near.S83D

namespace ElevenSquare.Tasks.T07.Ext.Near.S84
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Near.S83.next

def mid : PoseState := replaceRows prev 7 rs

def next : PoseState := replaceHull mid 7 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.Near.S84
