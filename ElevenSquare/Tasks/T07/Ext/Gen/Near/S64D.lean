import ElevenSquare.Tasks.T07.Ext.Gen.Near.S64C
import ElevenSquare.Tasks.T07.Ext.Gen.Near.S63D

namespace ElevenSquare.Tasks.T07.Ext.Near.S64
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Near.S63.next

def mid : PoseState := replaceRows prev 3 rs

def next : PoseState := replaceHull mid 3 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.Near.S64
