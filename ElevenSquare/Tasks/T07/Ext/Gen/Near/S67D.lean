import ElevenSquare.Tasks.T07.Ext.Gen.Near.S67C
import ElevenSquare.Tasks.T07.Ext.Gen.Near.S66D

namespace ElevenSquare.Tasks.T07.Ext.Near.S67
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Near.S66.next

def mid : PoseState := replaceRows prev 2 rs

def next : PoseState := replaceHull mid 2 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.Near.S67
