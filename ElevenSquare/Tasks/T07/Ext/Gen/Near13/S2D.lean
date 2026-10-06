import ElevenSquare.Tasks.T07.Ext.Gen.Near13.S2C
import ElevenSquare.Tasks.T07.Ext.Gen.Near13.S1D

namespace ElevenSquare.Tasks.T07.Ext.Near13.S2
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Near13.S1.next

def mid : PoseState := replaceRows prev 9 rs

def next : PoseState := replaceHull mid 9 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.Near13.S2
