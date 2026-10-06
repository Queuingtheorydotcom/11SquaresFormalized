import ElevenSquare.Tasks.T07.Ext.Gen.Near13.S18C
import ElevenSquare.Tasks.T07.Ext.Gen.Near13.S17D

namespace ElevenSquare.Tasks.T07.Ext.Near13.S18
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Near13.S17.next

def mid : PoseState := replaceRows prev 7 rs

def next : PoseState := replaceHull mid 7 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.Near13.S18
