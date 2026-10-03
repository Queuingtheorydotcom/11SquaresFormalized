import ElevenSquare.Tasks.T07.Ext.Gen.Near.S27C
import ElevenSquare.Tasks.T07.Ext.Gen.Near.S26D

namespace ElevenSquare.Tasks.T07.Ext.Near.S27
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Near.S26.next

def mid : PoseState := replaceRows prev 4 rs

def next : PoseState := replaceHull mid 4 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.Near.S27
