import ElevenSquare.Tasks.T07.Ext.Gen.Near.S14C
import ElevenSquare.Tasks.T07.Ext.Gen.Near.S13D

namespace ElevenSquare.Tasks.T07.Ext.Near.S14
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Near.S13.next

def mid : PoseState := replaceRows prev 8 rs

def next : PoseState := replaceHull mid 8 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.Near.S14
