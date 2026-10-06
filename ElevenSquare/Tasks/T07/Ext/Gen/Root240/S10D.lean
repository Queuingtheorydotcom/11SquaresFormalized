import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S10C
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S9D

namespace ElevenSquare.Tasks.T07.Ext.Root240.S10
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Root240.S9.next

def mid : PoseState := replaceRows prev 3 rs

def next : PoseState := replaceHull mid 3 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.Root240.S10
