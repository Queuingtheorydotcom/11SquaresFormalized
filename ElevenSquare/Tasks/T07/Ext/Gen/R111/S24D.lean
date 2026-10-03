import ElevenSquare.Tasks.T07.Ext.Gen.R111.S24C
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S23D

namespace ElevenSquare.Tasks.T07.Ext.R111.S24
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.R111.S23.next

def mid : PoseState := replaceRows prev 0 rs

def next : PoseState := replaceHull mid 0 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.R111.S24
