import ElevenSquare.Tasks.T07.Ext.Gen.R111.S29C
import ElevenSquare.Tasks.T07.Ext.Gen.R111.S28D

namespace ElevenSquare.Tasks.T07.Ext.R111.S29
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.R111.S28.next

def mid : PoseState := replaceRows prev 3 rs

def next : PoseState := replaceHull mid 3 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.R111.S29
