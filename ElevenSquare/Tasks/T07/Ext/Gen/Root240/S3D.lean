import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S3C
import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S2D

namespace ElevenSquare.Tasks.T07.Ext.Root240.S3
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.Root240.S2.next

def mid : PoseState := replaceRows prev 10 rs

def next : PoseState := replaceHull mid 10 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.Root240.S3
