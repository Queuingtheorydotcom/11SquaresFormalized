import ElevenSquare.Tasks.T07.Ext.Gen.R11.S4C
import ElevenSquare.Tasks.T07.Ext.Gen.R11.S3D

namespace ElevenSquare.Tasks.T07.Ext.R11.S4
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.R11.S3.next

def mid : PoseState := replaceRows prev 1 rs

def next : PoseState := replaceHull mid 1 (combs.map Comb.v)

end ElevenSquare.Tasks.T07.Ext.R11.S4
