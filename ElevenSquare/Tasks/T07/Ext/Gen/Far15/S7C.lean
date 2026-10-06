import ElevenSquare.Tasks.T07.Ext.Promote

namespace ElevenSquare.Tasks.T07.Ext.Far15.S7
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rs : List PoseRow := []

def pcov (j : ℕ) : List (List PartnerPiece) := []

end ElevenSquare.Tasks.T07.Ext.Far15.S7
