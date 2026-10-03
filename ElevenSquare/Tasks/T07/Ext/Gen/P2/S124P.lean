import ElevenSquare.Tasks.T07.Ext.Gen.P2.S124D

namespace ElevenSquare.Tasks.T07.Ext.P2.S124
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  simp [pcov] at hj

end ElevenSquare.Tasks.T07.Ext.P2.S124
