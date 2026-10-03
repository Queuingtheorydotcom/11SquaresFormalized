import ElevenSquare.Tasks.T07.Ext.Gen.R111.S1D

namespace ElevenSquare.Tasks.T07.Ext.R111.S1
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pc6_ok : pcovB prev 6 pc6 = true := by decide +kernel

theorem pc9_ok : pcovB prev 9 pc9 = true := by decide +kernel

theorem pc0_ok : pcovB prev 0 pc0 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h6 : j = 6
  · subst h6; exact pc6_ok
  by_cases h9 : j = 9
  · subst h9; exact pc9_ok
  by_cases h0 : j = 0
  · subst h0; exact pc0_ok
  simp [pcov, h6, h9, h0] at hj

end ElevenSquare.Tasks.T07.Ext.R111.S1
