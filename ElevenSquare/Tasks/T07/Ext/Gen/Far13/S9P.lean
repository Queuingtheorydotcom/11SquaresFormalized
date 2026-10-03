import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S9D

namespace ElevenSquare.Tasks.T07.Ext.Far13.S9
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pc3_ok : pcovB prev 3 pc3 = true := by decide +kernel

theorem pc6_ok : pcovB prev 6 pc6 = true := by decide +kernel

theorem pc4_ok : pcovB prev 4 pc4 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h3 : j = 3
  · subst h3; exact pc3_ok
  by_cases h6 : j = 6
  · subst h6; exact pc6_ok
  by_cases h4 : j = 4
  · subst h4; exact pc4_ok
  simp [pcov, h3, h6, h4] at hj

end ElevenSquare.Tasks.T07.Ext.Far13.S9
