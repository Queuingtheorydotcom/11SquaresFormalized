import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S8D

namespace ElevenSquare.Tasks.T07.Ext.Far13.S8
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pc2_ok : pcovB prev 2 pc2 = true := by decide +kernel

theorem pc3_ok : pcovB prev 3 pc3 = true := by decide +kernel

theorem pc8_ok : pcovB prev 8 pc8 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h2 : j = 2
  · subst h2; exact pc2_ok
  by_cases h3 : j = 3
  · subst h3; exact pc3_ok
  by_cases h8 : j = 8
  · subst h8; exact pc8_ok
  simp [pcov, h2, h3, h8] at hj

end ElevenSquare.Tasks.T07.Ext.Far13.S8
