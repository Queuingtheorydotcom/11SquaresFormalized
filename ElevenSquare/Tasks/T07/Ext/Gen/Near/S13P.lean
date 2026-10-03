import ElevenSquare.Tasks.T07.Ext.Gen.Near.S13D

namespace ElevenSquare.Tasks.T07.Ext.Near.S13
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pc8_ok : pcovB prev 8 pc8 = true := by decide +kernel

theorem pc10_ok : pcovB prev 10 pc10 = true := by decide +kernel

theorem pc6_ok : pcovB prev 6 pc6 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h8 : j = 8
  · subst h8; exact pc8_ok
  by_cases h10 : j = 10
  · subst h10; exact pc10_ok
  by_cases h6 : j = 6
  · subst h6; exact pc6_ok
  simp [pcov, h8, h10, h6] at hj

end ElevenSquare.Tasks.T07.Ext.Near.S13
