import ElevenSquare.Tasks.T07.Ext.Gen.Near.S113D

namespace ElevenSquare.Tasks.T07.Ext.Near.S113
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pc9_ok : pcovB prev 9 pc9 = true := by decide +kernel

theorem pc6_ok : pcovB prev 6 pc6 = true := by decide +kernel

theorem pc10_ok : pcovB prev 10 pc10 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h9 : j = 9
  · subst h9; exact pc9_ok
  by_cases h6 : j = 6
  · subst h6; exact pc6_ok
  by_cases h10 : j = 10
  · subst h10; exact pc10_ok
  simp [pcov, h9, h6, h10] at hj

end ElevenSquare.Tasks.T07.Ext.Near.S113
