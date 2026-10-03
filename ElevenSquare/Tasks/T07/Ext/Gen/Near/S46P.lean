import ElevenSquare.Tasks.T07.Ext.Gen.Near.S46D

namespace ElevenSquare.Tasks.T07.Ext.Near.S46
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pc10_ok : pcovB prev 10 pc10 = true := by decide +kernel

theorem pc7_ok : pcovB prev 7 pc7 = true := by decide +kernel

theorem pc8_ok : pcovB prev 8 pc8 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h10 : j = 10
  · subst h10; exact pc10_ok
  by_cases h7 : j = 7
  · subst h7; exact pc7_ok
  by_cases h8 : j = 8
  · subst h8; exact pc8_ok
  simp [pcov, h10, h7, h8] at hj

end ElevenSquare.Tasks.T07.Ext.Near.S46
