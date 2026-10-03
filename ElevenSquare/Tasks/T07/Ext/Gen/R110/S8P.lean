import ElevenSquare.Tasks.T07.Ext.Gen.R110.S8D

namespace ElevenSquare.Tasks.T07.Ext.R110.S8
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pc9_ok : pcovB prev 9 pc9 = true := by decide +kernel

theorem pc7_ok : pcovB prev 7 pc7 = true := by decide +kernel

theorem pc10_ok : pcovB prev 10 pc10 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h9 : j = 9
  · subst h9; exact pc9_ok
  by_cases h7 : j = 7
  · subst h7; exact pc7_ok
  by_cases h10 : j = 10
  · subst h10; exact pc10_ok
  simp [pcov, h9, h7, h10] at hj

end ElevenSquare.Tasks.T07.Ext.R110.S8
