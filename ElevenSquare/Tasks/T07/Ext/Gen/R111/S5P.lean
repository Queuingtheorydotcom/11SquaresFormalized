import ElevenSquare.Tasks.T07.Ext.Gen.R111.S5D

namespace ElevenSquare.Tasks.T07.Ext.R111.S5
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pc7_ok : pcovB prev 7 pc7 = true := by decide +kernel

theorem pc1_ok : pcovB prev 1 pc1 = true := by decide +kernel

theorem pc10_ok : pcovB prev 10 pc10 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h7 : j = 7
  · subst h7; exact pc7_ok
  by_cases h1 : j = 1
  · subst h1; exact pc1_ok
  by_cases h10 : j = 10
  · subst h10; exact pc10_ok
  simp [pcov, h7, h1, h10] at hj

end ElevenSquare.Tasks.T07.Ext.R111.S5
