import ElevenSquare.Tasks.T07.Ext.Gen.R111.S11D

namespace ElevenSquare.Tasks.T07.Ext.R111.S11
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pc5_ok : pcovB prev 5 pc5 = true := by decide +kernel

theorem pc0_ok : pcovB prev 0 pc0 = true := by decide +kernel

theorem pc7_ok : pcovB prev 7 pc7 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h5 : j = 5
  · subst h5; exact pc5_ok
  by_cases h0 : j = 0
  · subst h0; exact pc0_ok
  by_cases h7 : j = 7
  · subst h7; exact pc7_ok
  simp [pcov, h5, h0, h7] at hj

end ElevenSquare.Tasks.T07.Ext.R111.S11
