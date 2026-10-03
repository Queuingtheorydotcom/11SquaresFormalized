import ElevenSquare.Tasks.T07.Ext.Gen.R111.S13D

namespace ElevenSquare.Tasks.T07.Ext.R111.S13
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pc6_ok : pcovB prev 6 pc6 = true := by decide +kernel

theorem pc7_ok : pcovB prev 7 pc7 = true := by decide +kernel

theorem pc5_ok : pcovB prev 5 pc5 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h6 : j = 6
  · subst h6; exact pc6_ok
  by_cases h7 : j = 7
  · subst h7; exact pc7_ok
  by_cases h5 : j = 5
  · subst h5; exact pc5_ok
  simp [pcov, h6, h7, h5] at hj

end ElevenSquare.Tasks.T07.Ext.R111.S13
