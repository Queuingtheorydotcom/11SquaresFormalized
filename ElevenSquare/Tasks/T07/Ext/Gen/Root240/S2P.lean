import ElevenSquare.Tasks.T07.Ext.Gen.Root240.S2D

namespace ElevenSquare.Tasks.T07.Ext.Root240.S2
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pc9_ok : pcovB prev 9 pc9 = true := by decide +kernel

theorem pc6_ok : pcovB prev 6 pc6 = true := by decide +kernel

theorem pc1_ok : pcovB prev 1 pc1 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h9 : j = 9
  · subst h9; exact pc9_ok
  by_cases h6 : j = 6
  · subst h6; exact pc6_ok
  by_cases h1 : j = 1
  · subst h1; exact pc1_ok
  simp [pcov, h9, h6, h1] at hj

end ElevenSquare.Tasks.T07.Ext.Root240.S2
