import ElevenSquare.Tasks.T07.Ext.Gen.Far13.S3D

namespace ElevenSquare.Tasks.T07.Ext.Far13.S3
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pc2_ok : pcovB prev 2 pc2 = true := by decide +kernel

theorem pc8_ok : pcovB prev 8 pc8 = true := by decide +kernel

theorem pc9_ok : pcovB prev 9 pc9 = true := by decide +kernel

theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by
  intro j hj
  by_cases h2 : j = 2
  · subst h2; exact pc2_ok
  by_cases h8 : j = 8
  · subst h8; exact pc8_ok
  by_cases h9 : j = 9
  · subst h9; exact pc9_ok
  simp [pcov, h2, h8, h9] at hj

end ElevenSquare.Tasks.T07.Ext.Far13.S3
