import ElevenSquare.Tasks.T07.Ext.Trace
import ElevenSquare.Tasks.T07.CaptureBranches

/-! The case-438 branch composition for extended traces.

The archived capture runs one root trace and then splits at the closed cuts
`y₁₅ ≤ 5/4`, `t₁₃ ≤ 147/512` and `t₂ ≤ 183/512` (`capture_closed_partition`),
continuing with a trace after every cut.  If the three far branches end in
terminal states, every charted packing in the `coverCap` container satisfies the
final near state.  This is `near_of_far_terminal_traces` for `ExtTrace`, from an
arbitrary root state and with traces between the cuts. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem ext_near_of_far {P : Packing 11 coverCap} (hchart : IsCharted P) (i15 i13 i2 : Owner)
    {sR sY s13 sNear far15 far13 far2 : PoseState} (hR : StateHolds P sR)
    (hF15 : ExtTrace (cutYUpper sR i15 physicalYCut) far15) (tF15 : Terminal far15)
    (hY : ExtTrace (cutYLower sR i15 physicalYCut) sY)
    (hF13 : ExtTrace (cutAngleUpper sY i13 (147/512)) far13) (tF13 : Terminal far13)
    (h13 : ExtTrace (cutAngleLower sY i13 (147/512)) s13)
    (hF2 : ExtTrace (cutAngleUpper s13 i2 (183/512)) far2) (tF2 : Terminal far2)
    (hN : ExtTrace (cutAngleLower s13 i2 (183/512)) sNear) :
    StateHolds P sNear := by
  obtain ⟨t13, ht13₀, _, ha13⟩ := hchart i13
  obtain ⟨t2, ht2₀, _, ha2⟩ := hchart i2
  let y15 : ℝ := (P.squares i15).center.2 - coverCap / 2
  have cast147 : ((147/512 : ℚ) : ℝ) = 147/512 := by norm_num
  have cast183 : ((183/512 : ℚ) : ℝ) = 183/512 := by norm_num
  have yupper (h : y15 ≤ 5/4) : StateHolds P (cutYUpper sR i15 physicalYCut) := by
    apply cutYUpper_sound P sR i15 physicalYCut hR
    rw [physicalYCut_eq]; dsimp [y15] at h; linarith
  have ylower (h : 5/4 ≤ y15) : StateHolds P (cutYLower sR i15 physicalYCut) := by
    apply cutYLower_sound P sR i15 physicalYCut hR
    rw [physicalYCut_eq]; dsimp [y15] at h; linarith
  rcases capture_closed_partition y15 t13 t2 with h15 | ⟨hy, ht⟩ | ⟨hy, ht13, ht2⟩ | ⟨hy, ht13, ht2⟩
  · exact (ext_terminal_refutes P (yupper h15) hF15 tF15).elim
  · have hsY := ext_trace_sound P (ylower hy) hY
    have := cutAngleUpper_from_parameter P sY i13 (147/512) hsY t13 ht13₀ ha13
      (by simpa only [cast147] using ht)
    exact (ext_terminal_refutes P this hF13 tF13).elim
  · have hsY := ext_trace_sound P (ylower hy) hY
    have h1 := cutAngleLower_from_parameter P sY i13 (147/512) hsY t13 ht13₀ ha13
      (by simpa only [cast147] using ht13)
    have hs13 := ext_trace_sound P h1 h13
    have := cutAngleUpper_from_parameter P s13 i2 (183/512) hs13 t2 ht2₀ ha2
      (by simpa only [cast183] using ht2)
    exact (ext_terminal_refutes P this hF2 tF2).elim
  · have hsY := ext_trace_sound P (ylower hy) hY
    have h1 := cutAngleLower_from_parameter P sY i13 (147/512) hsY t13 ht13₀ ha13
      (by simpa only [cast147] using ht13)
    have hs13 := ext_trace_sound P h1 h13
    have h2 := cutAngleLower_from_parameter P s13 i2 (183/512) hs13 t2 ht2₀ ha2
      (by simpa only [cast183] using ht2)
    exact ext_trace_sound P h2 hN

end
end ElevenSquare.Tasks.T07
