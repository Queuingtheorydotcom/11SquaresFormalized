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

/-- A strict angular cut: rows starting at or above `a` are dropped, the others are
clipped at `a`.  Used on the far side of a split, where `t < a`; poses with
`t = a` belong to the near side. -/
def cutAngleBelow (s : PoseState) (i : Owner) (a : ℚ) : PoseState :=
  replaceRows s i (((s.rows i).filter fun r => decide (r.lo < a)).map fun r => clipAngleUpper r a)

theorem cutAngleBelow_from_parameter {S : ℝ} (P : Packing 11 S) (s : PoseState) (i : Owner) (a : ℚ)
    (hs : StateHolds P s) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (ha : (P.squares i).axis = chartAxis t₀)
    (hlt : t₀ < (a : ℝ)) : StateHolds P (cutAngleBelow s i a) := by
  refine ⟨?_, hs.2⟩
  intro k
  by_cases hki : k = i
  · subst k
    obtain ⟨r, hr, hqr⟩ := hs.1 i
    obtain ⟨hc, t, ht0, ht1, hlo, hhi, hax⟩ := hqr
    have htt := chartAxis_parameter_unique ht₀ ha t ht0 ht1 hax
    subst htt
    have hlo' : r.lo < a := by exact_mod_cast lt_of_le_of_lt hlo hlt
    have hrow : RowsContain (((s.rows i).filter fun r => decide (r.lo < a)).map
        fun r => clipAngleUpper r a) (P.squares i) := by
      refine ⟨clipAngleUpper r a, List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simpa using hlo'⟩, rfl⟩, ?_⟩
      refine ⟨hc, t, ht0, ht1, hlo, ?_, hax⟩
      simp only [clipAngleUpper, Rat.cast_min]
      exact le_min hhi hlt.le
    simpa only [cutAngleBelow, replaceRows, Function.update_self] using hrow
  · simpa only [cutAngleBelow, replaceRows, Function.update_of_ne hki] using hs.1 k

theorem ext_near_of_far {P : Packing 11 coverCap} (hchart : IsCharted P) (i15 i13 i2 : Owner)
    {sR sY s13 sNear far15 far13 far2 : PoseState} (hR : StateHolds P sR)
    (hF15 : ExtTrace (cutYUpper sR i15 physicalYCut) far15) (tF15 : Terminal far15)
    (hY : ExtTrace (cutYLower sR i15 physicalYCut) sY)
    (hF13 : ExtTrace (cutAngleBelow sY i13 (147/512)) far13) (tF13 : Terminal far13)
    (h13 : ExtTrace (cutAngleLower sY i13 (147/512)) s13)
    (hF2 : ExtTrace (cutAngleBelow s13 i2 (183/512)) far2) (tF2 : Terminal far2)
    (hN : ExtTrace (cutAngleLower s13 i2 (183/512)) sNear) :
    StateHolds P sNear := by
  obtain ⟨t13, ht13₀, _, ha13⟩ := hchart i13
  obtain ⟨t2, ht2₀, _, ha2⟩ := hchart i2
  let y15 : ℝ := (P.squares i15).center.2 - coverCap / 2
  have cast147 : ((147/512 : ℚ) : ℝ) = 147/512 := by norm_num
  have cast183 : ((183/512 : ℚ) : ℝ) = 183/512 := by norm_num
  rcases le_total y15 (5/4) with h15 | hy
  · have : StateHolds P (cutYUpper sR i15 physicalYCut) := by
      apply cutYUpper_sound P sR i15 physicalYCut hR
      rw [physicalYCut_eq]; dsimp [y15] at h15; linarith
    exact (ext_terminal_refutes P this hF15 tF15).elim
  have hsY : StateHolds P sY := by
    refine ext_trace_sound P ?_ hY
    apply cutYLower_sound P sR i15 physicalYCut hR
    rw [physicalYCut_eq]; dsimp [y15] at hy; linarith
  rcases lt_or_ge t13 (147/512) with ht | ht13
  · have := cutAngleBelow_from_parameter P sY i13 (147/512) hsY t13 ht13₀ ha13
      (by rw [cast147]; exact ht)
    exact (ext_terminal_refutes P this hF13 tF13).elim
  have hs13 : StateHolds P s13 := by
    refine ext_trace_sound P ?_ h13
    exact cutAngleLower_from_parameter P sY i13 (147/512) hsY t13 ht13₀ ha13
      (by rw [cast147]; exact ht13)
  rcases lt_or_ge t2 (183/512) with ht | ht2
  · have := cutAngleBelow_from_parameter P s13 i2 (183/512) hs13 t2 ht2₀ ha2
      (by rw [cast183]; exact ht)
    exact (ext_terminal_refutes P this hF2 tF2).elim
  exact ext_trace_sound P (cutAngleLower_from_parameter P s13 i2 (183/512) hs13 t2 ht2₀ ha2
    (by rw [cast183]; exact ht2)) hN

end
end ElevenSquare.Tasks.T07
