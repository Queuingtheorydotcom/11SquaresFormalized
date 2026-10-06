import ElevenSquare.Pending.S07_GridChecks

namespace ElevenSquare.Pending.GridDistance

-- Only natural-number multiplication/comparison is evaluated per literal vertex.
def fractionCheck (nx dx ny dy gx gy : ℕ) : Bool :=
  decide (0 < dx ∧ 0 < dy ∧
    gx*dx ≤ scale*nx ∧ scale*nx ≤ (gx+1)*dx ∧
    gy*dy ≤ scale*ny ∧ scale*ny ≤ (gy+1)*dy)

theorem fractionCheck_sound (nx dx ny dy gx gy : ℕ)
    (h : fractionCheck nx dx ny dy gx gy = true) :
    pointCheck ((nx/dx : ℚ), (ny/dy : ℚ)) ((gx : ℤ), (gy : ℤ)) = true := by
  have hn := of_decide_eq_true h
  have hdx : (0 : ℚ) < dx := by exact_mod_cast hn.1
  have hdy : (0 : ℚ) < dy := by exact_mod_cast hn.2.1
  rw [pointCheck, decide_eq_true_eq]
  simp only [Prod.fst, Prod.snd, Int.cast_natCast]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← mul_div_assoc, le_div_iff₀ hdx]
    exact_mod_cast hn.2.2.1
  · rw [← mul_div_assoc, div_le_iff₀ hdx]
    exact_mod_cast hn.2.2.2.1
  · rw [← mul_div_assoc, le_div_iff₀ hdy]
    exact_mod_cast hn.2.2.2.2.1
  · rw [← mul_div_assoc, div_le_iff₀ hdy]
    exact_mod_cast hn.2.2.2.2.2

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.fractionCheck_sound
