import ElevenSquare.ConstructionData
import ElevenSquare.Tasks.T07.NearFinalPacket
import ElevenSquare.Tasks.T07.CoordinateBridge
import ElevenSquare.Tasks.T07.LocalRadii
import ElevenSquare.Tasks.T07.LocalPolynomial

/-! Exact, slightly widened rational isolation of the algebraic witness centers.
The root bounds are a direct consequence of `Endpoint.u_bounds`. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare ElevenSquare.Pending
noncomputable section

def nearRootLo : ℝ := 36576930760467729338 / 100000000000000000000
def nearRootHi : ℝ := 36576930760467729339 / 100000000000000000000

theorem near_root_bounds : nearRootLo ≤ u ∧ u ≤ nearRootHi := by
  have h := u_bounds
  constructor
  · have hrat : nearRootLo ≤ rootLo := by norm_num [nearRootLo, rootLo]
    exact hrat.trans h.1.le
  · have hrat : rootHi ≤ nearRootHi := by norm_num [nearRootHi, rootHi]
    exact h.2.le.trans hrat

theorem near_power_bounds (k : ℕ) : nearRootLo^k ≤ u^k ∧ u^k ≤ nearRootHi^k := by
  have h := near_root_bounds
  exact ⟨pow_le_pow_left₀ (by norm_num [nearRootLo]) h.1 k,
    pow_le_pow_left₀ (by linarith [show 0 ≤ u from le_trans (by norm_num [nearRootLo]) h.1]) h.2 k⟩

private def center00Coeffs : Fin 8 → ℚ :=
  ![-3/4, -37/16, 5/2, -35/16, -4, -15/16, 15/4, -25/16]

private theorem center00_eq_poly :
    (constructionCenter 0).1 - T/2 = polynomialAt center00Coeffs u := by
  rw [← constructionSide_eq_T]
  simp [constructionCenter, constructionSide, polynomialAt, center00Coeffs,
    Fin.sum_univ_succ]
  ring

private theorem center00_bounds :
    (-1438541795011408 : ℝ)/1000000000000000 ≤ (constructionCenter 0).1 - T/2 ∧
      (constructionCenter 0).1 - T/2 ≤ (-1438541795011406 : ℝ)/1000000000000000 := by
  have hp := polynomial_interval center00Coeffs
    (by norm_num [nearRootLo]) near_root_bounds.1 near_root_bounds.2
  have hl : (-1438541795011408 : ℝ)/1000000000000000 ≤
      polynomialLower center00Coeffs nearRootLo nearRootHi := by
    norm_num [polynomialLower, center00Coeffs, nearRootLo, nearRootHi,
      Fin.sum_univ_succ]
  have hh : polynomialUpper center00Coeffs nearRootLo nearRootHi ≤
      (-1438541795011406 : ℝ)/1000000000000000 := by
    norm_num [polynomialUpper, center00Coeffs, nearRootLo, nearRootHi,
      Fin.sum_univ_succ]
  rw [center00_eq_poly]
  exact ⟨hl.trans hp.1, hp.2.trans hh⟩

end
end ElevenSquare.Tasks.T07
