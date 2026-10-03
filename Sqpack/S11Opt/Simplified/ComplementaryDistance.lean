import Sqpack.S11Opt.Simplified.ComplementaryPoints

/-! Two points at distance at most one cannot lie strictly beyond opposite
sides of a unit square. This removes the angle interval from the gap test. -/
namespace SquarePacking.S11Opt.Simplified.ComplementaryPoints
open SquarePacking BoxTree FieldTree

def distanceCheck (Q : ℕ) (p q : ℕ × ℕ) : Bool :=
  decide (((p.1 : ℤ)-q.1)^2+((p.2 : ℤ)-q.2)^2 ≤ (Q : ℤ)^2)

theorem projection_bound (a b x y r d : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hab : a^2+b^2=d^2) (hxy : x^2+y^2 ≤ r^2) : a*x+b*y ≤ r*d := by
  have hs : (a*x+b*y)^2 ≤ (r*d)^2 := by
    calc
      (a*x+b*y)^2 ≤ (a^2+b^2)*(x^2+y^2) := by
        nlinarith only [sq_nonneg (a*y-b*x)]
      _ ≤ (a^2+b^2)*r^2 := mul_le_mul_of_nonneg_left hxy (by positivity)
      _ = (r*d)^2 := by rw [hab]; ring
  nlinarith only [hs, mul_nonneg hr hd]

theorem distance_gap_sound {Q : ℕ} (hQ : 0 < Q) (p q : ℕ × ℕ)
    (h : distanceCheck Q p q = true) (k : Fin 4) (c : ℝ × ℝ) (u : ℝ) :
    gval k ((p.1 : ℝ)/Q-c.1) ((p.2 : ℝ)/Q-c.2) u +
      gval (oppositeSide k) ((q.1 : ℝ)/Q-c.1) ((q.2 : ℝ)/Q-c.2) u ≤ 0 := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hn : ((p.1 : ℝ)-q.1)^2+((p.2 : ℝ)-q.2)^2 ≤ (Q : ℝ)^2 := by
    exact_mod_cast (of_decide_eq_true h)
  have hk : (deltaX p q k)^2+(deltaY p q k)^2 ≤ (Q : ℝ)^2 := by
    fin_cases k <;> simp only [deltaX, deltaY] <;> nlinarith only [hn]
  have hg := projection_bound (1-u^2) (2*u) (deltaX p q k) (deltaY p q k)
    Q (1+u^2) hQr.le (by positivity) (by ring) hk
  have he : (Q : ℝ)*(gval k ((p.1 : ℝ)/Q-c.1) ((p.2 : ℝ)/Q-c.2) u +
      gval (oppositeSide k) ((q.1 : ℝ)/Q-c.1) ((q.2 : ℝ)/Q-c.2) u) =
      2*((1-u^2)*deltaX p q k+2*u*deltaY p q k-(1+u^2)*Q) := by
    fin_cases k <;> simp [oppositeSide, deltaX, deltaY, gval, gc, qeval] <;>
      field_simp <;> ring
  exact nonpos_of_mul_nonpos_right (by rw [he]; nlinarith only [hg]) hQr

def checkWithDistance (Q R a b : ℕ) (hs : List Plane) (pairs : List (ℕ × ℕ))
    (p q : ℕ × ℕ) (k : ℕ) : Bool :=
  check Q R a b hs pairs p q k ||
    (decide (k < 4) &&
      PolyhedralPoint.listCheck hs (partialTargets Q R a b p k) (partialPairs pairs k) &&
      PolyhedralPoint.listCheck hs (partialTargets Q R a b q (opposite k))
        (partialPairs pairs (opposite k)) && distanceCheck Q p q)

theorem soundWithDistance {Q R a b : ℕ} (hQ : 0 < Q) (hR : 0 < R) (hb : b ≤ R)
    {hs : List Plane} {pairs : List (ℕ × ℕ)} {p q : ℕ × ℕ} {k : ℕ}
    (h : checkWithDistance Q R a b hs pairs p q k = true) (c : ℝ × ℝ) (u : ℝ)
    (hhs : ∀ z ∈ hs, InHP Q z c)
    (hu0 : (a : ℝ)/R ≤ u) (hu1 : u ≤ (b : ℝ)/R) :
    ((p.1 : ℝ)/Q, (p.2 : ℝ)/Q) ∈ sq c (2*Real.arctan u) 1 ∨
      ((q.1 : ℝ)/Q, (q.2 : ℝ)/Q) ∈ sq c (2*Real.arctan u) 1 := by
  simp only [checkWithDistance, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact sound hQ hR hb h c u hhs hu0 hu1
  let side : Fin 4 := ⟨k, h.1.1.1⟩
  have hp := partial_sound hQ hR hb p c u hu0 hu1
    (PolyhedralPoint.listCheck_sound hs _ _ h.1.1.2 c hhs)
  have hq := partial_sound hQ hR hb q c u hu0 hu1
    (PolyhedralPoint.listCheck_sound hs _ _ h.1.2 c hhs)
  have hsum := distance_gap_sound hQ p q h.2 side c u
  by_cases hside : gval side ((p.1 : ℝ)/Q-c.1) ((p.2 : ℝ)/Q-c.2) u ≤ 0
  · left
    rw [mem_sq_iff_gval]
    intro j
    by_cases hj : j = side
    · simpa [hj] using hside
    · apply hp j
      intro e
      apply hj
      exact Fin.ext e
  · right
    rw [mem_sq_iff_gval]
    intro j
    by_cases hj : j = oppositeSide side
    · subst j
      linarith only [hsum, hside]
    · apply hq j
      intro e
      apply hj
      apply Fin.ext
      simpa [side] using e

#print axioms distance_gap_sound
#print axioms soundWithDistance
end SquarePacking.S11Opt.Simplified.ComplementaryPoints
