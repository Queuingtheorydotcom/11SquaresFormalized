import Sqpack.S11Opt.FieldTree

/-! A closed-interval quartic certificate. All five Bernstein coefficients are
multiplied by twelve, so the finite checker uses rational ring arithmetic
without divisions by the binomial coefficients. -/
namespace SquarePacking.S11Opt.Simplified.QuarticBernstein

structure Poly where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  c3 : ℚ
  c4 : ℚ
  deriving Inhabited, DecidableEq

def eval (p : Poly) (t : ℝ) : ℝ :=
  p.c0 + p.c1*t + p.c2*t^2 + p.c3*t^3 + p.c4*t^4

def shift (p : Poly) (a b : ℚ) : Poly :=
  ⟨p.c0+p.c1*a+p.c2*a^2+p.c3*a^3+p.c4*a^4,
   (b-a)*(p.c1+2*p.c2*a+3*p.c3*a^2+4*p.c4*a^3),
   (b-a)^2*(p.c2+3*p.c3*a+6*p.c4*a^2),
   (b-a)^3*(p.c3+4*p.c4*a), (b-a)^4*p.c4⟩

def coefficients (p : Poly) (a b : ℚ) : Poly :=
  let q := shift p a b
  ⟨12*q.c0, 12*q.c0+3*q.c1, 12*q.c0+6*q.c1+2*q.c2,
   12*q.c0+9*q.c1+6*q.c2+3*q.c3,
   12*(q.c0+q.c1+q.c2+q.c3+q.c4)⟩

def check (p : Poly) (a b : ℚ) : Bool :=
  let v := coefficients p a b
  decide (0≤v.c0 ∧ 0≤v.c1 ∧ 0≤v.c2 ∧ 0≤v.c3 ∧ 0≤v.c4)

theorem check_sound (p : Poly) (a b : ℚ) (h : check p a b = true)
    (t : ℝ) (ha : (a : ℝ) ≤ t) (hb : t ≤ b) : 0 ≤ eval p t := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := of_decide_eq_true h
  have hv0 : (0 : ℝ) ≤ ((coefficients p a b).c0 : ℝ) := by exact_mod_cast h0
  have hv1 : (0 : ℝ) ≤ ((coefficients p a b).c1 : ℝ) := by exact_mod_cast h1
  have hv2 : (0 : ℝ) ≤ ((coefficients p a b).c2 : ℝ) := by exact_mod_cast h2
  have hv3 : (0 : ℝ) ≤ ((coefficients p a b).c3 : ℝ) := by exact_mod_cast h3
  have hv4 : (0 : ℝ) ≤ ((coefficients p a b).c4 : ℝ) := by exact_mod_cast h4
  by_cases hab : a = b
  · subst b
    have ht : t = (a : ℝ) := le_antisymm hb ha
    subst t
    simp only [coefficients, shift] at hv0
    push_cast at hv0
    dsimp only [eval]
    linarith
  · have hd : (0 : ℝ) < (b : ℝ)-a := by
      have hle := ha.trans hb
      have hne : (a : ℝ) ≠ (b : ℝ) := by exact_mod_cast hab
      exact sub_pos.mpr (lt_of_le_of_ne hle hne)
    have hx : 0 ≤ t-(a : ℝ) := sub_nonneg.mpr ha
    have hy : 0 ≤ (b : ℝ)-t := sub_nonneg.mpr hb
    have identity : 12*((b : ℝ)-a)^4*eval p t =
        ((coefficients p a b).c0 : ℝ)*((b : ℝ)-t)^4 +
        4*((coefficients p a b).c1 : ℝ)*(t-a)*((b : ℝ)-t)^3 +
        6*((coefficients p a b).c2 : ℝ)*(t-a)^2*((b : ℝ)-t)^2 +
        4*((coefficients p a b).c3 : ℝ)*(t-a)^3*((b : ℝ)-t) +
        ((coefficients p a b).c4 : ℝ)*(t-a)^4 := by
      simp only [eval, coefficients, shift]
      push_cast
      ring
    have rhs : 0 ≤
        ((coefficients p a b).c0 : ℝ)*((b : ℝ)-t)^4 +
        4*((coefficients p a b).c1 : ℝ)*(t-a)*((b : ℝ)-t)^3 +
        6*((coefficients p a b).c2 : ℝ)*(t-a)^2*((b : ℝ)-t)^2 +
        4*((coefficients p a b).c3 : ℝ)*(t-a)^3*((b : ℝ)-t) +
        ((coefficients p a b).c4 : ℝ)*(t-a)^4 := by positivity
    have hp : 0 < 12*((b : ℝ)-a)^4 := by positivity
    by_contra hn
    have hn' : eval p t < 0 := lt_of_not_ge hn
    have hm := mul_neg_of_pos_of_neg hp hn'
    linarith

#print axioms check_sound
end SquarePacking.S11Opt.Simplified.QuarticBernstein
