import ElevenSquare.Pending.Types
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ElevenSquare.Pending.T03

/-- Integer arithmetic certificates avoid repeated rational normalization. -/
structure IntegerPlane where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq, Inhabited

def IntegerPlane.rational (l : IntegerPlane) : Halfplane := ⟨l.a, l.b, l.c⟩

def IntegerPlane.holds (l : IntegerPlane) (p : Point) : Prop :=
  (l.a : ℝ)*p.1 + (l.b : ℝ)*p.2 ≤ (l.c : ℝ)

theorem IntegerPlane.rational_correct (l : IntegerPlane) (p : Point) :
    l.rational.contains p ↔ l.holds p := by
  simp [IntegerPlane.rational, Halfplane.contains, IntegerPlane.holds]

def IntegerCarrier (ls : List IntegerPlane) : Set Point :=
  {p | ∀ l ∈ ls, l.holds p}

theorem integerCarrier_as_polygon (ls : List IntegerPlane) :
    IntegerCarrier ls = Polygon.carrier (ls.map IntegerPlane.rational) := by
  ext p
  simp [IntegerCarrier, Polygon.carrier, IntegerPlane.rational_correct]

structure WeightedPlane where
  weight : ℕ
  plane : IntegerPlane
  deriving DecidableEq, Inhabited

def weightedPlane : List WeightedPlane → IntegerPlane
  | [] => ⟨0,0,0⟩
  | t::ts =>
      ⟨t.weight*t.plane.a + (weightedPlane ts).a,
       t.weight*t.plane.b + (weightedPlane ts).b,
       t.weight*t.plane.c + (weightedPlane ts).c⟩

theorem weightedPlane_holds (ts : List WeightedPlane) (p : Point)
    (h : ∀ t ∈ ts, t.plane.holds p) : (weightedPlane ts).holds p := by
  induction ts with
  | nil => simp [weightedPlane, IntegerPlane.holds]
  | cons t ts ih =>
    have ht := h t (by simp)
    have hs := ih (fun u hu => h u (List.mem_cons_of_mem t hu))
    have ht' := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg t.weight : (0:ℝ) ≤ t.weight)
    have hh := add_le_add ht' hs
    dsimp [weightedPlane, IntegerPlane.holds] at hh ⊢
    push_cast
    nlinarith only [hh]

structure LinearCertificate where
  denominator : ℕ
  terms : List WeightedPlane
  deriving DecidableEq, Inhabited

def LinearCertificate.check (w : LinearCertificate) (ls : List IntegerPlane)
    (target : IntegerPlane) : Bool :=
  decide (0 < w.denominator ∧
    (∀ t ∈ w.terms, t.plane ∈ ls) ∧
    (weightedPlane w.terms).a = w.denominator*target.a ∧
    (weightedPlane w.terms).b = w.denominator*target.b ∧
    (weightedPlane w.terms).c ≤ w.denominator*target.c)

theorem LinearCertificate.sound (w : LinearCertificate) (ls : List IntegerPlane)
    (target : IntegerPlane) (h : w.check ls target = true) :
    IntegerCarrier ls ⊆ {p | target.holds p} := by
  obtain ⟨hd, hmem, ha, hb, hc⟩ := of_decide_eq_true h
  intro p hp
  have hw := weightedPlane_holds w.terms p (fun t ht => hp t.plane (hmem t ht))
  have hd' : (0:ℝ) < w.denominator := by exact_mod_cast hd
  have ha' : ((weightedPlane w.terms).a:ℝ) = (w.denominator:ℝ)*(target.a:ℝ) := by
    exact_mod_cast ha
  have hb' : ((weightedPlane w.terms).b:ℝ) = (w.denominator:ℝ)*(target.b:ℝ) := by
    exact_mod_cast hb
  have hc' : ((weightedPlane w.terms).c:ℝ) ≤ (w.denominator:ℝ)*(target.c:ℝ) := by
    exact_mod_cast hc
  apply (mul_le_mul_left hd').mp
  dsimp [IntegerPlane.holds] at hw ⊢
  calc
    (w.denominator:ℝ)*((target.a:ℝ)*p.1+(target.b:ℝ)*p.2) =
        ((weightedPlane w.terms).a:ℝ)*p.1+((weightedPlane w.terms).b:ℝ)*p.2 := by
      rw [ha',hb']
      ring
    _ ≤ ((weightedPlane w.terms).c:ℝ) := hw
    _ ≤ (w.denominator:ℝ)*(target.c:ℝ) := hc'

theorem LinearCertificate.empty (w : LinearCertificate) (ls : List IntegerPlane)
    (h : w.check ls ⟨0,0,-1⟩ = true) : IntegerCarrier ls = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  have hh := w.sound ls ⟨0,0,-1⟩ h hp
  norm_num [IntegerPlane.holds] at hh

end ElevenSquare.Pending.T03
