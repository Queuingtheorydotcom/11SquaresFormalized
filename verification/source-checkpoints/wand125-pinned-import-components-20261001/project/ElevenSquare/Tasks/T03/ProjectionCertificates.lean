import ElevenSquare.Tasks.T03.LinearCertificates

namespace ElevenSquare.Pending.T03
noncomputable section

def LinearCertificate.strictCheck (w : LinearCertificate) (ls : List IntegerPlane)
    (target : IntegerPlane) : Bool :=
  decide (0 < w.denominator ∧
    (∀ t ∈ w.terms, t.plane ∈ ls) ∧
    (weightedPlane w.terms).a = w.denominator*target.a ∧
    (weightedPlane w.terms).b = w.denominator*target.b ∧
    (weightedPlane w.terms).c < w.denominator*target.c)

theorem LinearCertificate.strict_sound (w : LinearCertificate) (ls : List IntegerPlane)
    (target : IntegerPlane) (h : w.strictCheck ls target = true)
    (p : Point) (hp : p ∈ IntegerCarrier ls) :
    (target.a:ℝ)*p.1+(target.b:ℝ)*p.2 < (target.c:ℝ) := by
  obtain ⟨hd,hmem,ha,hb,hc⟩ := of_decide_eq_true h
  have hw := weightedPlane_holds w.terms p (fun t ht => hp t.plane (hmem t ht))
  have hd' : (0:ℝ) < w.denominator := by exact_mod_cast hd
  have ha' : ((weightedPlane w.terms).a:ℝ) = (w.denominator:ℝ)*(target.a:ℝ) := by
    exact_mod_cast ha
  have hb' : ((weightedPlane w.terms).b:ℝ) = (w.denominator:ℝ)*(target.b:ℝ) := by
    exact_mod_cast hb
  have hc' : ((weightedPlane w.terms).c:ℝ) < (w.denominator:ℝ)*(target.c:ℝ) := by
    exact_mod_cast hc
  apply (mul_lt_mul_left hd').mp
  dsimp [IntegerPlane.holds] at hw
  calc
    (w.denominator:ℝ)*((target.a:ℝ)*p.1+(target.b:ℝ)*p.2) =
        ((weightedPlane w.terms).a:ℝ)*p.1+((weightedPlane w.terms).b:ℝ)*p.2 := by
      rw [ha',hb']; ring
    _ ≤ ((weightedPlane w.terms).c:ℝ) := hw
    _ < (w.denominator:ℝ)*(target.c:ℝ) := hc'

structure ProjectionCertificate where
  factor : ℕ
  target : IntegerPlane
  witness : LinearCertificate
  deriving DecidableEq, Inhabited

def ProjectionCertificate.check (w : ProjectionCertificate) (ls : List IntegerPlane)
    (v n : QPoint) : Bool :=
  decide (0 < w.factor ∧
    (w.target.a:ℚ) = -(w.factor:ℚ)*n.1 ∧
    (w.target.b:ℚ) = -(w.factor:ℚ)*n.2 ∧
    (w.target.c:ℚ) = (w.factor:ℚ)*(1/2-n.1*v.1-n.2*v.2)) &&
  w.witness.strictCheck ls w.target

theorem ProjectionCertificate.sound (w : ProjectionCertificate) (ls : List IntegerPlane)
    (v n : QPoint) (h : w.check ls v n = true) (p : Point)
    (hp : p ∈ IntegerCarrier ls) :
    (n.1:ℝ)*((v.1:ℝ)-p.1)+(n.2:ℝ)*((v.2:ℝ)-p.2) < 1/2 := by
  simp only [ProjectionCertificate.check, Bool.and_eq_true] at h
  obtain ⟨he,hw⟩ := h
  obtain ⟨hd,ha,hb,hc⟩ := of_decide_eq_true he
  have hd' : (0:ℝ) < w.factor := by exact_mod_cast hd
  have ha' : (w.target.a:ℝ) = -(w.factor:ℝ)*(n.1:ℝ) := by exact_mod_cast ha
  have hb' : (w.target.b:ℝ) = -(w.factor:ℝ)*(n.2:ℝ) := by exact_mod_cast hb
  have hc' := congrArg (fun x : ℚ => (x:ℝ)) hc
  push_cast at hc'
  have hh := w.witness.strict_sound ls w.target hw p hp
  rw [ha',hb',hc'] at hh
  apply (mul_lt_mul_left hd').mp
  nlinarith only [hh]

end
end ElevenSquare.Pending.T03
