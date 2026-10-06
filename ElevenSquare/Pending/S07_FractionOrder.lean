import ElevenSquare.Pending.S07_IntegerOverlay
namespace ElevenSquare.Pending

def fractionLE (n d m e : ℤ) : Bool := decide (0<d ∧ 0<e ∧ n*e≤m*d)
def fractionLT (n d m e : ℤ) : Bool := decide (0<d ∧ 0<e ∧ n*e<m*d)
def fractionEQ (n d m e : ℤ) : Bool := decide (0<d ∧ 0<e ∧ n*e=m*d)

theorem fractionLE_sound (n d m e : ℤ) (h : fractionLE n d m e = true) :
    (n:ℝ)/(d:ℝ) ≤ (m:ℝ)/(e:ℝ) := by
  have hh := of_decide_eq_true h
  have hd : (0:ℝ)<(d:ℝ) := by exact_mod_cast hh.1
  have he : (0:ℝ)<(e:ℝ) := by exact_mod_cast hh.2.1
  apply (div_le_div_iff₀ hd he).mpr
  exact_mod_cast hh.2.2

theorem fractionLT_sound (n d m e : ℤ) (h : fractionLT n d m e = true) :
    (n:ℝ)/(d:ℝ) < (m:ℝ)/(e:ℝ) := by
  have hh := of_decide_eq_true h
  have hd : (0:ℝ)<(d:ℝ) := by exact_mod_cast hh.1
  have he : (0:ℝ)<(e:ℝ) := by exact_mod_cast hh.2.1
  apply (div_lt_div_iff₀ hd he).mpr
  exact_mod_cast hh.2.2

theorem fractionEQ_sound (n d m e : ℤ) (h : fractionEQ n d m e = true) :
    (n:ℝ)/(d:ℝ) = (m:ℝ)/(e:ℝ) := by
  have hh := of_decide_eq_true h
  have hd : (d:ℝ)≠0 := ne_of_gt (by exact_mod_cast hh.1 : (0:ℝ)<d)
  have he : (e:ℝ)≠0 := ne_of_gt (by exact_mod_cast hh.2.1 : (0:ℝ)<e)
  apply (div_eq_div_iff hd he).mpr
  exact_mod_cast hh.2.2

noncomputable def FractionPoint.real (q : FractionPoint) : Point :=
  ((q.nx:ℝ)/(q.dx:ℝ),(q.ny:ℝ)/(q.dy:ℝ))

theorem FractionPoint.real_correct (q : FractionPoint) :
    q.real = realPoint q.rational := by
  simp [FractionPoint.real, FractionPoint.rational, realPoint]

theorem FractionPoint.xLE (q r : FractionPoint)
    (h : fractionLE q.nx q.dx r.nx r.dx = true) : q.real.1 ≤ r.real.1 :=
  fractionLE_sound _ _ _ _ h

theorem FractionPoint.xLT (q r : FractionPoint)
    (h : fractionLT q.nx q.dx r.nx r.dx = true) : q.real.1 < r.real.1 :=
  fractionLT_sound _ _ _ _ h

theorem FractionPoint.xEQ (q r : FractionPoint)
    (h : fractionEQ q.nx q.dx r.nx r.dx = true) : q.real.1 = r.real.1 :=
  fractionEQ_sound _ _ _ _ h

end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.fractionLE_sound
#print axioms ElevenSquare.Pending.fractionLT_sound
#print axioms ElevenSquare.Pending.fractionEQ_sound
