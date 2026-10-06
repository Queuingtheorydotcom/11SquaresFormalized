import ElevenSquare.Pending.S07_IntegerOverlay
namespace ElevenSquare.Pending

def IntegerPlane.combine (l m : IntegerPlane) (u v : ℤ) : IntegerPlane :=
  ⟨u*l.a+v*m.a,u*l.b+v*m.b,u*l.c+v*m.c⟩

theorem IntegerPlane.combine_sound (l m : IntegerPlane) (u v : ℤ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (p : Point)
    (hl : l.rational.contains p) (hm : m.rational.contains p) :
    (l.combine m u v).rational.contains p := by
  have hu' : (0:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu
  have hv' : (0:ℝ) ≤ (v:ℝ) := by exact_mod_cast hv
  change (l.a:ℝ)*p.1+(l.b:ℝ)*p.2 ≤ (l.c:ℝ) at hl
  change (m.a:ℝ)*p.1+(m.b:ℝ)*p.2 ≤ (m.c:ℝ) at hm
  dsimp [IntegerPlane.combine, IntegerPlane.rational, Halfplane.contains]
  push_cast
  have h1 := mul_le_mul_of_nonneg_left hl hu'
  have h2 := mul_le_mul_of_nonneg_left hm hv'
  nlinarith only [h1,h2]

def IntegerPlane.xBoundCheck (l : IntegerPlane) (n d : ℤ) (lower : Bool) : Bool :=
  decide (0 < d ∧ l.b=0 ∧ l.c*d=l.a*n ∧ (if lower then l.a<0 else 0<l.a))

theorem IntegerPlane.xBoundCheck_sound (l : IntegerPlane) (n d : ℤ)
    (lower : Bool) (h : l.xBoundCheck n d lower = true) (p : Point)
    (hp : l.rational.contains p) :
    if lower then (n:ℝ)/(d:ℝ) ≤ p.1 else p.1 ≤ (n:ℝ)/(d:ℝ) := by
  have hn := of_decide_eq_true h
  have hd : (0:ℝ) < (d:ℝ) := by exact_mod_cast hn.1
  have he : (l.c:ℝ)*(d:ℝ)=(l.a:ℝ)*(n:ℝ) := by exact_mod_cast hn.2.2.1
  change (l.a:ℝ)*p.1+(l.b:ℝ)*p.2 ≤ (l.c:ℝ) at hp
  rw [hn.2.1] at hp
  simp only [Int.cast_zero, zero_mul, add_zero] at hp
  have hh : (l.a:ℝ)*((d:ℝ)*p.1-(n:ℝ)) ≤ 0 := by
    have hm := mul_le_mul_of_nonneg_left hp hd.le
    nlinarith only [hm,he]
  cases lower with
  | false =>
    have ha : (0:ℝ)<(l.a:ℝ) := by exact_mod_cast hn.2.2.2
    apply (le_div_iff₀ hd).mpr
    by_contra hc
    have : 0 < (l.a:ℝ)*((d:ℝ)*p.1-(n:ℝ)) := mul_pos ha (by nlinarith)
    linarith
  | true =>
    have ha : (l.a:ℝ)<0 := by exact_mod_cast hn.2.2.2
    apply (div_le_iff₀ hd).mpr
    by_contra hc
    have : 0 < (l.a:ℝ)*((d:ℝ)*p.1-(n:ℝ)) := mul_pos_of_neg_of_neg ha (by nlinarith)
    linarith

def IntegerPlane.swap (l : IntegerPlane) : IntegerPlane := ⟨l.b,l.a,l.c⟩

theorem IntegerPlane.swap_contains (l : IntegerPlane) (p : Point)
    (hp : l.rational.contains p) : l.swap.rational.contains (p.2,p.1) := by
  dsimp [IntegerPlane.swap, IntegerPlane.rational, Halfplane.contains] at *
  linarith

end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.IntegerPlane.combine_sound
#print axioms ElevenSquare.Pending.IntegerPlane.xBoundCheck_sound
