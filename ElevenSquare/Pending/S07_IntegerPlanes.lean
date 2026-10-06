import ElevenSquare.Pending.S07_ViewPlanes

/-! Executable integer halfplanes and checked fraction inequalities. All
arithmetic in the Boolean certificate is over integers. -/
namespace ElevenSquare.Pending

structure IntegerPlane where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq, Inhabited

def IntegerPlane.rational (l : IntegerPlane) : Halfplane := ⟨l.a,l.b,l.c⟩

def IntegerPlane.fractionCheck (l : IntegerPlane) (nx dx ny dy : ℤ) : Bool :=
  decide (0 < dx ∧ 0 < dy ∧ l.a*nx*dy+l.b*ny*dx ≤ l.c*dx*dy)

theorem IntegerPlane.fractionCheck_sound (l : IntegerPlane) (nx dx ny dy : ℤ)
    (h : l.fractionCheck nx dx ny dy = true) :
    l.rational.contains (realPoint ((nx/dx : ℚ),(ny/dy : ℚ))) := by
  have hn := of_decide_eq_true h
  have hx : (0:ℝ) < (dx:ℝ) := by exact_mod_cast hn.1
  have hy : (0:ℝ) < (dy:ℝ) := by exact_mod_cast hn.2.1
  have hi : (l.a:ℝ)*(nx:ℝ)*(dy:ℝ)+(l.b:ℝ)*(ny:ℝ)*(dx:ℝ) ≤
      (l.c:ℝ)*(dx:ℝ)*(dy:ℝ) := by exact_mod_cast hn.2.2
  change ((l.a:ℚ):ℝ)*((nx/dx:ℚ):ℝ)+((l.b:ℚ):ℝ)*((ny/dy:ℚ):ℝ) ≤ ((l.c:ℚ):ℝ)
  push_cast
  apply (mul_le_mul_iff_of_pos_right (mul_pos hx hy)).mp
  calc
    _ = (l.a:ℝ)*(nx:ℝ)*(dy:ℝ)+(l.b:ℝ)*(ny:ℝ)*(dx:ℝ) := by
      field_simp [ne_of_gt hx, ne_of_gt hy]
      <;> ring
    _ ≤ _ := by nlinarith [hi]

def IntegerPlane.view (g : Fin 4) (l : IntegerPlane) : IntegerPlane :=
  (![l, ⟨-l.a,l.b,l.c-l.a⟩, ⟨l.b,-l.a,l.c-l.a⟩, ⟨l.b,l.a,l.c⟩] : Fin 4 → IntegerPlane) g

theorem IntegerPlane.view_correct (g : Fin 4) (l : IntegerPlane) :
    (l.view g).rational = viewPlane g l.rational := by
  fin_cases g <;> simp [IntegerPlane.view, IntegerPlane.rational, viewPlane]

def integerSite (i : Fin 16) : ℤ × ℤ :=
  (![(209982,265837),(746404,91006),(1267243,277512),(1731123,205608),
     (206181,800758),(742311,625866),(1270514,832045),(1781756,671052),
     (218244,1328948),(729486,1167955),(1257689,1374134),(1793819,1199242),
     (268877,1794392),(732757,1722488),(1253596,1908994),(1790018,1734163)] :
     Fin 16 → ℤ × ℤ) i

theorem integerSite_correct (i : Fin 16) :
    coverSite i = (((integerSite i).1:ℝ)/2000000, ((integerSite i).2:ℝ)/2000000) := by
  fin_cases i <;> norm_num [integerSite, coverSite]

def integerBisector (a b : ℤ × ℤ) : IntegerPlane :=
  ⟨4000000*(b.1-a.1),4000000*(b.2-a.2),
    b.1*b.1+b.2*b.2-a.1*a.1-a.2*a.2⟩

theorem integerBisector_correct (a b : ℤ × ℤ) (p : Point) :
    (integerBisector a b).rational.contains p ↔
      coordinateDistanceSq p ((a.1:ℝ)/2000000,(a.2:ℝ)/2000000) ≤
      coordinateDistanceSq p ((b.1:ℝ)/2000000,(b.2:ℝ)/2000000) := by
  rw [distance_comparison_linear]
  dsimp [integerBisector, IntegerPlane.rational, Halfplane.contains]
  push_cast
  constructor <;> intro h <;> nlinarith

end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.IntegerPlane.fractionCheck_sound
#print axioms ElevenSquare.Pending.integerSite_correct
#print axioms ElevenSquare.Pending.integerBisector_correct
