import ElevenSquare.Tasks.T03.CellLinear
import ElevenSquare.Tasks.T03.LinearCertificates
import Mathlib.Tactic.FinCases

namespace ElevenSquare.Pending.T03
noncomputable section

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
    (integerBisector a b).holds p ↔
      coordinateDistanceSq p ((a.1:ℝ)/2000000,(a.2:ℝ)/2000000) ≤
      coordinateDistanceSq p ((b.1:ℝ)/2000000,(b.2:ℝ)/2000000) := by
  rw [distance_comparison_linear]
  dsimp [integerBisector, IntegerPlane.holds]
  push_cast
  constructor <;> intro h <;> nlinarith


end
end ElevenSquare.Pending.T03
