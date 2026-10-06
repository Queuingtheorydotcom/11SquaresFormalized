import ElevenSquare.Pending.S08_SeparationGeometry

namespace ElevenSquare.Pending.SATCoordinates
noncomputable section

def cosine (a b : UnitSquare) : ℝ := dot a.axis b.axis
def sine (a b : UnitSquare) : ℝ := dot (perp a.axis) b.axis

theorem cross_perp (a b : UnitSquare) : dot a.axis (perp b.axis) = -sine a b := by
  dsimp [sine, dot, perp]; ring

theorem both_perp (a b : UnitSquare) : dot (perp a.axis) (perp b.axis) = cosine a b := by
  dsimp [cosine, dot, perp]; ring

theorem relative_unit (a b : UnitSquare) : (cosine a b)^2+(sine a b)^2=1 := by
  have he := orthogonal_decomposition b.axis a.axis a.axis_unit
  rw [dot_comm b.axis a.axis, dot_comm b.axis (perp a.axis), b.axis_unit] at he
  exact he

theorem vector_basis (a : UnitSquare) (p v : Point) :
    dot p v = dot p a.axis * dot a.axis v + dot p (perp a.axis) * dot (perp a.axis) v := by
  have he := dot_reconstruction ({ a with center := 0 } : UnitSquare) p v
  simpa only [dot_reconstruction, localX, localY, sub_zero] using he

theorem localX_affine (a : UnitSquare) (x y : ℝ) :
    localX a (a.center + x • a.axis + y • perp a.axis) = x := by
  calc
    _ = x * normSq a.axis := by dsimp [localX, normSq, dot, perp]; ring
    _ = x := by rw [a.axis_unit, mul_one]

theorem localY_affine (a : UnitSquare) (x y : ℝ) :
    localY a (a.center + x • a.axis + y • perp a.axis) = y := by
  calc
    _ = y * normSq a.axis := by dsimp [localY, normSq, dot, perp]; ring
    _ = y := by rw [a.axis_unit, mul_one]

theorem localX_change (a b : UnitSquare) (p : Point) :
    localX b p = localX a p * cosine a b + localY a p * sine a b -
      dot (b.center-a.center) b.axis := by
  calc
    _ = dot (p-a.center) b.axis - dot (b.center-a.center) b.axis := by
      dsimp [localX, dot]; ring
    _ = _ := by rw [dot_reconstruction]; rfl

theorem localY_change (a b : UnitSquare) (p : Point) :
    localY b p = localX a p * (-sine a b) + localY a p * cosine a b -
      dot (b.center-a.center) (perp b.axis) := by
  calc
    _ = dot (p-a.center) (perp b.axis) - dot (b.center-a.center) (perp b.axis) := by
      dsimp [localY, dot, perp]; ring
    _ = _ := by rw [dot_reconstruction, cross_perp, both_perp]

theorem half_abs_lt {t : ℝ} (h : |t| < 1) : |t/2| < (1:ℝ)/2 := by
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).2 h

#print axioms cross_perp
#print axioms both_perp
#print axioms relative_unit
#print axioms vector_basis
#print axioms localX_affine
#print axioms localY_affine
#print axioms localX_change
#print axioms localY_change
#print axioms half_abs_lt
end
end ElevenSquare.Pending.SATCoordinates
