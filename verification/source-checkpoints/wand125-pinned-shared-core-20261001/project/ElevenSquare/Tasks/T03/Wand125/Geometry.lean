import ElevenSquare.Geometry
import ElevenSquare.Tasks.T03.Wand125.Upstream.Packing
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
The original axis-vector geometry and the imported angle geometry describe the
same closed squares and open interiors. No orientation or boundary restriction
is added. The explicit nonnegative-side condition handles the empty packing.
-/

namespace ElevenSquare.Pending.T03.Wand125
noncomputable section

def angle (q : UnitSquare) : ℝ := Complex.arg ⟨q.axis.1, q.axis.2⟩

theorem axis_norm (q : UnitSquare) : ‖(⟨q.axis.1, q.axis.2⟩ : ℂ)‖ = 1 := by
  have h := q.axis_unit
  have hn := Complex.sq_abs (⟨q.axis.1, q.axis.2⟩ : ℂ)
  have hp := norm_nonneg (⟨q.axis.1, q.axis.2⟩ : ℂ)
  simp only [normSq, dot] at h
  simp only [Complex.normSq_apply] at hn
  rw [Complex.norm_eq_abs] at hp ⊢
  nlinarith

theorem cos_angle (q : UnitSquare) : Real.cos (angle q) = q.axis.1 := by
  simpa [angle, ← Complex.norm_eq_abs, axis_norm] using
    Complex.abs_mul_cos_arg (⟨q.axis.1, q.axis.2⟩ : ℂ)

theorem sin_angle (q : UnitSquare) : Real.sin (angle q) = q.axis.2 := by
  simpa [angle, ← Complex.norm_eq_abs, axis_norm] using
    Complex.abs_mul_sin_arg (⟨q.axis.1, q.axis.2⟩ : ℂ)

theorem coord_angle (q : UnitSquare) (p : Point) :
    SquarePacking.coord q.center (angle q) p = (localX q p, localY q p) := by
  simp only [SquarePacking.coord, cos_angle, sin_angle, localX, localY, dot, perp]
  ext <;> simp <;> ring

theorem closed_iff (q : UnitSquare) (p : Point) :
    ClosedSquare q p ↔ p ∈ SquarePacking.sq q.center (angle q) 1 := by
  simp only [SquarePacking.sq, Set.mem_setOf_eq, coord_angle, ClosedSquare]

theorem open_iff (q : UnitSquare) (p : Point) :
    OpenSquare q p ↔ p ∈ SquarePacking.sqInt q.center (angle q) 1 := by
  simp only [SquarePacking.sqInt, Set.mem_setOf_eq, coord_angle, OpenSquare]

def ofAngle (c : Point) (θ : ℝ) : UnitSquare where
  center := c
  axis := (Real.cos θ, Real.sin θ)
  axis_unit := by simpa [normSq, dot, pow_two] using Real.cos_sq_add_sin_sq θ

theorem closed_ofAngle (c : Point) (θ : ℝ) (p : Point) :
    ClosedSquare (ofAngle c θ) p ↔ p ∈ SquarePacking.sq c θ 1 := by
  simp [ClosedSquare, ofAngle, localX, localY, dot, perp, SquarePacking.sq,
    SquarePacking.coord, mul_neg, neg_mul] <;> ring_nf <;> simp

theorem open_ofAngle (c : Point) (θ : ℝ) (p : Point) :
    OpenSquare (ofAngle c θ) p ↔ p ∈ SquarePacking.sqInt c θ 1 := by
  simp [OpenSquare, ofAngle, localX, localY, dot, perp, SquarePacking.sqInt,
    SquarePacking.coord, mul_neg, neg_mul] <;> ring_nf <;> simp

theorem packing_to_packs {n : ℕ} {S : ℝ} (P : Packing n S) :
    SquarePacking.Packs n S := by
  refine ⟨fun i => (P.squares i).center, fun i => angle (P.squares i), ?_, ?_⟩
  · intro i p hp
    exact P.contained i p ((closed_iff _ _).mpr hp)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    exact P.interior_disjoint i j hij p
      ⟨(open_iff _ _).mpr hi, (open_iff _ _).mpr hj⟩

theorem packable_iff_packs {n : ℕ} {S : ℝ} :
    Packable n S ↔ 0 ≤ S ∧ SquarePacking.Packs n S := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.side_nonneg, packing_to_packs P⟩
  · rintro ⟨hS, ctr, ang, hin, hd⟩
    refine ⟨⟨fun i => ofAngle (ctr i) (ang i), hS, ?_, ?_⟩⟩
    · intro i p hp
      exact hin i ((closed_ofAngle _ _ _).mp hp)
    · intro i j hij p hp
      exact Set.disjoint_left.mp (hd i j hij)
        ((open_ofAngle _ _ _).mp hp.1) ((open_ofAngle _ _ _).mp hp.2)

theorem packable_eleven_iff {S : ℝ} : Packable 11 S ↔ SquarePacking.Packs 11 S := by
  rw [packable_iff_packs]
  constructor
  · exact And.right
  · rintro ⟨ctr, ang, hin, hd⟩
    have hc : ctr 0 ∈ SquarePacking.sq (ctr 0) (ang 0) 1 := by
      simp [SquarePacking.sq, SquarePacking.coord]
    have hb := hin 0 hc
    exact ⟨hb.1.trans hb.2.1, ctr, ang, hin, hd⟩

end
end ElevenSquare.Pending.T03.Wand125

#print axioms ElevenSquare.Pending.T03.Wand125.packable_eleven_iff
