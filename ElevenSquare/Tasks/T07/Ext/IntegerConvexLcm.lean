import ElevenSquare.Tasks.T07.Ext.IntegerConvex

/-! Optional convexity checker using least common denominators.

The products in `IntegerConvex` can retain large common factors. Here each
vertex and edge uses one positive least common denominator. Conversion performs
integer gcd/division only outside the quadratic edge/vertex loop. -/
namespace ElevenSquare.Tasks.T07.Ext.IntegerConvexLcm
open ElevenSquare ElevenSquare.Pending

def pointDen (p : QPoint) : ℕ := Nat.lcm p.1.den p.2.den

def planeDen (h : Halfplane) : ℕ := Nat.lcm (Nat.lcm h.a.den h.b.den) h.c.den

/-- The numerator at denominator `d`; used only where `q.den ∣ d`. -/
def scaleNumerator (q : ℚ) (d : ℕ) : ℤ := q.num * (d / q.den : ℕ)

def pointInts (p : QPoint) : IntHomPoint :=
  let d := pointDen p
  ⟨scaleNumerator p.1 d, scaleNumerator p.2 d, d⟩

def halfplaneInts (h : Halfplane) : IntHomHalfplane :=
  let d := planeDen h
  ⟨scaleNumerator h.a d, scaleNumerator h.b d, scaleNumerator h.c d⟩

private theorem scaleNumerator_eq (q : ℚ) (d : ℕ) (hq : q.den ∣ d) :
    (scaleNumerator q d : ℚ) = q * d := by
  have hd : (q.den : ℚ) * (d / q.den : ℕ) = d := by
    exact_mod_cast Nat.mul_div_cancel' hq
  simp only [scaleNumerator, Int.cast_mul, Int.cast_natCast]
  rw [← Rat.mul_den_eq_num q, mul_assoc, hd]

/-- Strict side comparisons are unchanged by least-common-denominator scaling. -/
theorem integer_side_iff (h : Halfplane) (p : QPoint) :
    (halfplaneInts h).a * (pointInts p).x +
      (halfplaneInts h).b * (pointInts p).y <
        (halfplaneInts h).c * (pointInts p).d ↔
      h.a * p.1 + h.b * p.2 < h.c := by
  let H : ℚ := planeDen h
  let P : ℚ := pointDen p
  have hH : 0 < H := by
    dsimp [H, planeDen]
    exact_mod_cast Nat.lcm_pos (Nat.lcm_pos h.a.den_pos h.b.den_pos) h.c.den_pos
  have hP : 0 < P := by
    dsimp [P, pointDen]
    exact_mod_cast Nat.lcm_pos p.1.den_pos p.2.den_pos
  have ha : (scaleNumerator h.a (planeDen h) : ℚ) = h.a * H :=
    scaleNumerator_eq h.a _
      ((Nat.dvd_lcm_left h.a.den h.b.den).trans (Nat.dvd_lcm_left _ _))
  have hb : (scaleNumerator h.b (planeDen h) : ℚ) = h.b * H :=
    scaleNumerator_eq h.b _
      ((Nat.dvd_lcm_right h.a.den h.b.den).trans (Nat.dvd_lcm_left _ _))
  have hc : (scaleNumerator h.c (planeDen h) : ℚ) = h.c * H :=
    scaleNumerator_eq h.c _ (Nat.dvd_lcm_right _ _)
  have hx : (scaleNumerator p.1 (pointDen p) : ℚ) = p.1 * P :=
    scaleNumerator_eq p.1 _ (Nat.dvd_lcm_left _ _)
  have hy : (scaleNumerator p.2 (pointDen p) : ℚ) = p.2 * P :=
    scaleNumerator_eq p.2 _ (Nat.dvd_lcm_right _ _)
  have cast_iff :
      (halfplaneInts h).a * (pointInts p).x +
        (halfplaneInts h).b * (pointInts p).y <
          (halfplaneInts h).c * (pointInts p).d ↔
        ((halfplaneInts h).a : ℚ) * (pointInts p).x +
          ((halfplaneInts h).b : ℚ) * (pointInts p).y <
            ((halfplaneInts h).c : ℚ) * (pointInts p).d := by
    norm_cast
  rw [cast_iff]
  dsimp only [halfplaneInts, pointInts]
  simp only [Int.cast_natCast]
  rw [ha, hb, hc, hx, hy]
  change h.a * H * (p.1 * P) + h.b * H * (p.2 * P) < h.c * H * P ↔
    h.a * p.1 + h.b * p.2 < h.c
  have hl : h.a * H * (p.1 * P) + h.b * H * (p.2 * P) =
      (h.a * p.1 + h.b * p.2) * (H * P) := by ring
  have hr : h.c * H * P = h.c * (H * P) := by ring
  rw [hl, hr]
  exact mul_lt_mul_iff_left₀ (mul_pos hH hP)

theorem strictSideInts_eq (h : Halfplane) (p : QPoint) :
    strictSideInts (halfplaneInts h) (pointInts p) =
      decide (h.a * p.1 + h.b * p.2 < h.c) := by
  unfold strictSideInts
  simp only [integer_side_iff]

def convexLcmF (V : List QPoint) : Bool :=
  let es := (edgesF V).zipIdx.map fun ek => (halfplaneInts ek.1, ek.2)
  let vs := V.zipIdx.map fun vm => (pointInts vm.1, vm.2)
  decide (3 ≤ V.length) &&
    (es.all fun ek => vs.all fun vm =>
      decide (vm.2 = ek.2) || decide (vm.2 = (ek.2 + 1) % V.length) ||
        strictSideInts ek.1 vm.1)

theorem convexLcmF_eq_convexF (V : List QPoint) : convexLcmF V = convexF V := by
  simp only [convexLcmF, List.all_map, Function.comp_def, strictSideInts_eq, convexF]

end ElevenSquare.Tasks.T07.Ext.IntegerConvexLcm
