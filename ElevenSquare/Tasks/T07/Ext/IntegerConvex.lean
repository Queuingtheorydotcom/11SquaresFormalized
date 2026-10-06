import ElevenSquare.Tasks.T07.Ext.Poly

/-! An exact integer implementation of `convexF`.

Each rational edge and vertex is converted once to homogeneous integer
coordinates. The quadratic loop then uses integer multiplication, addition and
strict comparison, without reducing rational fractions. Positive denominators
preserve strict inequalities and all boundary cases. -/
namespace ElevenSquare.Tasks.T07.Ext
open ElevenSquare ElevenSquare.Pending

/-- A rational point represented by `(x / d, y / d)`. -/
structure IntHomPoint where
  x : ℤ
  y : ℤ
  d : ℤ

/-- Coefficients of a halfplane after multiplying by a positive denominator. -/
structure IntHomHalfplane where
  a : ℤ
  b : ℤ
  c : ℤ

def pointInts (p : QPoint) : IntHomPoint :=
  ⟨p.1.num * p.2.den, p.2.num * p.1.den, (p.1.den : ℤ) * p.2.den⟩

def halfplaneInts (h : Halfplane) : IntHomHalfplane :=
  ⟨h.a.num * h.b.den * h.c.den,
    h.b.num * h.a.den * h.c.den,
    h.c.num * h.a.den * h.b.den⟩

def strictSideInts (h : IntHomHalfplane) (p : IntHomPoint) : Bool :=
  decide (h.a * p.x + h.b * p.y < h.c * p.d)

private lemma num_eq_mul_den (q : ℚ) : (q.num : ℚ) = q * q.den := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  exact ((eq_div_iff hd).mp (Rat.num_div_den q).symm).symm

/-- Cross-multiplication for arbitrary rational coefficients and coordinates.
No normalization, nonzero numerator, or geometric assumption is required. -/
theorem integer_side_iff (h : Halfplane) (p : QPoint) :
    (halfplaneInts h).a * (pointInts p).x +
      (halfplaneInts h).b * (pointInts p).y <
        (halfplaneInts h).c * (pointInts p).d ↔
      h.a * p.1 + h.b * p.2 < h.c := by
  let H : ℚ := (h.a.den : ℚ) * h.b.den * h.c.den
  let P : ℚ := (p.1.den : ℚ) * p.2.den
  have den_pos (q : ℚ) : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hH : 0 < H := mul_pos (mul_pos (den_pos h.a) (den_pos h.b)) (den_pos h.c)
  have hP : 0 < P := mul_pos (den_pos p.1) (den_pos p.2)
  have ha : ((halfplaneInts h).a : ℚ) = h.a * H := by
    simp only [halfplaneInts, Int.cast_mul, Int.cast_natCast]
    rw [num_eq_mul_den h.a]
    dsimp [H]
    ring
  have hb : ((halfplaneInts h).b : ℚ) = h.b * H := by
    simp only [halfplaneInts, Int.cast_mul, Int.cast_natCast]
    rw [num_eq_mul_den h.b]
    dsimp [H]
    ring
  have hc : ((halfplaneInts h).c : ℚ) = h.c * H := by
    simp only [halfplaneInts, Int.cast_mul, Int.cast_natCast]
    rw [num_eq_mul_den h.c]
    dsimp [H]
    ring
  have hx : ((pointInts p).x : ℚ) = p.1 * P := by
    simp only [pointInts, Int.cast_mul, Int.cast_natCast]
    rw [num_eq_mul_den p.1]
    dsimp [P]
    ring
  have hy : ((pointInts p).y : ℚ) = p.2 * P := by
    simp only [pointInts, Int.cast_mul, Int.cast_natCast]
    rw [num_eq_mul_den p.2]
    dsimp [P]
    ring
  have hd : ((pointInts p).d : ℚ) = P := by
    simp only [pointInts, Int.cast_mul, Int.cast_natCast, P]
  have cast_iff :
      (halfplaneInts h).a * (pointInts p).x +
        (halfplaneInts h).b * (pointInts p).y <
          (halfplaneInts h).c * (pointInts p).d ↔
        ((halfplaneInts h).a : ℚ) * (pointInts p).x +
          ((halfplaneInts h).b : ℚ) * (pointInts p).y <
            ((halfplaneInts h).c : ℚ) * (pointInts p).d := by
    norm_cast
  rw [cast_iff, ha, hb, hc, hx, hy, hd]
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

/-- The same indexed edge/vertex checks as `convexF`, with integer inner tests.
Both conversions are outside the quadratic loop. -/
def convexIntF (V : List QPoint) : Bool :=
  let es := (edgesF V).zipIdx.map fun ek => (halfplaneInts ek.1, ek.2)
  let vs := V.zipIdx.map fun vm => (pointInts vm.1, vm.2)
  decide (3 ≤ V.length) &&
    (es.all fun ek => vs.all fun vm =>
      decide (vm.2 = ek.2) || decide (vm.2 = (ek.2 + 1) % V.length) ||
        strictSideInts ek.1 vm.1)

theorem convexIntF_eq_convexF (V : List QPoint) : convexIntF V = convexF V := by
  simp only [convexIntF, List.all_map, Function.comp_def, strictSideInts_eq, convexF]

theorem convexIntF_imp {V : List QPoint} (h : convexIntF V = true) :
    convexB V = true :=
  convexF_imp ((convexIntF_eq_convexF V) ▸ h)

end ElevenSquare.Tasks.T07.Ext
