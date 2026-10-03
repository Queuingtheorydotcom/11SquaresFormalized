import Sqpack.S11Opt.Simplified.QuarticBernstein

/-! Parametric two-facet duality. Source normals are fixed, while their bounds
and the target normal depend quadratically on the angle parameter. Clearing
one positive quadratic denominator produces a quartic certificate. -/
namespace SquarePacking.S11Opt.Simplified.CorrelatedSupport

structure Quad where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  deriving Inhabited, DecidableEq

def Quad.eval (p : Quad) (t : ℝ) : ℝ := p.c0 + p.c1*t + p.c2*t^2

def Quad.scale (r : ℚ) (p : Quad) : Quad := ⟨r*p.c0, r*p.c1, r*p.c2⟩
def Quad.add (p q : Quad) : Quad := ⟨p.c0+q.c0, p.c1+q.c1, p.c2+q.c2⟩
def Quad.sub (p q : Quad) : Quad := p.add (q.scale (-1))
def Quad.toPoly (p : Quad) : QuarticBernstein.Poly := ⟨p.c0,p.c1,p.c2,0,0⟩
def Quad.mul (p q : Quad) : QuarticBernstein.Poly :=
  ⟨p.c0*q.c0, p.c0*q.c1+p.c1*q.c0,
   p.c0*q.c2+p.c1*q.c1+p.c2*q.c0,
   p.c1*q.c2+p.c2*q.c1, p.c2*q.c2⟩
def psub (p q : QuarticBernstein.Poly) : QuarticBernstein.Poly :=
  ⟨p.c0-q.c0,p.c1-q.c1,p.c2-q.c2,p.c3-q.c3,p.c4-q.c4⟩

@[simp] theorem eval_scale (r : ℚ) (p : Quad) (t : ℝ) :
    (p.scale r).eval t = (r : ℝ)*p.eval t := by
  simp only [Quad.eval, Quad.scale]; push_cast; ring
@[simp] theorem eval_add (p q : Quad) (t : ℝ) :
    (p.add q).eval t = p.eval t + q.eval t := by
  simp only [Quad.eval, Quad.add]; push_cast; ring
@[simp] theorem eval_sub (p q : Quad) (t : ℝ) :
    (p.sub q).eval t = p.eval t - q.eval t := by
  simp only [Quad.sub, eval_add, eval_scale, Rat.cast_neg, Rat.cast_one]; ring
@[simp] theorem eval_toPoly (p : Quad) (t : ℝ) :
    QuarticBernstein.eval p.toPoly t = p.eval t := by simp [QuarticBernstein.eval, Quad.toPoly, Quad.eval]
@[simp] theorem eval_mul (p q : Quad) (t : ℝ) :
    QuarticBernstein.eval (p.mul q) t = p.eval t * q.eval t := by
  simp only [QuarticBernstein.eval, Quad.mul, Quad.eval]; push_cast; ring
@[simp] theorem eval_psub (p q : QuarticBernstein.Poly) (t : ℝ) :
    QuarticBernstein.eval (psub p q) t = QuarticBernstein.eval p t - QuarticBernstein.eval q t := by
  simp only [QuarticBernstein.eval, psub]; push_cast; ring

structure Source where
  a : ℚ
  b : ℚ
  bound : Quad
  deriving Inhabited, DecidableEq

structure Target where
  x : Quad
  y : Quad
  rhs : Quad
  deriving Inhabited, DecidableEq

def Holds (D : Quad) (s : Source) (t x y : ℝ) : Prop :=
  2*D.eval t*((s.a : ℝ)*x+(s.b : ℝ)*y) ≤ s.bound.eval t

def Satisfies (z : Target) (t x y : ℝ) : Prop :=
  z.x.eval t*x + z.y.eval t*y ≤ z.rhs.eval t

def det (u v : Source) : ℚ := u.a*v.b-u.b*v.a
def alpha (v : Source) (z : Target) : Quad := (z.x.scale v.b).sub (z.y.scale v.a)
def beta (u : Source) (z : Target) : Quad := (z.y.scale u.a).sub (z.x.scale u.b)

def slack (D : Quad) (u v : Source) (z : Target) : QuarticBernstein.Poly :=
  psub (psub ((D.scale (2*det u v)).mul z.rhs)
    ((alpha v z).mul u.bound)) ((beta u z).mul v.bound)

def pairCheck (D : Quad) (u v : Source) (z : Target) (a b : ℚ) : Bool :=
  decide (0 < det u v) && QuarticBernstein.check (alpha v z).toPoly a b &&
  QuarticBernstein.check (beta u z).toPoly a b && QuarticBernstein.check (slack D u v z) a b

theorem pair_sound (D : Quad) (u v : Source) (z : Target) (a b : ℚ)
    (h : pairCheck D u v z a b = true) (t x y : ℝ)
    (ha : (a : ℝ) ≤ t) (hb : t ≤ b) (hD : 0 < D.eval t)
    (hu : Holds D u t x y) (hv : Holds D v t x y) : Satisfies z t x y := by
  simp only [pairCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hd : (0 : ℝ) < (det u v : ℝ) := by exact_mod_cast h.1.1.1
  have hα := QuarticBernstein.check_sound _ _ _ h.1.1.2 t ha hb
  have hβ := QuarticBernstein.check_sound _ _ _ h.1.2 t ha hb
  have hs := QuarticBernstein.check_sound _ _ _ h.2 t ha hb
  simp only [eval_toPoly] at hα hβ
  simp only [slack, eval_psub, eval_mul, eval_scale, Rat.cast_mul,
    Rat.cast_ofNat] at hs
  have hsum := add_le_add
    (mul_le_mul_of_nonneg_left hu hα) (mul_le_mul_of_nonneg_left hv hβ)
  have identity : (alpha v z).eval t*(2*D.eval t*((u.a : ℝ)*x+(u.b : ℝ)*y)) +
      (beta u z).eval t*(2*D.eval t*((v.a : ℝ)*x+(v.b : ℝ)*y)) =
      (2*(det u v : ℝ)*D.eval t)*(z.x.eval t*x+z.y.eval t*y) := by
    simp only [alpha, beta, eval_sub, eval_scale, det]
    push_cast
    ring
  unfold Holds at hsum
  rw [identity] at hsum
  have htotal : (2*(det u v : ℝ)*D.eval t)*(z.x.eval t*x+z.y.eval t*y) ≤
      (2*(det u v : ℝ)*D.eval t)*z.rhs.eval t := by linarith only [hsum, hs]
  exact le_of_mul_le_mul_left htotal (by positivity : 0 < 2*(det u v : ℝ)*D.eval t)

def facetCheck (D : Quad) (ss : List Source) (z : Target) (ij : ℕ × ℕ)
    (a b : ℚ) : Bool :=
  match ss[ij.1]?, ss[ij.2]? with
  | some u, some v => pairCheck D u v z a b
  | _, _ => false

theorem facet_sound (D : Quad) (ss : List Source) (z : Target) (ij : ℕ × ℕ)
    (a b : ℚ) (h : facetCheck D ss z ij a b = true) (t x y : ℝ)
    (ha : (a : ℝ) ≤ t) (hb : t ≤ b) (hD : 0 < D.eval t)
    (hh : ∀ s ∈ ss, Holds D s t x y) : Satisfies z t x y := by
  unfold facetCheck at h
  cases hu : ss[ij.1]? with
  | none => simp [hu] at h
  | some u =>
    cases hv : ss[ij.2]? with
    | none => simp [hu, hv] at h
    | some v =>
      exact pair_sound D u v z a b (by simpa [hu, hv] using h) t x y ha hb hD
        (hh u (List.mem_of_getElem? hu)) (hh v (List.mem_of_getElem? hv))

def listCheck (D : Quad) (ss : List Source) (a b : ℚ) :
    List Target → List (ℕ × ℕ) → Bool
  | [], [] => true
  | z :: zs, ij :: ijs => facetCheck D ss z ij a b && listCheck D ss a b zs ijs
  | _, _ => false

theorem list_sound (D : Quad) (ss : List Source) (zs : List Target)
    (ijs : List (ℕ × ℕ)) (a b : ℚ) (h : listCheck D ss a b zs ijs = true)
    (t x y : ℝ) (ha : (a : ℝ) ≤ t) (hb : t ≤ b) (hD : 0 < D.eval t)
    (hh : ∀ s ∈ ss, Holds D s t x y) : ∀ z ∈ zs, Satisfies z t x y := by
  induction zs generalizing ijs with
  | nil => simp
  | cons z zs ih =>
    cases ijs with
    | nil => simp [listCheck] at h
    | cons ij ijs =>
      simp only [listCheck, Bool.and_eq_true] at h
      intro z' hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact facet_sound D ss _ ij a b h.1 t x y ha hb hD hh
      · exact ih ijs h.2 z' hz

#print axioms pair_sound
#print axioms list_sound
end SquarePacking.S11Opt.Simplified.CorrelatedSupport
