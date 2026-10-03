import Sqpack.S11Opt.Simplified.PolyhedralPoint

/-! Two partial captures can cover a pose without either point being captured
uniformly: the two missing square sides have opposite normals. -/
namespace SquarePacking.S11Opt.Simplified.ComplementaryPoints
open SquarePacking BoxTree FieldTree
abbrev Plane := PolyhedralPoint.Plane

def opposite : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | _ => 2

def oppositeSide : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | _ => 2

@[simp] theorem oppositeSide_val (k : Fin 4) :
    (oppositeSide k).val = opposite k.val := by fin_cases k <;> rfl

def planeAt (Q : ℕ) (A B C : ℤ) (p : ℕ × ℕ) : ℕ → Plane
  | 0 => (-A, -B, C*Q-A*p.1-B*p.2)
  | 1 => (A, B, C*Q+A*p.1+B*p.2)
  | 2 => (B, -A, C*Q+B*p.1-A*p.2)
  | _ => (-B, A, C*Q-B*p.1+A*p.2)

def planesExcept (Q : ℕ) (A B C : ℤ) (p : ℕ × ℕ) (k : ℕ) : List Plane :=
  ((List.range 4).filter (fun j => decide (j ≠ k))).map (planeAt Q A B C p)

theorem planeAt_mem {Q A B C p k j} (hj : j < 4) (hne : j ≠ k) :
    planeAt Q A B C p j ∈ planesExcept Q A B C p k := by
  apply List.mem_map.mpr
  exact ⟨j, by simp [hne, hj], rfl⟩

def partialTargets (Q R a b : ℕ) (p : ℕ × ℕ) (k : ℕ) : List Plane :=
  planesExcept Q (2*((R : ℤ)*R-(a : ℤ)*a)) (4*(R : ℤ)*a)
      ((R : ℤ)*R+(a : ℤ)*a) p k ++
  planesExcept Q (2*((R : ℤ)*R-(b : ℤ)*b)) (4*(R : ℤ)*b)
      ((R : ℤ)*R+(b : ℤ)*b) p k ++
  planesExcept Q (2*((R : ℤ)*R-(a : ℤ)*b)) (2*(R : ℤ)*(a+b))
      ((R : ℤ)*R+(a : ℤ)*b) p k

def partialPairs (pairs : List (ℕ × ℕ)) (k : ℕ) : List (ℕ × ℕ) :=
  (pairs.zipIdx.filter (fun ij => decide (ij.2 % 4 ≠ k))).map Prod.fst

theorem partial_sound {Q R a b k : ℕ} (hQ : 0 < Q) (hR : 0 < R) (hb : b ≤ R)
    (p : ℕ × ℕ) (c : ℝ × ℝ) (u : ℝ)
    (hu0 : (a : ℝ)/R ≤ u) (hu1 : u ≤ (b : ℝ)/R)
    (ht : ∀ z ∈ partialTargets Q R a b p k, InHP Q z c) :
    ∀ j : Fin 4, j.val ≠ k →
      gval j ((p.1 : ℝ)/Q-c.1) ((p.2 : ℝ)/Q-c.2) u ≤ 0 := by
  intro j hj
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hu0' : 0 ≤ u := (div_nonneg (Nat.cast_nonneg _) hRr.le).trans hu0
  have hu1' : u ≤ 1 := hu1.trans ((div_le_one hRr).mpr (by exact_mod_cast hb))
  have hv0 : (a : ℝ) ≤ u*R := (div_le_iff₀ hRr).mp hu0
  have hv1 : u*R ≤ (b : ℝ) := (le_div_iff₀ hRr).mp hu1
  have T0 := ht (planeAt Q (2*((R : ℤ)*R-(a : ℤ)*a)) (4*(R : ℤ)*a)
      ((R : ℤ)*R+(a : ℤ)*a) p j.val)
    (by simp only [partialTargets, List.mem_append];
        exact Or.inl (Or.inl (planeAt_mem j.isLt hj)))
  have T1 := ht (planeAt Q (2*((R : ℤ)*R-(b : ℤ)*b)) (4*(R : ℤ)*b)
      ((R : ℤ)*R+(b : ℤ)*b) p j.val)
    (by simp only [partialTargets, List.mem_append];
        exact Or.inl (Or.inr (planeAt_mem j.isLt hj)))
  have Tm := ht (planeAt Q (2*((R : ℤ)*R-(a : ℤ)*b)) (2*(R : ℤ)*(a+b))
      ((R : ℤ)*R+(a : ℤ)*b) p j.val)
    (by simp only [partialTargets, List.mem_append]; exact Or.inr (planeAt_mem j.isLt hj))
  have L := fun {x y : ℝ}
      (h0 : 2*((R : ℝ)^2-a*a)*x+4*R*a*y ≤ (R^2+a*a)*Q)
      (h1 : 2*((R : ℝ)^2-b*b)*x+4*R*b*y ≤ (R^2+b*b)*Q)
      (hm : 2*((R : ℝ)^2-a*b)*x+2*R*(a+b)*y ≤ (R^2+a*b)*Q) =>
    lin3 (Q := (Q : ℝ)) (R := (R : ℝ)) (v := u*R) hv0 hv1
      (by rw [pow_two]; linarith) (by rw [pow_two]; linarith) hm
  have eX : ((p.1 : ℝ)/Q-c.1)*Q = p.1-Q*c.1 := by field_simp
  have eY : ((p.2 : ℝ)/Q-c.2)*Q = p.2-Q*c.2 := by field_simp
  fin_cases j <;> simp only [planeAt, InHP] at T0 T1 Tm <;>
    push_cast at T0 T1 Tm
  · exact gval0_le hQr hRr hu0' hu1' (le_of_eq eX) (le_of_eq eY)
      (L (by nlinarith only [T0]) (by nlinarith only [T1]) (by nlinarith only [Tm]))
  · change gval 1 _ _ _ ≤ 0
    rw [gval_one]
    exact gval0_le hQr hRr hu0' hu1' (by rw [neg_mul, eX]) (by rw [neg_mul, eY])
      (L (by nlinarith only [T0]) (by nlinarith only [T1]) (by nlinarith only [Tm]))
  · change gval 2 _ _ _ ≤ 0
    rw [gval_two]
    exact gval0_le hQr hRr hu0' hu1' (le_of_eq eY) (by rw [neg_mul, eX])
      (L (by nlinarith only [T0]) (by nlinarith only [T1]) (by nlinarith only [Tm]))
  · change gval 3 _ _ _ ≤ 0
    rw [gval_three]
    exact gval0_le hQr hRr hu0' hu1' (by rw [neg_mul, eY]) (le_of_eq eX)
      (L (by nlinarith only [T0]) (by nlinarith only [T1]) (by nlinarith only [Tm]))

def offsetSum (Q : ℕ) (A B C : ℤ) (p q : ℕ × ℕ) (k : ℕ) : ℤ :=
  (planeAt Q A B C p k).2.2 + (planeAt Q A B C q (opposite k)).2.2

def gapCheck (Q R a b : ℕ) (p q : ℕ × ℕ) (k : ℕ) : Bool :=
  decide (0 ≤ offsetSum Q (2*((R : ℤ)*R-(a : ℤ)*a)) (4*(R : ℤ)*a)
      ((R : ℤ)*R+(a : ℤ)*a) p q k ∧
    0 ≤ offsetSum Q (2*((R : ℤ)*R-(b : ℤ)*b)) (4*(R : ℤ)*b)
      ((R : ℤ)*R+(b : ℤ)*b) p q k ∧
    0 ≤ offsetSum Q (2*((R : ℤ)*R-(a : ℤ)*b)) (2*(R : ℤ)*(a+b))
      ((R : ℤ)*R+(a : ℤ)*b) p q k)

def deltaX (p q : ℕ × ℕ) (k : Fin 4) : ℝ := match k.val with
  | 0 => (p.1 : ℝ)-q.1
  | 1 => (q.1 : ℝ)-p.1
  | 2 => (p.2 : ℝ)-q.2
  | _ => (q.2 : ℝ)-p.2
def deltaY (p q : ℕ × ℕ) (k : Fin 4) : ℝ := match k.val with
  | 0 => (p.2 : ℝ)-q.2
  | 1 => (q.2 : ℝ)-p.2
  | 2 => (q.1 : ℝ)-p.1
  | _ => (p.1 : ℝ)-q.1

theorem gap_sound {Q R a b : ℕ} (hQ : 0 < Q) (hR : 0 < R)
    (p q : ℕ × ℕ) (k : Fin 4) (h : gapCheck Q R a b p q k.val = true)
    (c : ℝ × ℝ) (u : ℝ) (hu0 : (a : ℝ)/R ≤ u) (hu1 : u ≤ (b : ℝ)/R) :
    gval k ((p.1 : ℝ)/Q-c.1) ((p.2 : ℝ)/Q-c.2) u +
      gval (oppositeSide k) ((q.1 : ℝ)/Q-c.1) ((q.2 : ℝ)/Q-c.2) u ≤ 0 := by
  obtain ⟨h0, h1, hm⟩ := of_decide_eq_true h
  have cast_nonnegative : ∀ x : ℤ, 0 ≤ x → (0 : ℝ) ≤ x := by
    intro x hx
    exact_mod_cast hx
  have h0r := cast_nonnegative _ h0
  have h1r := cast_nonnegative _ h1
  have hmr := cast_nonnegative _ hm
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hv0 : (a : ℝ) ≤ u*R := (div_le_iff₀ hRr).mp hu0
  have hv1 : u*R ≤ (b : ℝ) := (le_div_iff₀ hRr).mp hu1
  have hg : 2*((R : ℝ)^2-(u*R)^2)*deltaX p q k +
      4*R*(u*R)*deltaY p q k ≤ ((R : ℝ)^2+(u*R)^2)*(2*Q) := by
    apply lin3 (Q := (2*(Q : ℝ))) (R := (R : ℝ)) (v := u*R) hv0 hv1
    all_goals
      fin_cases k <;> simp only [offsetSum, opposite,
        planeAt, deltaX, deltaY] at h0r h1r hmr ⊢ <;>
        push_cast at h0r h1r hmr <;> nlinarith only [h0r, h1r, hmr]
  have he : (Q : ℝ)*R^2*(gval k ((p.1 : ℝ)/Q-c.1) ((p.2 : ℝ)/Q-c.2) u +
      gval (oppositeSide k) ((q.1 : ℝ)/Q-c.1) ((q.2 : ℝ)/Q-c.2) u) =
      2*((R : ℝ)^2-(u*R)^2)*deltaX p q k + 4*R*(u*R)*deltaY p q k -
        ((R : ℝ)^2+(u*R)^2)*(2*Q) := by
    fin_cases k <;> simp [oppositeSide, deltaX, deltaY, gval, gc, qeval] <;>
      field_simp <;> ring
  apply nonpos_of_mul_nonpos_right (a := (Q : ℝ)*R^2)
    (by rw [he]; linarith only [hg]) (by positivity)

def check (Q R a b : ℕ) (hs : List Plane) (pairs : List (ℕ × ℕ))
    (p q : ℕ × ℕ) (k : ℕ) : Bool :=
  decide (k < 4) &&
  PolyhedralPoint.listCheck hs (partialTargets Q R a b p k) (partialPairs pairs k) &&
  PolyhedralPoint.listCheck hs (partialTargets Q R a b q (opposite k)) (partialPairs pairs (opposite k)) &&
  gapCheck Q R a b p q k

theorem sound {Q R a b : ℕ} (hQ : 0 < Q) (hR : 0 < R) (hb : b ≤ R)
    {hs : List Plane} {pairs : List (ℕ × ℕ)} {p q : ℕ × ℕ} {k : ℕ}
    (h : check Q R a b hs pairs p q k = true) (c : ℝ × ℝ) (u : ℝ)
    (hhs : ∀ z ∈ hs, InHP Q z c)
    (hu0 : (a : ℝ)/R ≤ u) (hu1 : u ≤ (b : ℝ)/R) :
    ((p.1 : ℝ)/Q, (p.2 : ℝ)/Q) ∈ sq c (2*Real.arctan u) 1 ∨
      ((q.1 : ℝ)/Q, (q.2 : ℝ)/Q) ∈ sq c (2*Real.arctan u) 1 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  let side : Fin 4 := ⟨k, h.1.1.1⟩
  have hp := partial_sound hQ hR hb p c u hu0 hu1
    (PolyhedralPoint.listCheck_sound hs _ _ h.1.1.2 c hhs)
  have hq := partial_sound hQ hR hb q c u hu0 hu1
    (PolyhedralPoint.listCheck_sound hs _ _ h.1.2 c hhs)
  have hsum := gap_sound hQ hR p q side h.2 c u hu0 hu1
  by_cases hside : gval side ((p.1 : ℝ)/Q-c.1) ((p.2 : ℝ)/Q-c.2) u ≤ 0
  · left
    rw [mem_sq_iff_gval]
    intro j
    by_cases hj : j = side
    · simpa [hj] using hside
    · apply hp j
      intro e
      apply hj
      exact Fin.ext e
  · right
    rw [mem_sq_iff_gval]
    intro j
    by_cases hj : j = oppositeSide side
    · subst j
      linarith only [hsum, hside]
    · apply hq j
      intro e
      apply hj
      apply Fin.ext
      simpa [side] using e

#print axioms sound
end SquarePacking.S11Opt.Simplified.ComplementaryPoints
