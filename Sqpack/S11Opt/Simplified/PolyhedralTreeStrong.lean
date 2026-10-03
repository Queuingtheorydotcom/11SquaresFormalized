import Sqpack.S11Opt.Simplified.PolyhedralPoint
import Sqpack.S11Opt.Simplified.EndpointWall
import Sqpack.S11Opt.Simplified.PolyhedralEmpty

namespace SquarePacking.S11Opt.Simplified.PolyhedralTreeStrong
open SquarePacking BoxTree FieldTree PolyhedralPoint

abbrev Facets := List (ℕ × ℕ)

def rectPlanes (xl xh yl yh : ℕ) : List Plane :=
  [(-1, 0, -(xl : ℤ)), (1, 0, xh), (0, -1, -(yl : ℤ)), (0, 1, yh)]

def domain (Q M R : ℕ) (hs : List Plane) (x0 x1 y0 y1 a b : ℕ) : List Plane :=
  let w := wloStrong Q R a b
  hs ++ rectPlanes (max x0 w) (min x1 (M - w)) (max y0 w) (min y1 (M - w))

theorem domain_holds {Q M R x0 x1 y0 y1 a b : ℕ} {hs : List Plane}
    (hQ : 0 < Q) (hR : 0 < R) (hb : b ≤ R) (c : ℝ × ℝ) (u : ℝ)
    (hx0 : (x0 : ℝ) / Q ≤ c.1) (hx1 : c.1 ≤ (x1 : ℝ) / Q)
    (hy0 : (y0 : ℝ) / Q ≤ c.2) (hy1 : c.2 ≤ (y1 : ℝ) / Q)
    (ha : (a : ℝ) / R ≤ u) (hu : u ≤ (b : ℝ) / R)
    (hsub : sq c (2 * Real.arctan u) 1 ⊆ box ((M : ℝ) / Q))
    (hin : ∀ h ∈ hs, InHP Q h c) :
    ∀ h ∈ domain Q M R hs x0 x1 y0 y1 a b, InHP Q h c := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨a1, a2, a3, a4⟩ := (sq_subset_box_iff _ c _).mp hsub
  have hw := wloStrong_le (a := a) hQ hR hb ha hu
  set w := wloStrong Q R a b with hwdef
  have hMW : ((M : ℝ) - w) / Q ≤ ((M - w : ℕ) : ℝ) / Q := by
    apply div_le_div_of_nonneg_right _ hQr.le
    rcases le_total w M with h | h
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le h]
      have : (M : ℝ) ≤ w := by exact_mod_cast h
      simp only [Nat.cast_zero]; linarith
  have he : ((M : ℝ) - w) / Q = (M : ℝ) / Q - (w : ℝ) / Q := by ring
  have lo : ∀ (z0 : ℕ) (z : ℝ), (z0 : ℝ) / Q ≤ z → w / (Q : ℝ) ≤ z →
      ((max z0 w : ℕ) : ℝ) / Q ≤ z := by
    intro z0 z h0 h1
    rcases le_total z0 w with h | h
    · rw [max_eq_right h]; exact h1
    · rw [max_eq_left h]; exact h0
  have hi : ∀ (z1 : ℕ) (z : ℝ), z ≤ (z1 : ℝ) / Q → z ≤ (M : ℝ) / Q - w / Q →
      z ≤ ((min z1 (M - w) : ℕ) : ℝ) / Q := by
    intro z1 z h1 h2
    rcases le_total z1 (M - w) with h | h
    · rw [min_eq_left h]; exact h1
    · rw [min_eq_right h]; linarith
  have cx0 := (div_le_iff₀ hQr).mp (lo x0 c.1 hx0 (by linarith))
  have cx1 := (le_div_iff₀ hQr).mp (hi x1 c.1 hx1 (by linarith))
  have cy0 := (div_le_iff₀ hQr).mp (lo y0 c.2 hy0 (by linarith))
  have cy1 := (le_div_iff₀ hQr).mp (hi y1 c.2 hy1 (by linarith))
  intro h hh
  simp only [domain, List.mem_append] at hh
  rcases hh with hh | hh
  · exact hin h hh
  · simp only [rectPlanes, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl <;>
      simp only [InHP, Int.cast_neg, Int.cast_natCast, Int.cast_one, Int.cast_zero,
        neg_mul, one_mul, zero_mul, zero_add, add_zero] <;> dsimp [w] at * <;> nlinarith

def groupsCheck (Q R a b : ℕ) (hs : List Plane) (pairs : Facets) : List (List (ℕ × ℕ)) → List ℕ → Bool
  | [], [] => true
  | g :: gs, k :: cs =>
    (match g[k]? with
      | some p => listCheck hs (targets Q R a b p) pairs
      | none => false) && groupsCheck Q R a b hs pairs gs cs
  | _, _ => false

theorem groupsCheck_sound {Q R a b : ℕ} (hQ : 0 < Q) (hR : 0 < R) (hb : b ≤ R)
    (hs : List Plane) (pairs : Facets) (c : ℝ × ℝ) (u : ℝ) (hc : ∀ h ∈ hs, InHP Q h c)
    (hu0 : (a : ℝ) / R ≤ u) (hu1 : u ≤ (b : ℝ) / R) :
    ∀ (gs : List (List (ℕ × ℕ))) (cs : List ℕ), groupsCheck Q R a b hs pairs gs cs = true →
      ∀ g ∈ gs, ∃ p ∈ g, ((p.1 : ℝ) / Q, (p.2 : ℝ) / Q) ∈ sq c (2 * Real.arctan u) 1
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [groupsCheck] at h
  | g :: gs, k :: cs, h => by
    simp only [groupsCheck, Bool.and_eq_true] at h
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · cases hk : g'[k]? with
      | none => simp [hk] at h
      | some p =>
        exact ⟨p, List.mem_of_getElem? hk,
          checked_point_mem hQ hR hb hs p pairs (by simpa [hk] using h.1) c u hc hu0 hu1⟩
    · exact groupsCheck_sound hQ hR hb hs pairs c u hc hu0 hu1 gs cs h.2 g' hg'

def leafCheck (Q M R : ℕ) (hs : List Plane) (opts : List (List (List (ℕ × ℕ))))
    (x0 x1 y0 y1 a b i : ℕ) (cs : List ℕ) (pairs : Facets) : Bool :=
  Nat.ble b R && match opts[i]? with
    | some gs => groupsCheck Q R a b (domain Q M R hs x0 x1 y0 y1 a b) pairs gs cs
    | none => false

theorem leaf_sound {Q M R : ℕ} (hQ : 0 < Q) (hR : 0 < R) {hs opts x0 x1 y0 y1 a b i cs pairs}
    (h : leafCheck Q M R hs opts x0 x1 y0 y1 a b i cs pairs = true) :
    CovF Q M R hs opts x0 x1 y0 y1 a b := by
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin
  simp only [leafCheck, Bool.and_eq_true, Nat.ble_eq] at h
  cases hi : opts[i]? with
  | none => simp [hi] at h
  | some gs =>
    refine ⟨gs, List.mem_of_getElem? hi, ?_⟩
    exact groupsCheck_sound hQ hR h.1 _ pairs c u
      (domain_holds hQ hR h.1 c u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin)
      hu0 hu1 gs cs (by simpa [hi] using h.2)

inductive Tree
  | empty3 (ijk : ℕ × ℕ × ℕ)
  | old (t : FT)
  | poly (i : ℕ) (cs : List ℕ) (pairs : Facets)
  | X (l r : Tree)
  | Y (l r : Tree)
  | U (l r : Tree)

def check (Q M R : ℕ) (hs : List Plane) (opts : List (List (List (ℕ × ℕ)))) :
    Tree → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | .empty3 ijk, x0,x1,y0,y1,a,b =>
    Nat.ble b R && PolyhedralEmpty.check (domain Q M R hs x0 x1 y0 y1 a b) ijk
  | .old t, x0,x1,y0,y1,a,b => checkF Q M R hs opts t x0 x1 y0 y1 a b
  | .poly i cs pairs, x0,x1,y0,y1,a,b => leafCheck Q M R hs opts x0 x1 y0 y1 a b i cs pairs
  | .X l r, x0,x1,y0,y1,a,b =>
    check Q M R hs opts l x0 ((x0+x1)/2) y0 y1 a b &&
    check Q M R hs opts r ((x0+x1)/2) x1 y0 y1 a b
  | .Y l r, x0,x1,y0,y1,a,b =>
    check Q M R hs opts l x0 x1 y0 ((y0+y1)/2) a b &&
    check Q M R hs opts r x0 x1 ((y0+y1)/2) y1 a b
  | .U l r, x0,x1,y0,y1,a,b =>
    check Q M R hs opts l x0 x1 y0 y1 a ((a+b)/2) &&
    check Q M R hs opts r x0 x1 y0 y1 ((a+b)/2) b

theorem sound {Q M R : ℕ} (hQ : 0 < Q) (hR : 0 < R) (hs opts) :
    ∀ t x0 x1 y0 y1 a b, check Q M R hs opts t x0 x1 y0 y1 a b = true →
    CovF Q M R hs opts x0 x1 y0 y1 a b := by
  intro t
  induction t with
  | empty3 ijk =>
    intro x0 x1 y0 y1 a b h
    simp only [check, Bool.and_eq_true, Nat.ble_eq] at h
    intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin
    exact (PolyhedralEmpty.check_sound _ ijk h.2 c
      (domain_holds hQ hR h.1 c u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin)).elim
  | old t => intro x0 x1 y0 y1 a b h; exact FieldTree.soundF Q M R hQ hR hs opts t x0 x1 y0 y1 a b h
  | poly i cs pairs => intro x0 x1 y0 y1 a b h; exact leaf_sound hQ hR h
  | X l r il ir =>
    intro x0 x1 y0 y1 a b h
    simp only [check, Bool.and_eq_true] at h
    exact CovF.splitX _ (il _ _ _ _ _ _ h.1) (ir _ _ _ _ _ _ h.2)
  | Y l r il ir =>
    intro x0 x1 y0 y1 a b h
    simp only [check, Bool.and_eq_true] at h
    exact CovF.splitY _ (il _ _ _ _ _ _ h.1) (ir _ _ _ _ _ _ h.2)
  | U l r il ir =>
    intro x0 x1 y0 y1 a b h
    simp only [check, Bool.and_eq_true] at h
    exact CovF.splitU _ (il _ _ _ _ _ _ h.1) (ir _ _ _ _ _ _ h.2)

/-- Twelve facet pairs shared by every point in a leaf: their normals agree. -/
def decPairs (B : ℕ) : ℕ → ℕ → List (ℕ × ℕ) × ℕ
  | 0, n => ([], n)
  | k+1, n =>
    let tail := decPairs B k (n / B / B)
    ((n % B, n / B % B) :: tail.1, tail.2)

def dec (B : ℕ) : ℕ → ℕ → Tree × ℕ
  | 0, n => (.old .wall, n)
  | f+1, n =>
    match n % B with
    | 0 => (.old .wall, n / B)
    | 1 => (.old (.out (n / B % B)), n / B / B)
    | 2 =>
      let i := n / B % B
      let ks := FieldTree.decList B (n / B / B % B) (n / B / B / B)
      (.old (.opt i ks.1), ks.2)
    | 3 =>
      let l := dec B f (n / B); let r := dec B f l.2
      (.X l.1 r.1, r.2)
    | 4 =>
      let l := dec B f (n / B); let r := dec B f l.2
      (.Y l.1 r.1, r.2)
    | 5 =>
      let l := dec B f (n / B); let r := dec B f l.2
      (.U l.1 r.1, r.2)
    | 6 =>
      let i := n / B % B
      let cs := FieldTree.decList B (n / B / B % B) (n / B / B / B)
      let pairs := decPairs B 12 cs.2
      (.poly i cs.1 pairs.1, pairs.2)
    | 7 => (.empty3 (n / B % B, n / B / B % B, n / B / B / B % B), n / B / B / B / B)
    | _ => (.old .wall, n / B)

theorem soundDec (Q M R B fuel n : ℕ) (hQ : 0 < Q) (hR : 0 < R) (hs opts)
    {x0 x1 y0 y1 a b : ℕ}
    (h : check Q M R hs opts (dec B fuel n).1 x0 x1 y0 y1 a b = true) :
    CovF Q M R hs opts x0 x1 y0 y1 a b := sound hQ hR hs opts _ _ _ _ _ _ _ h

#print axioms leaf_sound
#print axioms soundDec
end SquarePacking.S11Opt.Simplified.PolyhedralTreeStrong
