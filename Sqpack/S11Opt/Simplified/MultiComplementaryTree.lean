import Sqpack.S11Opt.Simplified.ComplementaryTree

/-! Whole-option complementary capture. Choose one point from each group in
both options. If every cross pair has at least one captured point, all chosen
points of one option are captured. The geometry is the already proved
complementary-point rule; the new step is finite distributivity. -/
namespace SquarePacking.S11Opt.Simplified.MultiComplementaryTree
open SquarePacking BoxTree FieldTree PolyhedralPoint
abbrev Facets := List (ℕ × ℕ)

def pickPoints : List (List (ℕ × ℕ)) → List ℕ → Option (List (ℕ × ℕ))
  | [], [] => some []
  | g :: gs, k :: ks =>
    match g[k]?, pickPoints gs ks with
    | some p, some ps => some (p :: ps)
    | _, _ => none
  | _, _ => none

theorem pickPoints_sound (P : (ℕ × ℕ) → Prop)
    (gs : List (List (ℕ × ℕ))) (ks : List ℕ) (ps : List (ℕ × ℕ))
    (h : pickPoints gs ks = some ps) (hp : ∀ p ∈ ps, P p) :
    ∀ g ∈ gs, ∃ p ∈ g, P p := by
  induction gs generalizing ks ps with
  | nil => simp
  | cons g gs ih =>
    cases ks with
    | nil => simp [pickPoints] at h
    | cons k ks =>
      cases hk : g[k]? with
      | none => simp [pickPoints, hk] at h
      | some p =>
        cases ht : pickPoints gs ks with
        | none => simp [pickPoints, hk, ht] at h
        | some tail =>
          have he : p :: tail = ps := by simpa [pickPoints, hk, ht] using h
          subst ps
          intro g' hg'
          rcases List.mem_cons.mp hg' with rfl | hg'
          · exact ⟨p, List.mem_of_getElem? hk, hp p (by simp)⟩
          · exact ih ks tail ht (fun q hq => hp q (by simp [hq])) g' hg'

theorem all_or_all {α : Type*} (P : α → Prop) (ps qs : List α)
    (h : ∀ p ∈ ps, ∀ q ∈ qs, P p ∨ P q) :
    (∀ p ∈ ps, P p) ∨ (∀ q ∈ qs, P q) := by
  classical
  by_cases hp : ∀ p ∈ ps, P p
  · exact Or.inl hp
  · right
    intro q hq
    by_contra hnq
    exact hp (fun p hmem => (h p hmem q hq).resolve_right hnq)

def pointPairCheck (Q R a b : ℕ) (hs : List Plane) (pairs : Facets)
    (p q : ℕ × ℕ) (k : ℕ) : Bool :=
  listCheck hs (targets Q R a b p) pairs ||
  listCheck hs (targets Q R a b q) pairs ||
  ComplementaryPoints.checkWithDistance Q R a b hs pairs p q k

theorem pointPair_sound {Q R a b : ℕ} (hQ : 0 < Q) (hR : 0 < R) (hb : b ≤ R)
    {hs pairs p q k} (h : pointPairCheck Q R a b hs pairs p q k = true)
    (c : ℝ × ℝ) (u : ℝ) (hc : ∀ h ∈ hs, InHP Q h c)
    (hu0 : (a : ℝ) / R ≤ u) (hu1 : u ≤ (b : ℝ) / R) :
    ((p.1 : ℝ) / Q, (p.2 : ℝ) / Q) ∈ sq c (2 * Real.arctan u) 1 ∨
    ((q.1 : ℝ) / Q, (q.2 : ℝ) / Q) ∈ sq c (2 * Real.arctan u) 1 := by
  simp only [pointPairCheck, Bool.or_eq_true] at h
  rcases h with (hp | hq) | hpq
  · exact Or.inl (checked_point_mem hQ hR hb hs p pairs hp c u hc hu0 hu1)
  · exact Or.inr (checked_point_mem hQ hR hb hs q pairs hq c u hc hu0 hu1)
  · exact ComplementaryPoints.soundWithDistance hQ hR hb hpq c u hc hu0 hu1

def leafCheck (Q M R : ℕ) (hs : List Plane) (opts : List (List (List (ℕ × ℕ))))
    (x0 x1 y0 y1 a b i j k : ℕ) (ci cj : List ℕ) (pairs : Facets) : Bool :=
  Nat.ble b R && match opts[i]?, opts[j]? with
  | some oi, some oj =>
    match pickPoints oi ci, pickPoints oj cj with
    | some ps, some qs =>
      let ds := PolyhedralTreeStrong.domain Q M R hs x0 x1 y0 y1 a b
      ps.all (fun p => qs.all (fun q => pointPairCheck Q R a b ds pairs p q k))
    | _, _ => false
  | _, _ => false

theorem leaf_sound {Q M R : ℕ} (hQ : 0 < Q) (hR : 0 < R)
    {hs opts x0 x1 y0 y1 a b i j k ci cj pairs}
    (h : leafCheck Q M R hs opts x0 x1 y0 y1 a b i j k ci cj pairs = true) :
    CovF Q M R hs opts x0 x1 y0 y1 a b := by
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin
  simp only [leafCheck, Bool.and_eq_true, Nat.ble_eq] at h
  cases hi : opts[i]? with
  | none => simp [hi] at h
  | some oi =>
    cases hj : opts[j]? with
    | none => simp [hi, hj] at h
    | some oj =>
      cases hp : pickPoints oi ci with
      | none => simp [hi, hj, hp] at h
      | some ps =>
        cases hq : pickPoints oj cj with
        | none => simp [hi, hj, hp, hq] at h
        | some qs =>
          have hh := h.2
          simp only [hi, hj, hp, hq, List.all_eq_true] at hh
          have hd := PolyhedralTreeStrong.domain_holds hQ hR h.1 c u
            hx0 hx1 hy0 hy1 hu0 hu1 hsub hin
          let P := fun p : ℕ × ℕ =>
            ((p.1 : ℝ) / Q, (p.2 : ℝ) / Q) ∈ sq c (2 * Real.arctan u) 1
          have hpair : ∀ p ∈ ps, ∀ q ∈ qs, P p ∨ P q := by
            intro p hpm q hqm
            exact pointPair_sound hQ hR h.1 (hh p hpm q hqm) c u hd hu0 hu1
          rcases all_or_all P ps qs hpair with hps | hqs
          · exact ⟨oi, List.mem_of_getElem? hi, pickPoints_sound P oi ci ps hp hps⟩
          · exact ⟨oj, List.mem_of_getElem? hj, pickPoints_sound P oj cj qs hq hqs⟩

inductive Tree
  | fallback (t : ComplementaryTree.Tree)
  | complementary (i j k : ℕ) (ci cj : List ℕ) (pairs : Facets)
  | X (l r : Tree)
  | Y (l r : Tree)
  | U (l r : Tree)

def check (Q M R : ℕ) (hs : List Plane) (opts : List (List (List (ℕ × ℕ)))) :
    Tree → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | .fallback t, x0,x1,y0,y1,a,b => ComplementaryTree.check Q M R hs opts t x0 x1 y0 y1 a b
  | .complementary i j k ci cj pairs, x0,x1,y0,y1,a,b =>
    leafCheck Q M R hs opts x0 x1 y0 y1 a b i j k ci cj pairs
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
  | fallback t =>
    intro x0 x1 y0 y1 a b h
    exact ComplementaryTree.sound hQ hR hs opts t _ _ _ _ _ _ h
  | complementary i j k ci cj pairs =>
    intro x0 x1 y0 y1 a b h; exact leaf_sound hQ hR h
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

def dec (B : ℕ) : ℕ → ℕ → Tree × ℕ
  | 0, n => (.fallback (.fallback (.fallback (.old .wall))), n)
  | f+1, n =>
    match n % B with
    | 3 =>
      let l := dec B f (n / B); let r := dec B f l.2
      (.X l.1 r.1, r.2)
    | 4 =>
      let l := dec B f (n / B); let r := dec B f l.2
      (.Y l.1 r.1, r.2)
    | 5 =>
      let l := dec B f (n / B); let r := dec B f l.2
      (.U l.1 r.1, r.2)
    | 12 =>
      let i := n / B % B
      let j := n / B / B % B
      let k := n / B / B / B % B
      let rest := n / B / B / B / B
      let ci := FieldTree.decList B (rest % B) (rest / B)
      let cj := FieldTree.decList B (ci.2 % B) (ci.2 / B)
      let pairs := PolyhedralTreeStrong.decPairs B 12 cj.2
      (.complementary i j k ci.1 cj.1 pairs.1, pairs.2)
    | _ =>
      let t := ComplementaryTree.dec B (f+1) n
      (.fallback t.1, t.2)

theorem soundDec (Q M R B fuel n : ℕ) (hQ : 0 < Q) (hR : 0 < R) (hs opts)
    {x0 x1 y0 y1 a b : ℕ}
    (h : check Q M R hs opts (dec B fuel n).1 x0 x1 y0 y1 a b = true) :
    CovF Q M R hs opts x0 x1 y0 y1 a b := sound hQ hR hs opts _ _ _ _ _ _ _ h

#print axioms leaf_sound
#print axioms soundDec
end SquarePacking.S11Opt.Simplified.MultiComplementaryTree
