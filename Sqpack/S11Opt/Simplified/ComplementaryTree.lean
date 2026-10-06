import Sqpack.S11Opt.Simplified.ComplementaryDistance
import Sqpack.S11Opt.Simplified.CorrelatedTree

/-! An option may have one unresolved group. If two such options have
complementary capture facets, one of their exceptional points is necessarily
captured. This proves the original disjunction without approximating its
rotating boundary by axis-aligned subdivisions. -/
namespace SquarePacking.S11Opt.Simplified.ComplementaryTree
open SquarePacking BoxTree FieldTree PolyhedralPoint
abbrev Facets := List (ℕ × ℕ)

def chosen : List (List (ℕ × ℕ)) → List ℕ → ℕ → Option (ℕ × ℕ)
  | g :: _, k :: _, 0 => g[k]?
  | _ :: gs, _ :: cs, j+1 => chosen gs cs j
  | _, _, _ => none

def groupsExceptCheck (Q R a b : ℕ) (hs : List Plane) (pairs : Facets) :
    List (List (ℕ × ℕ)) → List ℕ → ℕ → Bool
  | _ :: gs, _ :: cs, 0 => PolyhedralTreeStrong.groupsCheck Q R a b hs pairs gs cs
  | g :: gs, k :: cs, j+1 =>
    PolyhedralTreeStrong.groupsCheck Q R a b hs pairs [g] [k] &&
      groupsExceptCheck Q R a b hs pairs gs cs j
  | _, _, _ => false

theorem groupsExcept_sound {Q R a b : ℕ} (hQ : 0 < Q) (hR : 0 < R) (hb : b ≤ R)
    (hs : List Plane) (pairs : Facets) (c : ℝ × ℝ) (u : ℝ)
    (hc : ∀ h ∈ hs, InHP Q h c) (hu0 : (a : ℝ)/R ≤ u) (hu1 : u ≤ (b : ℝ)/R)
    (gs : List (List (ℕ × ℕ))) (cs : List ℕ) (j : ℕ)
    (h : groupsExceptCheck Q R a b hs pairs gs cs j = true)
    (p : ℕ × ℕ) (hp : chosen gs cs j = some p)
    (hin : ((p.1 : ℝ)/Q,(p.2 : ℝ)/Q) ∈ sq c (2*Real.arctan u) 1) :
    ∀ g ∈ gs, ∃ p ∈ g, ((p.1 : ℝ)/Q,(p.2 : ℝ)/Q) ∈ sq c (2*Real.arctan u) 1 := by
  induction gs generalizing cs j with
  | nil => simp
  | cons g gs ih =>
    cases cs with
    | nil => simp [groupsExceptCheck] at h
    | cons k cs =>
      cases j with
      | zero =>
        simp only [chosen] at hp
        intro g' hg'
        rcases List.mem_cons.mp hg' with rfl | hg'
        · exact ⟨p, List.mem_of_getElem? hp, hin⟩
        · exact PolyhedralTreeStrong.groupsCheck_sound hQ hR hb hs pairs c u hc
            hu0 hu1 gs cs h g' hg'
      | succ j =>
        simp only [groupsExceptCheck, Bool.and_eq_true] at h
        intro g' hg'
        rcases List.mem_cons.mp hg' with rfl | hg'
        · exact PolyhedralTreeStrong.groupsCheck_sound hQ hR hb hs pairs c u hc
            hu0 hu1 [_] [k] h.1 _ (by simp)
        · exact ih cs j h.2 hp g' hg'

def leafCheck (Q M R : ℕ) (hs : List Plane) (opts : List (List (List (ℕ × ℕ))))
    (x0 x1 y0 y1 a b i j gi gj k : ℕ) (ci cj : List ℕ) (pairs : Facets) : Bool :=
  Nat.ble b R && match opts[i]?, opts[j]? with
  | some oi, some oj =>
    match chosen oi ci gi, chosen oj cj gj with
    | some p, some q =>
      let ds := PolyhedralTreeStrong.domain Q M R hs x0 x1 y0 y1 a b
      ComplementaryPoints.checkWithDistance Q R a b ds pairs p q k &&
      groupsExceptCheck Q R a b ds pairs oi ci gi &&
      groupsExceptCheck Q R a b ds pairs oj cj gj
    | _, _ => false
  | _, _ => false

theorem leaf_sound {Q M R : ℕ} (hQ : 0 < Q) (hR : 0 < R)
    {hs opts x0 x1 y0 y1 a b i j gi gj k ci cj pairs}
    (h : leafCheck Q M R hs opts x0 x1 y0 y1 a b i j gi gj k ci cj pairs = true) :
    CovF Q M R hs opts x0 x1 y0 y1 a b := by
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin
  simp only [leafCheck, Bool.and_eq_true, Nat.ble_eq] at h
  cases hi : opts[i]? with
  | none => simp [hi] at h
  | some oi =>
    cases hj : opts[j]? with
    | none => simp [hi, hj] at h
    | some oj =>
      cases hp : chosen oi ci gi with
      | none => simp [hi, hj, hp] at h
      | some p =>
        cases hq : chosen oj cj gj with
        | none => simp [hi, hj, hp, hq] at h
        | some q =>
          have hh := h.2
          simp only [hi, hj, hp, hq, Bool.and_eq_true] at hh
          have hd := PolyhedralTreeStrong.domain_holds hQ hR h.1 c u
            hx0 hx1 hy0 hy1 hu0 hu1 hsub hin
          rcases ComplementaryPoints.soundWithDistance hQ hR h.1 hh.1.1 c u hd hu0 hu1 with hpin | hqin
          · exact ⟨oi, List.mem_of_getElem? hi,
              groupsExcept_sound hQ hR h.1 _ pairs c u hd hu0 hu1 oi ci gi hh.1.2 p hp hpin⟩
          · exact ⟨oj, List.mem_of_getElem? hj,
              groupsExcept_sound hQ hR h.1 _ pairs c u hd hu0 hu1 oj cj gj hh.2 q hq hqin⟩

inductive Tree
  | fallback (t : CorrelatedTree.Tree)
  | complementary (i j gi gj k : ℕ) (ci cj : List ℕ) (pairs : Facets)
  | X (l r : Tree)
  | Y (l r : Tree)
  | U (l r : Tree)

def check (Q M R : ℕ) (hs : List Plane) (opts : List (List (List (ℕ × ℕ)))) :
    Tree → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | .fallback t, x0,x1,y0,y1,a,b => CorrelatedTree.check Q M R hs opts t x0 x1 y0 y1 a b
  | .complementary i j gi gj k ci cj pairs, x0,x1,y0,y1,a,b =>
    leafCheck Q M R hs opts x0 x1 y0 y1 a b i j gi gj k ci cj pairs
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
    exact CorrelatedTree.sound hQ hR hs opts t _ _ _ _ _ _ h
  | complementary i j gi gj k ci cj pairs =>
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
  | 0, n => (.fallback (.fallback (.old .wall)), n)
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
    | 9 =>
      let i := n / B % B
      let j := n / B / B % B
      let gi := n / B / B / B % B
      let gj := n / B / B / B / B % B
      let k := n / B / B / B / B / B % B
      let rest := n / B / B / B / B / B / B
      let ci := FieldTree.decList B (rest % B) (rest / B)
      let cj := FieldTree.decList B (ci.2 % B) (ci.2 / B)
      let pairs := PolyhedralTreeStrong.decPairs B 12 cj.2
      (.complementary i j gi gj k ci.1 cj.1 pairs.1, pairs.2)
    | _ =>
      let t := CorrelatedTree.dec B (f+1) n
      (.fallback t.1, t.2)

theorem soundDec (Q M R B fuel n : ℕ) (hQ : 0 < Q) (hR : 0 < R) (hs opts)
    {x0 x1 y0 y1 a b : ℕ}
    (h : check Q M R hs opts (dec B fuel n).1 x0 x1 y0 y1 a b = true) :
    CovF Q M R hs opts x0 x1 y0 y1 a b := sound hQ hR hs opts _ _ _ _ _ _ _ h

#print axioms leaf_sound
#print axioms soundDec
end SquarePacking.S11Opt.Simplified.ComplementaryTree
