import Sqpack.S11Opt.Simplified.CorrelatedWall
import Sqpack.S11Opt.Simplified.PolyhedralTreeStrong

/-! A checked capture leaf with exact wall/angle correlation, with the original
and endpoint-wall rules retained as fallbacks. Four facet pairs are shared by
all selected points: only the target offsets depend on the point. -/
namespace SquarePacking.S11Opt.Simplified.CorrelatedTree
open SquarePacking BoxTree FieldTree CorrelatedSupport

abbrev Facets := List (ℕ × ℕ)

def groupsCheck (Q R a b : ℕ) (ss : List Source) (pairs : Facets) :
    List (List (ℕ × ℕ)) → List ℕ → Bool
  | [], [] => true
  | g :: gs, k :: cs =>
    (match g[k]? with
      | some p => listCheck (CorrelatedWall.denom R) ss a b
          (CorrelatedWall.targets Q R p) pairs
      | none => false) && groupsCheck Q R a b ss pairs gs cs
  | _, _ => false

theorem groups_sound {Q R a b : ℕ} (hQ : 0 < Q) (hR : 0 < R) (hb : b ≤ R)
    (ss : List Source) (pairs : Facets) (c : ℝ × ℝ) (u : ℝ)
    (hc : ∀ s ∈ ss, Holds (CorrelatedWall.denom R) s (u*R) (Q*c.1) (Q*c.2))
    (hu0 : (a : ℝ)/R ≤ u) (hu1 : u ≤ (b : ℝ)/R) :
    ∀ (gs : List (List (ℕ × ℕ))) (cs : List ℕ), groupsCheck Q R a b ss pairs gs cs = true →
      ∀ g ∈ gs, ∃ p ∈ g, ((p.1 : ℝ)/Q, (p.2 : ℝ)/Q) ∈ sq c (2*Real.arctan u) 1
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [groupsCheck] at h
  | g :: gs, k :: cs, h => by
    simp only [groupsCheck, Bool.and_eq_true] at h
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · cases hk : g'[k]? with
      | none => simp [hk] at h
      | some p =>
        have hRr : (0 : ℝ) < R := by exact_mod_cast hR
        have ha' : ((a : ℚ) : ℝ) ≤ u*R := by
          exact_mod_cast (div_le_iff₀ hRr).mp hu0
        have hb' : u*R ≤ ((b : ℚ) : ℝ) := by
          exact_mod_cast (le_div_iff₀ hRr).mp hu1
        have hu0' : 0 ≤ u := (div_nonneg (Nat.cast_nonneg _) hRr.le).trans hu0
        have hu1' : u ≤ 1 := hu1.trans ((div_le_one hRr).mpr (by exact_mod_cast hb))
        refine ⟨p, List.mem_of_getElem? hk, ?_⟩
        apply CorrelatedWall.targets_mem hQ hR p c u hu0' hu1'
        exact list_sound _ ss _ pairs a b (by simpa [hk] using h.1)
          (u*R) (Q*c.1) (Q*c.2) ha' hb'
          (CorrelatedWall.denom_pos hR _) hc
    · exact groups_sound hQ hR hb ss pairs c u hc hu0 hu1 gs cs h.2 g' hg'

def leafCheck (Q M R : ℕ) (hs : List (ℤ × ℤ × ℤ))
    (opts : List (List (List (ℕ × ℕ)))) (x0 x1 y0 y1 a b i : ℕ)
    (cs : List ℕ) (pairs : Facets) : Bool :=
  Nat.ble b R && match opts[i]? with
    | some gs => groupsCheck Q R a b (CorrelatedWall.domain Q M R hs x0 x1 y0 y1) pairs gs cs
    | none => false

theorem leaf_sound {Q M R : ℕ} (hQ : 0 < Q) (hR : 0 < R)
    {hs opts x0 x1 y0 y1 a b i cs pairs}
    (h : leafCheck Q M R hs opts x0 x1 y0 y1 a b i cs pairs = true) :
    CovF Q M R hs opts x0 x1 y0 y1 a b := by
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin
  simp only [leafCheck, Bool.and_eq_true, Nat.ble_eq] at h
  cases hi : opts[i]? with
  | none => simp [hi] at h
  | some gs =>
    have hRr : (0 : ℝ) < R := by exact_mod_cast hR
    have hu0' : 0 ≤ u := (div_nonneg (Nat.cast_nonneg _) hRr.le).trans hu0
    have hu1' : u ≤ 1 := hu1.trans ((div_le_one hRr).mpr (by exact_mod_cast h.1))
    refine ⟨gs, List.mem_of_getElem? hi, ?_⟩
    exact groups_sound hQ hR h.1 _ pairs c u
      (CorrelatedWall.domain_holds hQ hR c u hx0 hx1 hy0 hy1 hu0' hu1' hsub hin)
      hu0 hu1 gs cs (by simpa [hi] using h.2)

inductive Tree
  | fallback (t : PolyhedralTreeStrong.Tree)
  | correlated (i : ℕ) (cs : List ℕ) (pairs : Facets)
  | X (l r : Tree)
  | Y (l r : Tree)
  | U (l r : Tree)

def check (Q M R : ℕ) (hs : List (ℤ × ℤ × ℤ))
    (opts : List (List (List (ℕ × ℕ)))) : Tree → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | .fallback t, x0,x1,y0,y1,a,b => PolyhedralTreeStrong.check Q M R hs opts t x0 x1 y0 y1 a b
  | .correlated i cs pairs, x0,x1,y0,y1,a,b => leafCheck Q M R hs opts x0 x1 y0 y1 a b i cs pairs
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
    exact PolyhedralTreeStrong.sound hQ hR hs opts t _ _ _ _ _ _ h
  | correlated i cs pairs =>
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
  | 0, n => (.fallback (.old .wall), n)
  | f+1, n =>
    match n % B with
    | 0 => (.fallback (.old .wall), n / B)
    | 1 => (.fallback (.old (.out (n / B % B))), n / B / B)
    | 2 =>
      let i := n / B % B
      let ks := FieldTree.decList B (n / B / B % B) (n / B / B / B)
      (.fallback (.old (.opt i ks.1)), ks.2)
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
      let pairs := PolyhedralTreeStrong.decPairs B 12 cs.2
      (.fallback (.poly i cs.1 pairs.1), pairs.2)
    | 7 =>
      (.fallback (.empty3 (n / B % B, n / B / B % B, n / B / B / B % B)), n / B / B / B / B)
    | 8 =>
      let i := n / B % B
      let cs := FieldTree.decList B (n / B / B % B) (n / B / B / B)
      let pairs := PolyhedralTreeStrong.decPairs B 4 cs.2
      (.correlated i cs.1 pairs.1, pairs.2)
    | _ => (.fallback (.old .wall), n / B)

theorem soundDec (Q M R B fuel n : ℕ) (hQ : 0 < Q) (hR : 0 < R) (hs opts)
    {x0 x1 y0 y1 a b : ℕ}
    (h : check Q M R hs opts (dec B fuel n).1 x0 x1 y0 y1 a b = true) :
    CovF Q M R hs opts x0 x1 y0 y1 a b := sound hQ hR hs opts _ _ _ _ _ _ _ h

#print axioms leaf_sound
#print axioms soundDec
end SquarePacking.S11Opt.Simplified.CorrelatedTree
