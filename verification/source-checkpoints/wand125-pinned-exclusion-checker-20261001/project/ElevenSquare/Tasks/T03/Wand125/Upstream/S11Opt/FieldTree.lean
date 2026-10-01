import ElevenSquare.Tasks.T03.Wand125.Upstream.BoxTree

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# A box-tree checker for "options" certificates (field certificates, ownership)

Pose space `(c_x, c_y, u)`, `u = tan(θ/2) ∈ [0, 1]`, integers over `Q` (centre) and `R` (angle),
container `[0, M/Q]²`.  A *region* is a list of integer half-planes `A·x + B·y ≤ C` (with
`x = Q c_x`, `y = Q c_y`).  An *option* is a list of *groups* of candidate points `(X, Y)` (the
point `(X/Q, Y/Q)`).  The claim `CovF` on a box: every admissible closed unit square whose pose
lies in the box and whose centre lies in the region contains, for some option, a point of every
group of that option.

A leaf is `wall` (the wall-clipped centre rectangle is empty), `out j` (half-plane `j` excludes
the clipped rectangle), or `opt i ks` (option `i`; the `k`-th candidate of each group passes
evand's `ptOk` on the clipped rectangle).  Containment is `BoxTree.ptOk`/`ptOk_mem`, the wall
bound `BoxTree.wlo`/`wlo_le`, unchanged.
-/

namespace SquarePacking.S11Opt.FieldTree

open SquarePacking.BoxTree

/-- Trees.  `X l r`, `Y l r`, `U l r` split at the floor midpoint as in `BoxTree`. -/
inductive FT
  | wall
  | out (j : ℕ)
  | opt (i : ℕ) (ks : List ℕ)
  | X (l r : FT)
  | Y (l r : FT)
  | U (l r : FT)

/-- A half-plane `A x + B y ≤ C` excludes the rectangle `[xl,xh]×[yl,yh]`: its minimum there
exceeds `C`. -/
def outOk (h : ℤ × ℤ × ℤ) (xl xh yl yh : ℕ) : Bool :=
  decide (h.2.2 < h.1 * (if 0 ≤ h.1 then (xl : ℤ) else xh) + h.2.1 * (if 0 ≤ h.2.1 then (yl : ℤ) else yh))

/-- Every group has its chosen candidate certified. -/
def groupsOk (Q R U0 U1 xl xh yl yh : ℕ) : List (List (ℕ × ℕ)) → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | g :: gs, k :: ks =>
    (match g[k]? with
     | some p => ptOk Q R U0 U1 xl xh yl yh p.1 p.2
     | none => false) && groupsOk Q R U0 U1 xl xh yl yh gs ks

/-- The leaf test on the clipped rectangle. -/
def leafOk (Q R U0 U1 : ℕ) (hps : List (ℤ × ℤ × ℤ)) (opts : List (List (List (ℕ × ℕ))))
    (xl xh yl yh : ℕ) : FT → Bool
  | .wall => Nat.blt xh xl || Nat.blt yh yl
  | .out j => match hps[j]? with
    | some h => outOk h xl xh yl yh
    | none => false
  | .opt i ks => match opts[i]? with
    | some o => groupsOk Q R U0 U1 xl xh yl yh o ks
    | none => false
  | _ => false

/-- The tree check on `[x0,x1]×[y0,y1]×[u0,u1]`. -/
def checkF (Q M R : ℕ) (hps : List (ℤ × ℤ × ℤ)) (opts : List (List (List (ℕ × ℕ)))) :
    FT → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | .X l r, x0, x1, y0, y1, u0, u1 =>
    checkF Q M R hps opts l x0 (Nat.div (Nat.add x0 x1) 2) y0 y1 u0 u1 &&
    checkF Q M R hps opts r (Nat.div (Nat.add x0 x1) 2) x1 y0 y1 u0 u1
  | .Y l r, x0, x1, y0, y1, u0, u1 =>
    checkF Q M R hps opts l x0 x1 y0 (Nat.div (Nat.add y0 y1) 2) u0 u1 &&
    checkF Q M R hps opts r x0 x1 (Nat.div (Nat.add y0 y1) 2) y1 u0 u1
  | .U l r, x0, x1, y0, y1, u0, u1 =>
    checkF Q M R hps opts l x0 x1 y0 y1 u0 (Nat.div (Nat.add u0 u1) 2) &&
    checkF Q M R hps opts r x0 x1 y0 y1 (Nat.div (Nat.add u0 u1) 2) u1
  | t, x0, x1, y0, y1, u0, u1 =>
    Nat.ble u1 R &&
    leafOk Q R u0 u1 hps opts (max x0 (wlo Q R u0 u1)) (min x1 (Nat.sub M (wlo Q R u0 u1)))
      (max y0 (wlo Q R u0 u1)) (min y1 (Nat.sub M (wlo Q R u0 u1))) t

/-! ### Compact encoding: a base-`B` digit stream, least significant first.
`0` wall, `1 j` out, `2 i n k₁ … kₙ` opt, `3`/`4`/`5` X/Y/U followed by the two subtrees. -/

def decList (B : ℕ) : ℕ → ℕ → List ℕ × ℕ
  | 0, n => ([], n)
  | k + 1, n => (Nat.mod n B :: (decList B k (Nat.div n B)).1, (decList B k (Nat.div n B)).2)

def dec (B : ℕ) : ℕ → ℕ → FT × ℕ
  | 0, n => (.wall, n)
  | f + 1, n =>
    match Nat.mod n B with
    | 0 => (.wall, Nat.div n B)
    | 1 => (.out (Nat.mod (Nat.div n B) B), Nat.div (Nat.div n B) B)
    | 2 =>
      let n1 := Nat.div n B
      let i := Nat.mod n1 B
      let n2 := Nat.div n1 B
      let k := Nat.mod n2 B
      (.opt i (decList B k (Nat.div n2 B)).1, (decList B k (Nat.div n2 B)).2)
    | 3 => (.X (dec B f (Nat.div n B)).1 (dec B f (dec B f (Nat.div n B)).2).1,
            (dec B f (dec B f (Nat.div n B)).2).2)
    | 4 => (.Y (dec B f (Nat.div n B)).1 (dec B f (dec B f (Nat.div n B)).2).1,
            (dec B f (dec B f (Nat.div n B)).2).2)
    | _ => (.U (dec B f (Nat.div n B)).1 (dec B f (dec B f (Nat.div n B)).2).1,
            (dec B f (dec B f (Nat.div n B)).2).2)

/-! ## Semantics and soundness -/

/-- The centre lies in the half-plane (in grid units). -/
def InHP (Q : ℕ) (h : ℤ × ℤ × ℤ) (c : ℝ × ℝ) : Prop :=
  (h.1 : ℝ) * (Q * c.1) + (h.2.1 : ℝ) * (Q * c.2) ≤ h.2.2

/-- Some option has a captured point in every group. -/
def Good (Q : ℕ) (opts : List (List (List (ℕ × ℕ)))) (c : ℝ × ℝ) (θ : ℝ) : Prop :=
  ∃ o ∈ opts, ∀ g ∈ o, ∃ p ∈ g, ((p.1 : ℝ) / Q, (p.2 : ℝ) / Q) ∈ sq c θ 1

/-- The covering claim on a box. -/
def CovF (Q M R : ℕ) (hps : List (ℤ × ℤ × ℤ)) (opts : List (List (List (ℕ × ℕ))))
    (x0 x1 y0 y1 u0 u1 : ℕ) : Prop :=
  ∀ (c : ℝ × ℝ) (u : ℝ),
    (x0 : ℝ) / Q ≤ c.1 → c.1 ≤ (x1 : ℝ) / Q →
    (y0 : ℝ) / Q ≤ c.2 → c.2 ≤ (y1 : ℝ) / Q →
    (u0 : ℝ) / R ≤ u → u ≤ (u1 : ℝ) / R →
    sq c (2 * Real.arctan u) 1 ⊆ box ((M : ℝ) / Q) →
    (∀ h ∈ hps, InHP Q h c) →
    Good Q opts c (2 * Real.arctan u)

theorem CovF.splitX {Q M R : ℕ} {hps opts} {x0 x1 y0 y1 u0 u1 : ℕ} (m : ℕ)
    (h1 : CovF Q M R hps opts x0 m y0 y1 u0 u1) (h2 : CovF Q M R hps opts m x1 y0 y1 u0 u1) :
    CovF Q M R hps opts x0 x1 y0 y1 u0 u1 := by
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin
  rcases le_total c.1 ((m : ℝ) / Q) with h | h
  · exact h1 c u hx0 h hy0 hy1 hu0 hu1 hsub hin
  · exact h2 c u h hx1 hy0 hy1 hu0 hu1 hsub hin

theorem CovF.splitY {Q M R : ℕ} {hps opts} {x0 x1 y0 y1 u0 u1 : ℕ} (m : ℕ)
    (h1 : CovF Q M R hps opts x0 x1 y0 m u0 u1) (h2 : CovF Q M R hps opts x0 x1 m y1 u0 u1) :
    CovF Q M R hps opts x0 x1 y0 y1 u0 u1 := by
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin
  rcases le_total c.2 ((m : ℝ) / Q) with h | h
  · exact h1 c u hx0 hx1 hy0 h hu0 hu1 hsub hin
  · exact h2 c u hx0 hx1 h hy1 hu0 hu1 hsub hin

theorem CovF.splitU {Q M R : ℕ} {hps opts} {x0 x1 y0 y1 u0 u1 : ℕ} (m : ℕ)
    (h1 : CovF Q M R hps opts x0 x1 y0 y1 u0 m) (h2 : CovF Q M R hps opts x0 x1 y0 y1 m u1) :
    CovF Q M R hps opts x0 x1 y0 y1 u0 u1 := by
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin
  rcases le_total u ((m : ℝ) / R) with h | h
  · exact h1 c u hx0 hx1 hy0 hy1 hu0 h hsub hin
  · exact h2 c u hx0 hx1 hy0 hy1 h hu1 hsub hin

/-- An excluding half-plane: the centre in the clipped rectangle violates it. -/
lemma not_inHP_of_outOk {Q : ℕ} (hQ : 0 < Q) {h : ℤ × ℤ × ℤ} {xl xh yl yh : ℕ}
    (ho : outOk h xl xh yl yh = true) {c : ℝ × ℝ}
    (cx0 : (xl : ℝ) / Q ≤ c.1) (cx1 : c.1 ≤ (xh : ℝ) / Q)
    (cy0 : (yl : ℝ) / Q ≤ c.2) (cy1 : c.2 ≤ (yh : ℝ) / Q) : ¬ InHP Q h c := by
  obtain ⟨A, Bc, C⟩ := h
  simp only [outOk, decide_eq_true_eq] at ho
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have x0' : (xl : ℝ) ≤ Q * c.1 := by rw [div_le_iff hQr] at cx0; linarith
  have x1' : Q * c.1 ≤ (xh : ℝ) := by rw [le_div_iff hQr] at cx1; linarith
  have y0' : (yl : ℝ) ≤ Q * c.2 := by rw [div_le_iff hQr] at cy0; linarith
  have y1' : Q * c.2 ≤ (yh : ℝ) := by rw [le_div_iff hQr] at cy1; linarith
  have hA : (A : ℝ) * (if 0 ≤ A then (xl : ℤ) else xh : ℤ) ≤ A * (Q * c.1) := by
    split_ifs with hA
    · push_cast; exact mul_le_mul_of_nonneg_left x0' (by exact_mod_cast hA)
    · push_cast; exact mul_le_mul_of_nonpos_left x1' (by exact_mod_cast (lt_of_not_ge hA).le)
  have hB : (Bc : ℝ) * (if 0 ≤ Bc then (yl : ℤ) else yh : ℤ) ≤ Bc * (Q * c.2) := by
    split_ifs with hB
    · push_cast; exact mul_le_mul_of_nonneg_left y0' (by exact_mod_cast hB)
    · push_cast; exact mul_le_mul_of_nonpos_left y1' (by exact_mod_cast (lt_of_not_ge hB).le)
  have hor : (C : ℝ) < A * (if 0 ≤ A then (xl : ℤ) else xh : ℤ)
      + Bc * (if 0 ≤ Bc then (yl : ℤ) else yh : ℤ) := by exact_mod_cast ho
  simp only [InHP, not_le]
  linarith

/-- The chosen candidates are captured. -/
lemma groupsOk_sound {Q R U0 U1 xl xh yl yh : ℕ} (hQ : 0 < Q) (hR : 0 < R) (hU : U0 ≤ U1)
    (hU1 : U1 ≤ R) {c : ℝ × ℝ} {u : ℝ}
    (hu0 : (U0 : ℝ) / R ≤ u) (hu1 : u ≤ (U1 : ℝ) / R)
    (cx0 : (xl : ℝ) / Q ≤ c.1) (cx1 : c.1 ≤ (xh : ℝ) / Q)
    (cy0 : (yl : ℝ) / Q ≤ c.2) (cy1 : c.2 ≤ (yh : ℝ) / Q) :
    ∀ (o : List (List (ℕ × ℕ))) (ks : List ℕ), groupsOk Q R U0 U1 xl xh yl yh o ks = true →
      ∀ g ∈ o, ∃ p ∈ g, ((p.1 : ℝ) / Q, (p.2 : ℝ) / Q) ∈ sq c (2 * Real.arctan u) 1
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [groupsOk] at h
  | g :: gs, k :: ks, h => by
    simp only [groupsOk, Bool.and_eq_true] at h
    obtain ⟨hg, hgs⟩ := h
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · cases hk : g'[k]? with
      | none => simp [hk] at hg
      | some p =>
        simp only [hk] at hg
        exact ⟨p, List.getElem?_mem hk,
          ptOk_mem hQ hR hU hU1 hg c u hu0 hu1 cx0 cx1 cy0 cy1⟩
    · exact groupsOk_sound hQ hR hU hU1 hu0 hu1 cx0 cx1 cy0 cy1 gs ks hgs g' hg'

/-- **Soundness of a leaf.** -/
theorem leaf_sound {Q M R : ℕ} (hQ : 0 < Q) (hR : 0 < R) {hps opts} {x0 x1 y0 y1 u0 u1 : ℕ}
    (t : FT) (ht : ∀ l r, t ≠ .X l r ∧ t ≠ .Y l r ∧ t ≠ .U l r)
    (h : checkF Q M R hps opts t x0 x1 y0 y1 u0 u1 = true) :
    CovF Q M R hps opts x0 x1 y0 y1 u0 u1 := by
  intro cc u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin
  have h' : (Nat.ble u1 R && leafOk Q R u0 u1 hps opts (max x0 (wlo Q R u0 u1))
      (min x1 (Nat.sub M (wlo Q R u0 u1))) (max y0 (wlo Q R u0 u1))
      (min y1 (Nat.sub M (wlo Q R u0 u1))) t) = true := by
    cases t with
    | X l r => exact absurd rfl (ht l r).1
    | Y l r => exact absurd rfl (ht l r).2.1
    | U l r => exact absurd rfl (ht l r).2.2
    | _ => simpa [checkF] using h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h'
  obtain ⟨hu1R, h⟩ := h'
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hU : u0 ≤ u1 := by
    have : (u0 : ℝ) / R ≤ (u1 : ℝ) / R := le_trans hu0 hu1
    rw [div_le_div_right hRr] at this
    exact_mod_cast this
  obtain ⟨a1, a2, a3, a4⟩ := (sq_subset_box_iff _ cc _).mp hsub
  have hWL := wlo_le (U0 := u0) hQ hR hu1R hu0 hu1
  set WL := wlo Q R u0 u1 with hWLdef
  have hMWL : ((M : ℝ) - WL) / Q ≤ ((Nat.sub M WL : ℕ) : ℝ) / Q := by
    apply div_le_div_of_nonneg_right _ hQr.le
    rw [nat_sub_eq]
    rcases le_total WL M with h' | h'
    · rw [Nat.cast_sub h']
    · rw [Nat.sub_eq_zero_of_le h']
      have : (M : ℝ) ≤ WL := by exact_mod_cast h'
      simp only [Nat.cast_zero]; linarith
  have eMW : ((M : ℝ) - WL) / Q = (M : ℝ) / Q - (WL : ℝ) / Q := by ring
  have lo : ∀ (z0 : ℕ) (z : ℝ), (z0 : ℝ) / Q ≤ z → WL / (Q : ℝ) ≤ z →
      ((max z0 WL : ℕ) : ℝ) / Q ≤ z := by
    intro z0 z h1 h2
    rcases le_total z0 WL with h' | h'
    · rw [max_eq_right h']; exact h2
    · rw [max_eq_left h']; exact h1
  have hi : ∀ (z1 : ℕ) (z : ℝ), z ≤ (z1 : ℝ) / Q → z ≤ (M : ℝ) / Q - WL / Q →
      z ≤ ((min z1 (Nat.sub M WL) : ℕ) : ℝ) / Q := by
    intro z1 z h1 h2
    rcases le_total z1 (Nat.sub M WL) with h' | h'
    · rw [min_eq_left h']; exact h1
    · rw [min_eq_right h']; linarith
  have cx0 := lo x0 cc.1 hx0 (by linarith)
  have cx1 := hi x1 cc.1 hx1 (by linarith)
  have cy0 := lo y0 cc.2 hy0 (by linarith)
  have cy1 := hi y1 cc.2 hy1 (by linarith)
  have hxle : max x0 WL ≤ min x1 (Nat.sub M WL) := by
    have : ((max x0 WL : ℕ) : ℝ) ≤ ((min x1 (Nat.sub M WL) : ℕ) : ℝ) := by
      have := le_trans cx0 cx1
      rwa [div_le_div_right hQr] at this
    exact_mod_cast this
  have hyle : max y0 WL ≤ min y1 (Nat.sub M WL) := by
    have : ((max y0 WL : ℕ) : ℝ) ≤ ((min y1 (Nat.sub M WL) : ℕ) : ℝ) := by
      have := le_trans cy0 cy1
      rwa [div_le_div_right hQr] at this
    exact_mod_cast this
  cases t with
  | wall =>
    simp only [leafOk, Bool.or_eq_true, Nat.blt_eq] at h
    omega
  | out j =>
    simp only [leafOk] at h
    cases hj : hps[j]? with
    | none => simp [hj] at h
    | some hp =>
      simp only [hj] at h
      exact absurd (hin hp (List.getElem?_mem hj))
        (not_inHP_of_outOk hQ h cx0 cx1 cy0 cy1)
  | opt i ks =>
    simp only [leafOk] at h
    cases hi' : opts[i]? with
    | none => simp [hi'] at h
    | some o =>
      simp only [hi'] at h
      exact ⟨o, List.getElem?_mem hi',
        groupsOk_sound hQ hR hU hu1R hu0 hu1 cx0 cx1 cy0 cy1 o ks h⟩
  | X l r => exact absurd rfl (ht l r).1
  | Y l r => exact absurd rfl (ht l r).2.1
  | U l r => exact absurd rfl (ht l r).2.2

/-- **Soundness of the tree check.** -/
theorem soundF (Q M R : ℕ) (hQ : 0 < Q) (hR : 0 < R) (hps : List (ℤ × ℤ × ℤ))
    (opts : List (List (List (ℕ × ℕ)))) :
    ∀ (t : FT) (x0 x1 y0 y1 u0 u1 : ℕ), checkF Q M R hps opts t x0 x1 y0 y1 u0 u1 = true →
      CovF Q M R hps opts x0 x1 y0 y1 u0 u1 := by
  intro t
  induction t with
  | wall => intro x0 x1 y0 y1 u0 u1 h; exact leaf_sound hQ hR .wall (by simp) h
  | out j => intro x0 x1 y0 y1 u0 u1 h; exact leaf_sound hQ hR (.out j) (by simp) h
  | opt i ks => intro x0 x1 y0 y1 u0 u1 h; exact leaf_sound hQ hR (.opt i ks) (by simp) h
  | X l r ihl ihr =>
    intro x0 x1 y0 y1 u0 u1 h
    simp only [checkF, Bool.and_eq_true] at h
    exact CovF.splitX _ (ihl _ _ _ _ _ _ h.1) (ihr _ _ _ _ _ _ h.2)
  | Y l r ihl ihr =>
    intro x0 x1 y0 y1 u0 u1 h
    simp only [checkF, Bool.and_eq_true] at h
    exact CovF.splitY _ (ihl _ _ _ _ _ _ h.1) (ihr _ _ _ _ _ _ h.2)
  | U l r ihl ihr =>
    intro x0 x1 y0 y1 u0 u1 h
    simp only [checkF, Bool.and_eq_true] at h
    exact CovF.splitU _ (ihl _ _ _ _ _ _ h.1) (ihr _ _ _ _ _ _ h.2)

/-- The encoded form: any digit stream that decodes to an accepted tree proves the claim. -/
theorem soundDec (Q M R B fuel n : ℕ) (hQ : 0 < Q) (hR : 0 < R) (hps : List (ℤ × ℤ × ℤ))
    (opts : List (List (List (ℕ × ℕ)))) {x0 x1 y0 y1 u0 u1 : ℕ}
    (h : checkF Q M R hps opts (dec B fuel n).1 x0 x1 y0 y1 u0 u1 = true) :
    CovF Q M R hps opts x0 x1 y0 y1 u0 u1 :=
  soundF Q M R hQ hR hps opts _ _ _ _ _ _ _ h

end SquarePacking.S11Opt.FieldTree
