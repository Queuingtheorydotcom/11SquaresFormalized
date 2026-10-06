import ElevenSquare.Tasks.T07.Ext.Check
import ElevenSquare.Tasks.T07.Ext.FastComb
import ElevenSquare.Tasks.T07.Ext.IntegerConvex

/-! Isolated checker variants for controlled runtime comparisons. All tree
constructors, closed branches, comparison order and auxiliary checks match the
production checker. Only the three named arithmetic components can vary.
Every configured variant is proved equal to the production Boolean result. -/
namespace ElevenSquare.Tasks.T07.Ext.RuntimeCheck
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07

structure Components where
  empty : Polygon → List ℚ → Bool
  subset : Polygon → Polygon → List (List ℚ) → Bool
  convex : List QPoint → Bool

structure Agrees (K : Components) : Prop where
  empty_eq : ∀ P mu, K.empty P mu = emptyB P mu
  subset_eq : ∀ P Q mus, K.subset P Q mus = subsetB P Q mus
  convex_eq : ∀ V, K.convex V = convexF V

def subsetFastB (P Q : Polygon) (mus : List (List ℚ)) : Bool :=
  (mus.length == Q.length) &&
    ((Q.zip mus).all fun gm => FastComb.impliesFastB P gm.2 gm.1)

theorem subsetFastB_eq_subsetB (P Q : Polygon) (mus : List (List ℚ)) :
    subsetFastB P Q mus = subsetB P Q mus := by
  simp only [subsetFastB, subsetB, FastComb.impliesFastB_eq_impliesB]

def components (useFastSum useIntegerConvex : Bool) : Components where
  empty := if useFastSum then FastComb.emptyFastB else emptyB
  subset := if useFastSum then subsetFastB else subsetB
  convex := if useIntegerConvex then convexIntF else convexF

theorem components_agree (useFastSum useIntegerConvex : Bool) :
    Agrees (components useFastSum useIntegerConvex) := by
  constructor
  · intro P mu
    cases useFastSum <;> simp [components, FastComb.emptyFastB_eq_emptyB]
  · intro P Q mus
    cases useFastSum <;> simp [components, subsetFastB_eq_subsetB]
  · intro V
    cases useIntegerConvex <;> simp [components, convexIntF_eq_convexF]

def original : Components := components false false
def fastSum : Components := components true false
def integerConvex : Components := components false true
def combined : Components := components true true

theorem original_agrees : Agrees original := components_agree false false
theorem fastSum_agrees : Agrees fastSum := components_agree true false
theorem integerConvex_agrees : Agrees integerConvex := components_agree false true
theorem combined_agrees : Agrees combined := components_agree true true

def treeCheck (K : Components) (C : Ctx) : Polygon → CTree → Bool
  | P, .empty mu => K.empty P mu
  | P, .keep m mus => decide (m < C.rs.length) &&
      K.subset P (C.rs.getD m ⟨0, 0, []⟩).centers mus &&
      decide ((C.rs.getD m ⟨0, 0, []⟩).lo ≤ C.a) && decide (C.b ≤ (C.rs.getD m ⟨0, 0, []⟩).hi)
  | P, .forbid j T => decide (j < 11) && decide (j ≠ C.i.val) && T.check (ownedOf C.s j) C.core P
  | P, .forbidHull j corners mus =>
      decide (j < 11) && decide (j ≠ C.i.val) &&
      (corners.all fun ab => decide (ab.1 < (ownedOf C.s j).length ∧ ab.2 < C.core.length)) &&
      K.convex (diffs (ownedOf C.s j) C.core corners) &&
      K.subset P (edgesF (diffs (ownedOf C.s j) C.core corners)) mus
  | P, .collide k mus => decide (k < C.regs.length) &&
      convexZF (C.regs.getD k ⟨0, [], []⟩).verts &&
        K.subset P (edgesF ((C.regs.getD k ⟨0, [], []⟩).verts.map toQ)) mus
  | P, .split l le ge => treeCheck K C (l :: P) le && treeCheck K C (negH l :: P) ge

theorem treeCheck_eq (K : Components) (hK : Agrees K) (C : Ctx)
    (P : Polygon) (tree : CTree) : treeCheck K C P tree = CTree.check C P tree := by
  induction tree generalizing P with
  | empty mu => exact hK.empty_eq P mu
  | keep m mus => simp only [treeCheck, CTree.check, hK.subset_eq]
  | forbid j T => rfl
  | forbidHull j corners mus =>
    simp only [treeCheck, CTree.check, hK.convex_eq, hK.subset_eq]
  | collide k mus => simp only [treeCheck, CTree.check, hK.subset_eq]
  | split l le ge ihle ihge => simp only [treeCheck, CTree.check, ihle, ihge]

def subCheck (K : Components) (s : PoseState) (i : Owner) (rs : List PoseRow)
    (pcov : ℕ → List (List PartnerPiece)) (r : PoseRow) (u : Sub) : Bool :=
  (u.cuts.all fun k => k.check (s.owned i) u.a u.b) && wallB u.wall u.a u.b &&
    (u.core.all (coreVB u.a u.b)) && ((u.ccore.map toQ).all (coreVB u.a u.b)) &&
    (u.regs.all (CReg.check s i u.ccore pcov)) &&
    treeCheck K ⟨s, i, rs, u.core, u.a, u.b, u.regs⟩ (subPoly r u) u.tree

theorem subCheck_eq (K : Components) (hK : Agrees K) (s : PoseState) (i : Owner)
    (rs : List PoseRow) (pcov : ℕ → List (List PartnerPiece)) (r : PoseRow) (u : Sub) :
    subCheck K s i rs pcov r u = Sub.check s i rs pcov r u := by
  simp only [subCheck, Sub.check, treeCheck_eq K hK]

def rowCheck (K : Components) (s : PoseState) (i : Owner) (rs : List PoseRow)
    (pcov : ℕ → List (List PartnerPiece)) (r : PoseRow) (subs : List Sub) : Bool :=
  coversB r.hi r.lo (subs.map fun u => (u.a, u.b)) &&
    subs.all (subCheck K s i rs pcov r)

theorem rowCheck_eq (K : Components) (hK : Agrees K) (s : PoseState) (i : Owner)
    (rs : List PoseRow) (pcov : ℕ → List (List PartnerPiece)) (r : PoseRow)
    (subs : List Sub) : rowCheck K s i rs pcov r subs = rowB s i rs pcov r subs := by
  have he : subCheck K s i rs pcov r = Sub.check s i rs pcov r :=
    funext (fun u => subCheck_eq K hK s i rs pcov r u)
  unfold rowCheck rowB
  rw [he]

def stepCheck (K : Components) (s : PoseState) (i : Owner) (rs : List PoseRow)
    (pcov : ℕ → List (List PartnerPiece)) (certs : List (List Sub)) : Bool :=
  (certs.length == (s.rows i).length) &&
    (((s.rows i).zip certs).all fun rc => rowCheck K s i rs pcov rc.1 rc.2)

theorem stepCheck_eq (K : Components) (hK : Agrees K) (s : PoseState) (i : Owner)
    (rs : List PoseRow) (pcov : ℕ → List (List PartnerPiece)) (certs : List (List Sub)) :
    stepCheck K s i rs pcov certs = stepB s i rs pcov certs := by
  simp only [stepCheck, stepB, rowCheck_eq K hK]

theorem treeCheck_sound (K : Components) (hK : Agrees K) (C : Ctx)
    {q : UnitSquare} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : (C.a : ℝ) ≤ t) (hb : t ≤ C.b) (hax : q.axis = chartAxis t)
    (hreg : ∀ g ∈ C.regs, q.center ∈ convexHull ℝ (vpts (g.verts.map toQ)) →
      ∃ j : Owner, C.i ≠ j ∧ ∀ r : UnitSquare, RowsContain (C.s.rows j) r →
        rationalHull (C.s.owned j) ⊆ {p | OpenSquare r p} →
        (∀ p, ClosedSquare r p → InContainer coverCap p) →
        ∃ p, OpenSquare q p ∧ OpenSquare r p)
    (tree : CTree) (P : Polygon) (h : treeCheck K C P tree = true)
    (hp : q.center ∈ P.carrier) : Good C q := by
  exact CTree.sound C ht0 ht1 ha hb hax hreg tree P
    (by simpa only [treeCheck_eq K hK] using h) hp

theorem stepCheck_sound (K : Components) (hK : Agrees K) {s : PoseState}
    {i : Owner} {rs : List PoseRow} {pcov : ℕ → List (List PartnerPiece)}
    {certs : List (List Sub)}
    (hpcov : ∀ j, pcov j ≠ [] → pcovB s j (pcov j) = true)
    (h : stepCheck K s i rs pcov certs = true) : ExtStep s (replaceRows s i rs) := by
  exact stepB_sound hpcov (by simpa only [stepCheck_eq K hK] using h)

end ElevenSquare.Tasks.T07.Ext.RuntimeCheck

#print axioms ElevenSquare.Tasks.T07.Ext.RuntimeCheck.components_agree
#print axioms ElevenSquare.Tasks.T07.Ext.RuntimeCheck.stepCheck_eq
#print axioms ElevenSquare.Tasks.T07.Ext.RuntimeCheck.treeCheck_sound
#print axioms ElevenSquare.Tasks.T07.Ext.RuntimeCheck.stepCheck_sound
