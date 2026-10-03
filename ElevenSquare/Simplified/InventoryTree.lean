import ElevenSquare.Tasks.T04.Completeness.Support

/-! A finite prefix classifier for independent closed-cell labels.
Rejected prefixes reuse the original exact three-halfplane certificates. -/
namespace ElevenSquare.Simplified.InventoryTree
open ElevenSquare.Pending ElevenSquare.Pending.T04Completeness

abbrev PlaneRef := Fin 4 × Fin 20

inductive Tree where
  | accept (row : Fin 220)
  | reject (a b c : PlaneRef) (u v w : ℤ)
  | branch (children : Fin 16 → Tree)

def plane (labels : Fin 4 → Fin 16) (r : PlaneRef) : IntegerPlane :=
  sourcePlane r.1 (labels r.1) r.2

def check (depth : ℕ) (labels : Fin 4 → Fin 16) : Tree → Bool
  | .accept row => decide (depth = 4 ∧ ∀ g, overlayLabels row g = labels g)
  | .reject a b c u v w =>
      decide (a.1.val < depth ∧ b.1.val < depth ∧ c.1.val < depth) &&
        refutationCheck (plane labels a) (plane labels b) (plane labels c) u v w
  | .branch children =>
      if hd : depth < 4 then
        (List.finRange 16).all fun i =>
          check (depth + 1) (Function.update labels ⟨depth, hd⟩ i) (children i)
      else false

def Agrees (depth : ℕ) (seen actual : Fin 4 → Fin 16) : Prop :=
  ∀ g, g.val < depth → seen g = actual g

theorem check_sound (tree : Tree) (depth : ℕ) (seen actual : Fin 4 → Fin 16)
    (p : Point) (hphysical : ∀ g, ClosedCell (actual g) (view g p))
    (hprefix : Agrees depth seen actual) (hc : check depth seen tree = true) :
    ∃ row : Fin 220, overlayLabels row = actual := by
  induction tree generalizing depth seen with
  | accept row =>
      have h := of_decide_eq_true hc
      refine ⟨row, ?_⟩
      funext g
      exact (h.2 g).trans (hprefix g (by omega))
  | reject a b c u v w =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
      have hp (r : PlaneRef) (hr : r.1.val < depth) :
          (plane seen r).rational.contains p := by
        apply sourcePlane_sound
        rw [hprefix r.1 hr]
        exact hphysical r.1
      exact False.elim (refutationCheck_sound _ _ _ u v w hc.2 p
        (hp a hc.1.1) (hp b hc.1.2.1) (hp c hc.1.2.2))
  | branch children ih =>
      simp only [check] at hc
      split at hc
      next hd =>
        let g : Fin 4 := ⟨depth, hd⟩
        have hchild := List.all_eq_true.mp hc (actual g) (by simp)
        apply ih (actual g) (depth + 1) (Function.update seen g (actual g))
        · intro j hj
          by_cases he : j = g
          · subst j
            simp
          · rw [Function.update_of_ne he]
            apply hprefix j
            have hne : j.val ≠ depth := by
              intro hv
              apply he
              exact Fin.ext hv
            omega
        · exact hchild
      next hd => simp at hc

theorem inventory_complete (tree : Tree)
    (hc : check 0 (fun _ => 0) tree = true)
    (labels : Fin 4 → Fin 16) (p : Point)
    (h : ∀ g, ClosedCell (labels g) (view g p)) :
    ∃ row : Fin 220, overlayLabels row = labels := by
  apply check_sound tree 0 (fun _ => 0) labels p h
  · intro g hg
    omega
  · exact hc

end ElevenSquare.Simplified.InventoryTree

#print axioms ElevenSquare.Simplified.InventoryTree.check_sound
#print axioms ElevenSquare.Simplified.InventoryTree.inventory_complete
