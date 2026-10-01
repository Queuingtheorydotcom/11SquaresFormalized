import ElevenSquare.Tasks.T03.BernsteinBands

namespace ElevenSquare.Pending.T03
noncomputable section

/-- A closed interval subdivision, with exact certificates at each leaf. -/
inductive OwnershipTree where
  | leaf : BernsteinBandCertificate → OwnershipTree
  | empty : AngleBand → LinearCertificate → OwnershipTree
  | split : ℚ → OwnershipTree → OwnershipTree → OwnershipTree
  deriving Inhabited

def OwnershipTree.check (i : Fin 16) (v : QPoint) (lo hi : ℚ) : OwnershipTree → Bool
  | .leaf w => decide (w.band.lo = lo ∧ w.band.hi = hi) && w.check i v
  | .empty r w => decide (r.lo = lo ∧ r.hi = hi) && r.check &&
      w.check (r.domain i) ⟨0,0,-1⟩
  | .split m left right => left.check i v lo m && right.check i v m hi

theorem OwnershipTree.sound (tree : OwnershipTree) (i : Fin 16) (v : QPoint)
    (lo hi : ℚ) (h : tree.check i v lo hi = true) (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell i (normalizeCenter q.center)) (hq : q.axis = chartAxis t)
    (ht0 : (lo:ℝ) ≤ t) (ht1 : t ≤ (hi:ℝ)) : OpenSquare q (realPoint v) := by
  induction tree generalizing lo hi with
  | leaf w =>
    simp only [OwnershipTree.check, Bool.and_eq_true, decide_eq_true_eq] at h
    exact w.sound i v h.2 q t hc hcell hq
      (by simpa [h.1.1] using ht0) (by simpa [h.1.2] using ht1)
  | empty r w =>
    simp only [OwnershipTree.check, Bool.and_eq_true, decide_eq_true_eq] at h
    have hp := r.contains_center i h.1.2 q t hc hcell hq
      (by simpa [h.1.1.1] using ht0) (by simpa [h.1.1.2] using ht1)
    rw [w.empty _ h.2] at hp
    exact False.elim hp
  | split m left right ihl ihr =>
    simp only [OwnershipTree.check, Bool.and_eq_true] at h
    by_cases hm : t ≤ (m:ℝ)
    · exact ihl lo m h.1 ht0 hm
    · exact ihr m hi h.2 (le_of_lt (lt_of_not_ge hm)) ht1

end
end ElevenSquare.Pending.T03
