import ElevenSquare.Pending.OrderedData
import Lean.Elab.Tactic.Omega

namespace ElevenSquare.Pending.OrderedData

-- A linear merge scan; fuel exhaustion rejects rather than certifying anything.
def disjointScan : ℕ → List ℕ → List ℕ → Bool
  | _, [], _ => true
  | _, _, [] => true
  | 0, _::_, _::_ => false
  | n+1, a::as, b::bs =>
    if a < b then disjointScan n as (b::bs)
    else if b < a then disjointScan n (a::as) bs else false

theorem disjointScan_sound (fuel : ℕ) : ∀ (xs ys : List ℕ),
    xs.Pairwise (· < ·) → ys.Pairwise (· < ·) →
    disjointScan fuel xs ys = true → xs.Disjoint ys := by
  induction fuel with
  | zero =>
    intro xs ys hx hy h
    cases xs with
    | nil => simp
    | cons a as =>
      cases ys with
      | nil => simp
      | cons b bs => simp [disjointScan] at h
  | succ n ih =>
    intro xs ys hx hy h
    cases xs with
    | nil => simp
    | cons a as =>
      cases ys with
      | nil => simp
      | cons b bs =>
        have hxa := List.pairwise_cons.mp hx
        have hyb := List.pairwise_cons.mp hy
        by_cases hab : a < b
        · simp only [disjointScan, if_pos hab] at h
          have ht := ih as (b::bs) hxa.2 hy h
          intro x hxs hys
          rcases List.mem_cons.mp hxs with rfl | hxs
          · rcases List.mem_cons.mp hys with heq | hys
            · omega
            · have := hyb.1 x hys
              omega
          · exact ht hxs hys
        · by_cases hba : b < a
          · simp only [disjointScan, if_neg hab, if_pos hba] at h
            have ht := ih (a::as) bs hx hyb.2 h
            intro x hxs hys
            rcases List.mem_cons.mp hys with rfl | hys
            · rcases List.mem_cons.mp hxs with heq | hxs
              · omega
              · have := hxa.1 x hxs
                omega
            · exact ht hxs hys
          · simp only [disjointScan, if_neg hab, if_neg hba, Bool.false_eq_true] at h

theorem blocks_disjoint {xs ys : List ℕ} {n m a b c d : ℕ}
    (hx : Block id xs n a b) (hy : Block id ys m c d)
    (h : disjointScan (n+m) xs ys = true) : xs.Disjoint ys := by
  exact disjointScan_sound (n+m) xs ys
    (List.isChain_iff_pairwise.mp hx.ordered) (List.isChain_iff_pairwise.mp hy.ordered) h

end ElevenSquare.Pending.OrderedData
#print axioms ElevenSquare.Pending.OrderedData.blocks_disjoint
