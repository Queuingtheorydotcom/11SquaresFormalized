import Sqpack.S11Opt.Split.U3.Data

/-!
# U3 — the finite search of the D4 bridge

One kernel check per identity-view mask (216 target choices each).
-/

set_option linter.style.longLine false

namespace SquarePacking.S11Opt.Split


/-- The order in which the search visits owners (fewest regions first). -/
def ownerOrder : List ℕ := [3, 12, 1, 14, 0, 15, 2, 4, 11, 13, 7, 8, 6, 9, 5, 10]

lemma ownerOrder_nodup : ownerOrder.Nodup := by decide

lemma search_0 : six.all (fun M1 => six.all fun M2 => six.all fun M3 =>
    !ext domT [M1, M2, M3] (2 ^ 220 - 1) (ownerOrder.filter fun o => [0, 1, 2, 4, 6, 7, 9, 10, 12, 14, 15].contains o)) = true := by
  decide +kernel

lemma search_1 : six.all (fun M1 => six.all fun M2 => six.all fun M3 =>
    !ext domT [M1, M2, M3] (2 ^ 220 - 1) (ownerOrder.filter fun o => [0, 1, 3, 5, 6, 8, 9, 11, 12, 13, 14].contains o)) = true := by
  decide +kernel

lemma search_2 : six.all (fun M1 => six.all fun M2 => six.all fun M3 =>
    !ext domT [M1, M2, M3] (2 ^ 220 - 1) (ownerOrder.filter fun o => [0, 1, 3, 5, 6, 8, 9, 11, 13, 14, 15].contains o)) = true := by
  decide +kernel

lemma search_3 : six.all (fun M1 => six.all fun M2 => six.all fun M3 =>
    !ext domT [M1, M2, M3] (2 ^ 220 - 1) (ownerOrder.filter fun o => [0, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14].contains o)) = true := by
  decide +kernel

lemma search_4 : six.all (fun M1 => six.all fun M2 => six.all fun M3 =>
    !ext domT [M1, M2, M3] (2 ^ 220 - 1) (ownerOrder.filter fun o => [1, 2, 3, 4, 6, 7, 9, 10, 12, 14, 15].contains o)) = true := by
  decide +kernel

lemma search_5 : six.all (fun M1 => six.all fun M2 => six.all fun M3 =>
    !ext domT [M1, M2, M3] (2 ^ 220 - 1) (ownerOrder.filter fun o => [1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 15].contains o)) = true := by
  decide +kernel

/-- **The finite assertion** (PROOF.md §6): for every identity-view mask `J₀` among the six raw
masks and every choice of target masks `M₁, M₂, M₃` for the views `1, 2, 3`, no pairwise compatible
choice of regions exists.  1,296 searches (28,636 nodes), checked by the kernel. -/
theorem search_unsat {J0 M1 M2 M3 : List ℕ} (h0 : J0 ∈ six) (h1 : M1 ∈ six) (h2 : M2 ∈ six)
    (h3 : M3 ∈ six) :
    ext domT [M1, M2, M3] (2 ^ 220 - 1) (ownerOrder.filter fun o => J0.contains o) = false := by
  simp only [six, List.mem_cons, List.not_mem_nil, or_false] at h0
  rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl
  · have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp search_0 M1 h1) M2 h2) M3 h3
    exact Bool.eq_false_iff.mpr fun h => by rw [h] at this; exact absurd this (by decide)
  · have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp search_1 M1 h1) M2 h2) M3 h3
    exact Bool.eq_false_iff.mpr fun h => by rw [h] at this; exact absurd this (by decide)
  · have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp search_2 M1 h1) M2 h2) M3 h3
    exact Bool.eq_false_iff.mpr fun h => by rw [h] at this; exact absurd this (by decide)
  · have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp search_3 M1 h1) M2 h2) M3 h3
    exact Bool.eq_false_iff.mpr fun h => by rw [h] at this; exact absurd this (by decide)
  · have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp search_4 M1 h1) M2 h2) M3 h3
    exact Bool.eq_false_iff.mpr fun h => by rw [h] at this; exact absurd this (by decide)
  · have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp search_5 M1 h1) M2 h2) M3 h3
    exact Bool.eq_false_iff.mpr fun h => by rw [h] at this; exact absurd this (by decide)

end SquarePacking.S11Opt.Split
