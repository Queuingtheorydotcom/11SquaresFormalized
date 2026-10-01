import Sqpack.S11Opt.Basic

/-!
# Majority-hull features have capacity one

A *majority feature* is a finite point set `P` of odd size `2k − 1`.  A set `A` is **TRUE** for it
when `A` meets the convex hull of every `k`-point subset of `P`.  Two disjoint open convex sets
cannot both be TRUE (`majority_capacity`): separate them by a line (Hahn–Banach); one closed side
contains `k` points of `P`, and their hull misses the set on the other side.

This is the capacity rule of the author's `majority_hull` field features (checker
`independent_patch_cover.true_rows`).  The author's TRUE region (the core projects onto every
pair normal and both frame axes over the median) implies TRUE in this sense by the
separating-axis theorem; our certificates prove TRUE directly by exhibiting a witness point of
each `k`-hull inside the square (`sqInt_*` below), so the separating-axis theorem is not needed.
-/

open Finset

namespace SquarePacking.S11Opt

/-- `A` meets the convex hull of every `k`-point subset of `P`. -/
def TrueFor (k : ℕ) (P : Finset (ℝ × ℝ)) (A : Set (ℝ × ℝ)) : Prop :=
  ∀ S ⊆ P, S.card = k → (A ∩ convexHull ℝ (S : Set (ℝ × ℝ))).Nonempty

/-- **Capacity one.** -/
theorem majority_capacity {k : ℕ} {P : Finset (ℝ × ℝ)} (hP : P.card + 1 = 2 * k)
    {A B : Set (ℝ × ℝ)} (hAc : Convex ℝ A) (hAo : IsOpen A) (hBc : Convex ℝ B) (hBo : IsOpen B)
    (hAB : Disjoint A B) (hA : TrueFor k P A) (hB : TrueFor k P B) : False := by
  obtain ⟨f, u, hfA, hfB⟩ := geometric_hahn_banach_open_open hAc hAo hBc hBo hAB
  have hsplit := Finset.card_filter_add_card_filter_not (s := P) (fun p => u ≤ f p)
  by_cases hge : k ≤ (P.filter fun p => u ≤ f p).card
  · obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hge
    obtain ⟨x, hxA, hxS⟩ := hA S (hSsub.trans (Finset.filter_subset _ _)) hScard
    have hhull : convexHull ℝ (S : Set (ℝ × ℝ)) ⊆ {x | u ≤ f x} := by
      refine convexHull_min (fun p hp => ?_) ?_
      · exact (Finset.mem_filter.mp (hSsub hp)).2
      · exact convex_halfSpace_ge f.isLinear u
    exact absurd (hhull hxS) (not_le.mpr (hfA x hxA))
  · have hlt : k ≤ (P.filter fun p => ¬ u ≤ f p).card := by omega
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hlt
    obtain ⟨x, hxB, hxS⟩ := hB S (hSsub.trans (Finset.filter_subset _ _)) hScard
    have hhull : convexHull ℝ (S : Set (ℝ × ℝ)) ⊆ {x | f x < u} := by
      refine convexHull_min (fun p hp => ?_) ?_
      · exact not_le.mp (Finset.mem_filter.mp (hSsub hp)).2
      · exact convex_halfSpace_lt f.isLinear u
    exact absurd (hhull hxS) (not_lt.mpr (hfB x hxB).le)

/-! ## Open unit squares are open and convex -/

lemma coord_affine (c : ℝ × ℝ) (θ : ℝ) (p q : ℝ × ℝ) (a b : ℝ) (hab : a + b = 1) :
    coord c θ (a • p + b • q) = (a * (coord c θ p).1 + b * (coord c θ q).1,
      a * (coord c θ p).2 + b * (coord c θ q).2) := by
  simp only [coord, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  ext
  · simp only; linear_combination (c.1 * Real.cos θ + c.2 * Real.sin θ) * hab
  · simp only; linear_combination (c.2 * Real.cos θ - c.1 * Real.sin θ) * hab

lemma abs_comb_lt {a b X Y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hX : |X| < 1 / 2) (hY : |Y| < 1 / 2) : |a * X + b * Y| < 1 / 2 := by
  rcases abs_lt.mp hX with ⟨h1, h2⟩
  rcases abs_lt.mp hY with ⟨h3, h4⟩
  rw [abs_lt]
  rcases ha.lt_or_eq with ha' | ha'
  · have e1 : 0 < a * (1 / 2 - X) := mul_pos ha' (by linarith)
    have e2 : 0 < a * (X + 1 / 2) := mul_pos ha' (by linarith)
    have e3 : 0 ≤ b * (1 / 2 - Y) := mul_nonneg hb (by linarith)
    have e4 : 0 ≤ b * (Y + 1 / 2) := mul_nonneg hb (by linarith)
    constructor <;> nlinarith
  · subst ha'
    have hb1 : b = 1 := by linarith
    subst hb1
    constructor <;> linarith

lemma convex_sqInt (c : ℝ × ℝ) (θ : ℝ) : Convex ℝ (sqInt c θ 1) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  show |(coord c θ (a • p + b • q)).1| < 1 / 2 ∧ |(coord c θ (a • p + b • q)).2| < 1 / 2
  rw [coord_affine c θ p q a b hab]
  exact ⟨abs_comb_lt ha hb hab hp1 hq1, abs_comb_lt ha hb hab hp2 hq2⟩

lemma isOpen_sqInt (c : ℝ × ℝ) (θ : ℝ) : IsOpen (sqInt c θ 1) := by
  have hc : Continuous (coord c θ) := by unfold coord; fun_prop
  exact (isOpen_lt (continuous_abs.comp (continuous_fst.comp hc)) continuous_const).inter
    (isOpen_lt (continuous_abs.comp (continuous_snd.comp hc)) continuous_const)

/-- Two squares of a packing are never both TRUE for the same majority feature. -/
theorem not_both_true {k : ℕ} {P : Finset (ℝ × ℝ)} (hP : P.card + 1 = 2 * k)
    {ci cj : ℝ × ℝ} {θi θj : ℝ} (hdisj : Disjoint (sqInt ci θi 1) (sqInt cj θj 1))
    (hi : TrueFor k P (sqInt ci θi 1)) (hj : TrueFor k P (sqInt cj θj 1)) : False :=
  majority_capacity hP (convex_sqInt _ _) (isOpen_sqInt _ _) (convex_sqInt _ _)
    (isOpen_sqInt _ _) hdisj hi hj

end SquarePacking.S11Opt
