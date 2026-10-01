import Sqpack.S11Opt.FieldBridge
import Sqpack.S11Opt.Cells

/-!
# General field certificates: atoms, capacity one, counting

An *atom* of a field certificate is a list of groups of grid points; a set `A` *satisfies* it
when every group has a point in `A` (`AtomSat`).  Two kinds occur:

* a weighted point site: the single group `[[p]]`;
* a weighted majority feature on `2k − 1` sites: one group per `k`-subset, made of barycentric
  witness points of that subset's hull (`baryOk`).

Both have capacity one for disjoint open convex sets (`pt_capacity`, `maj_capacity`).  The
counting theorem `field_count` then turns covers into a contradiction: if every square of a
positive cell `k` satisfies atoms of total weight `≥ γ k` and `Σ γ > Σ w`, there is no packing.
-/

open Finset

namespace SquarePacking.S11Opt

/-! ## Barycentric witnesses for any number of points -/

/-- `Σ lᵢ • pᵢ` over natural numbers, componentwise. -/
def bsum : List ℕ → List (ℕ × ℕ) → ℕ × ℕ
  | l :: ls, p :: ps => (l * p.1 + (bsum ls ps).1, l * p.2 + (bsum ls ps).2)
  | _, _ => (0, 0)

/-- `(Σ lᵢ) • w = Σ lᵢ • pᵢ` with `Σ lᵢ > 0` and one weight per point. -/
def baryOk (pts : List (ℕ × ℕ)) (w : ℕ × ℕ) (l : List ℕ) : Bool :=
  l.length == pts.length && decide (0 < l.sum) && l.sum * w.1 == (bsum l pts).1 &&
    l.sum * w.2 == (bsum l pts).2

/-- The real combination `Σ lᵢ • ptQ pᵢ`. -/
noncomputable def rsum (Q : ℕ) : List ℕ → List (ℕ × ℕ) → ℝ × ℝ
  | l :: ls, p :: ps => (l : ℝ) • ptQ Q p + rsum Q ls ps
  | _, _ => 0

lemma rsum_eq (Q : ℕ) : ∀ (l : List ℕ) (ps : List (ℕ × ℕ)),
    rsum Q l ps = (((bsum l ps).1 : ℝ) / Q, ((bsum l ps).2 : ℝ) / Q)
  | l :: ls, p :: ps => by
    rw [rsum, rsum_eq Q ls ps]
    simp only [bsum, ptQ, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    push_cast; ext <;> simp only <;> ring
  | [], _ => by simp only [rsum, bsum, Nat.cast_zero, zero_div]; rfl
  | _ :: _, [] => by simp only [rsum, bsum, Nat.cast_zero, zero_div]; rfl

/-- A positive combination, normalized, lies in the convex hull of the points. -/
lemma rsum_mem_hull (Q : ℕ) : ∀ (l : List ℕ) (ps : List (ℕ × ℕ)), l.length = ps.length →
    0 < l.sum → ((l.sum : ℝ))⁻¹ • rsum Q l ps ∈ convexHull ℝ {x | ∃ p ∈ ps, x = ptQ Q p}
  | [], _, _, h => by simp at h
  | _ :: _, [], hl, _ => by simp at hl
  | l :: ls, p :: ps, hl, hs => by
    have hcv := convex_convexHull ℝ {x | ∃ q ∈ p :: ps, x = ptQ Q q}
    have hp : ptQ Q p ∈ convexHull ℝ {x | ∃ q ∈ p :: ps, x = ptQ Q q} :=
      subset_convexHull ℝ _ ⟨p, List.mem_cons_self .., rfl⟩
    have hsub : convexHull ℝ {x | ∃ q ∈ ps, x = ptQ Q q}
        ⊆ convexHull ℝ {x | ∃ q ∈ p :: ps, x = ptQ Q q} :=
      convexHull_mono fun x ⟨q, hq, hx⟩ => ⟨q, List.mem_cons_of_mem _ hq, hx⟩
    simp only [List.sum_cons] at hs ⊢
    rw [rsum]
    rcases Nat.eq_zero_or_pos ls.sum with h0 | h0
    · -- the tail has zero weight
      have ht : rsum Q ls ps = 0 := by
        have : ∀ (l' : List ℕ) (ps' : List (ℕ × ℕ)), l'.sum = 0 → rsum Q l' ps' = 0 := by
          intro l'
          induction l' with
          | nil => intro ps' _; simp [rsum]
          | cons a as ih =>
            intro ps' h
            cases ps' with
            | nil => simp [rsum]
            | cons q qs =>
              simp only [List.sum_cons] at h
              rw [rsum, ih qs (by omega), show a = 0 by omega]; simp
        exact this ls ps h0
      rw [ht, h0, add_zero, add_zero]
      have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
      rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
      exact hp
    · have ih := rsum_mem_hull Q ls ps (by simpa using hl) h0
      have hb : (0 : ℝ) < (ls.sum : ℝ) := Nat.cast_pos.mpr h0
      have ha : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _
      have hab : (0 : ℝ) < (l : ℝ) + (ls.sum : ℝ) := by linarith
      have e1 : ((l : ℝ) + (ls.sum : ℝ))⁻¹ * (l : ℝ) = (l : ℝ) / ((l : ℝ) + (ls.sum : ℝ)) := by
        field_simp
      have e2 : ((l : ℝ) + (ls.sum : ℝ))⁻¹
          = (ls.sum : ℝ) / ((l : ℝ) + (ls.sum : ℝ)) * (ls.sum : ℝ)⁻¹ := by
        field_simp
      have key : ((l + ls.sum : ℕ) : ℝ)⁻¹ • ((l : ℝ) • ptQ Q p + rsum Q ls ps)
          = ((l : ℝ) / ((l : ℝ) + (ls.sum : ℝ))) • ptQ Q p
            + ((ls.sum : ℝ) / ((l : ℝ) + (ls.sum : ℝ))) • (((ls.sum : ℝ))⁻¹ • rsum Q ls ps) := by
        rw [Nat.cast_add, smul_add, smul_smul, smul_smul, e1, ← e2]
      rw [key]
      exact hcv hp (hsub ih) (div_nonneg ha hab.le) (div_nonneg hb.le hab.le)
        (by field_simp)

lemma baryOk_mem {Q : ℕ} {pts : List (ℕ × ℕ)} {w : ℕ × ℕ} {l : List ℕ}
    (h : baryOk pts w l = true) : ptQ Q w ∈ convexHull ℝ {x | ∃ p ∈ pts, x = ptQ Q p} := by
  simp only [baryOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen, hm⟩, h1⟩, h2⟩ := h
  set m := l.sum
  have hmem := rsum_mem_hull Q l pts hlen hm
  rw [rsum_eq] at hmem
  have e : ptQ Q w = ((m : ℝ))⁻¹ • (((bsum l pts).1 : ℝ) / Q, ((bsum l pts).2 : ℝ) / Q) := by
    have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have h1' : ((bsum l pts).1 : ℝ) = m * w.1 := by exact_mod_cast h1.symm
    have h2' : ((bsum l pts).2 : ℝ) = m * w.2 := by exact_mod_cast h2.symm
    rw [h1', h2']
    simp only [ptQ, Prod.smul_mk, smul_eq_mul]
    ext <;> simp only <;> field_simp
  rw [e]; exact hmem

/-- Every point of the group is a barycentric witness for `pts`. -/
def groupBaryOk (pts : List (ℕ × ℕ)) : List (ℕ × ℕ) → List (List ℕ) → Bool
  | [], [] => true
  | w :: g, l :: ls => baryOk pts w l && groupBaryOk pts g ls
  | _, _ => false

lemma groupBaryOk_mem {Q : ℕ} {pts : List (ℕ × ℕ)} :
    ∀ (g : List (ℕ × ℕ)) (ls : List (List ℕ)), groupBaryOk pts g ls = true →
      ∀ w ∈ g, ptQ Q w ∈ convexHull ℝ {x | ∃ p ∈ pts, x = ptQ Q p}
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [groupBaryOk] at h
  | w :: g, l :: ls, h => by
    simp only [groupBaryOk, Bool.and_eq_true] at h
    intro w' hw'
    rcases List.mem_cons.mp hw' with rfl | hw'
    · exact baryOk_mem h.1
    · exact groupBaryOk_mem g ls h.2 w' hw'

/-! ## Atoms and capacity one -/

/-- `A` has a point of every group. -/
def AtomSat (Q : ℕ) (A : Set (ℝ × ℝ)) (groups : List (List (ℕ × ℕ))) : Prop :=
  ∀ g ∈ groups, ∃ p ∈ g, ptQ Q p ∈ A

/-- A single point is in at most one of two disjoint sets. -/
theorem pt_capacity {Q : ℕ} {p : ℕ × ℕ} {A B : Set (ℝ × ℝ)} (hAB : Disjoint A B)
    (hA : AtomSat Q A [[p]]) (hB : AtomSat Q B [[p]]) : False := by
  obtain ⟨q, hq, hqA⟩ := hA [p] (List.mem_singleton_self _)
  obtain ⟨q', hq', hqB⟩ := hB [p] (List.mem_singleton_self _)
  rw [List.mem_singleton] at hq hq'
  subst hq hq'
  exact Set.disjoint_left.mp hAB hqA hqB

/-- The `k`-subsets of `range n` all appear in `subs` (as index lists). -/
abbrev SubsComplete (n k : ℕ) (subs : List (List ℕ)) : Prop :=
  ∀ S ∈ (Finset.range n).powersetCard k, ∃ L ∈ subs, L.toFinset = S

/-- **Capacity one of a majority feature**, list form.  `sites` has `2k − 1` points; group `j`
of the atom consists of barycentric witnesses of the sites indexed by `subs[j]`. -/
theorem maj_capacity {Q k : ℕ} {sites : List (ℕ × ℕ)} (hn : sites.length + 1 = 2 * k)
    {subs : List (List ℕ)} (hcomp : SubsComplete sites.length k subs)
    {groups : List (List (ℕ × ℕ))} (hlen : groups.length = subs.length)
    (hbary : ∀ j (hj : j < subs.length) (hj' : j < groups.length), ∃ bs,
      groupBaryOk ((subs[j]).map (sites.getD · (0, 0))) (groups[j]'hj') bs = true)
    {A B : Set (ℝ × ℝ)} (hAc : Convex ℝ A) (hAo : IsOpen A) (hBc : Convex ℝ B) (hBo : IsOpen B)
    (hAB : Disjoint A B) (hA : AtomSat Q A groups) (hB : AtomSat Q B groups) : False := by
  classical
  set pt : ℕ → ℝ × ℝ := fun i => ptQ Q (sites.getD i (0, 0))
  -- a satisfied atom meets the hull of every k-subset
  have hull : ∀ {C : Set (ℝ × ℝ)}, AtomSat Q C groups → ∀ S ∈ (Finset.range sites.length).powersetCard k,
      (C ∩ convexHull ℝ (pt '' (S : Set ℕ))).Nonempty := by
    intro C hC S hS
    obtain ⟨L, hL, hLS⟩ := hcomp S hS
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
    obtain ⟨bs, hb⟩ := hbary j hj (by omega)
    obtain ⟨p, hp, hpC⟩ := hC (groups[j]'(by omega)) (List.getElem_mem _)
    refine ⟨ptQ Q p, hpC, ?_⟩
    have hm' := groupBaryOk_mem (Q := Q) _ _ hb p hp
    refine convexHull_mono ?_ hm'
    rintro x ⟨q, hq, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    refine ⟨i, ?_, rfl⟩
    rw [← hLS]; simpa using hi
  obtain ⟨f, u, hfA, hfB⟩ := geometric_hahn_banach_open_open hAc hAo hBc hBo hAB
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range sites.length)
    (fun i => u ≤ f (pt i))
  rw [Finset.card_range] at hsplit
  by_cases hge : k ≤ ((Finset.range sites.length).filter fun i => u ≤ f (pt i)).card
  · obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hge
    have hS : S ∈ (Finset.range sites.length).powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨hSsub.trans (Finset.filter_subset _ _), hScard⟩
    obtain ⟨x, hxA, hxS⟩ := hull hA S hS
    have hh : convexHull ℝ (pt '' (S : Set ℕ)) ⊆ {x | u ≤ f x} := by
      refine convexHull_min ?_ (convex_halfSpace_ge f.isLinear u)
      rintro _ ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp (hSsub hi)).2
    exact absurd (hh hxS) (not_le.mpr (hfA x hxA))
  · have hlt : k ≤ ((Finset.range sites.length).filter fun i => ¬ u ≤ f (pt i)).card := by omega
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hlt
    have hS : S ∈ (Finset.range sites.length).powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨hSsub.trans (Finset.filter_subset _ _), hScard⟩
    obtain ⟨x, hxB, hxS⟩ := hull hB S hS
    have hh : convexHull ℝ (pt '' (S : Set ℕ)) ⊆ {x | f x < u} := by
      refine convexHull_min ?_ (convex_halfSpace_lt f.isLinear u)
      rintro _ ⟨i, hi, rfl⟩
      exact not_le.mp (Finset.mem_filter.mp (hSsub hi)).2
    exact absurd (hh hxS) (not_lt.mpr (hfB x hxB).le)

/-- All groups of a majority atom are barycentric witnesses of their subsets. -/
def baryAll (sites : List (ℕ × ℕ)) :
    List (List ℕ) → List (List (ℕ × ℕ)) → List (List (List ℕ)) → Bool
  | S :: subs, g :: gs, b :: bs =>
    groupBaryOk (S.map (sites.getD · (0, 0))) g b && baryAll sites subs gs bs
  | [], [], [] => true
  | _, _, _ => false

lemma baryAll_spec {sites : List (ℕ × ℕ)} :
    ∀ {subs : List (List ℕ)} {groups : List (List (ℕ × ℕ))} {barys : List (List (List ℕ))},
      baryAll sites subs groups barys = true →
      groups.length = subs.length ∧ ∀ j (hj : j < subs.length) (hj' : j < groups.length), ∃ bs,
        groupBaryOk ((subs[j]).map (sites.getD · (0, 0))) (groups[j]'hj') bs = true
  | [], [], [], _ => ⟨rfl, fun j hj => by simp at hj⟩
  | [], _ :: _, _, h => by simp [baryAll] at h
  | [], [], _ :: _, h => by simp [baryAll] at h
  | _ :: _, [], _, h => by simp [baryAll] at h
  | _ :: _, _ :: _, [], h => by simp [baryAll] at h
  | S :: subs, g :: gs, b :: bs, h => by
    simp only [baryAll, Bool.and_eq_true] at h
    obtain ⟨hl, ih⟩ := baryAll_spec h.2
    refine ⟨by simp [hl], fun j hj hj' => ?_⟩
    cases j with
    | zero => exact ⟨b, h.1⟩
    | succ j => exact ih j (by simpa using hj) (by simpa using hj')

/-! ## Counting -/

/-- **Double counting.**  Positive cells `P` (distinct), atoms `0, …, n−1` of weights `w`.  If an
atom is satisfied by at most one cell, and every cell `k` satisfies a duplicate-free set of atoms
of weight `≥ γ k`, then `Σ γ ≤ Σ w`. -/
theorem field_count {P : List ℕ} (hP : P.Nodup) {n : ℕ} (w : ℕ → ℕ) (γ : ℕ → ℕ)
    (sat : ℕ → ℕ → Prop)
    (hcap : ∀ a, ∀ k ∈ P, ∀ k' ∈ P, k ≠ k' → sat k a → sat k' a → False)
    (S : ℕ → List ℕ) (hSnd : ∀ k ∈ P, (S k).Nodup) (hSn : ∀ k ∈ P, ∀ a ∈ S k, a < n)
    (hSsat : ∀ k ∈ P, ∀ a ∈ S k, sat k a) (hγ : ∀ k ∈ P, γ k ≤ ((S k).map w).sum) :
    (P.map γ).sum ≤ ∑ a ∈ Finset.range n, w a := by
  classical
  have h1 : (P.map γ).sum ≤ ∑ k ∈ P.toFinset, ∑ a ∈ (S k).toFinset, w a := by
    rw [List.sum_toFinset _ hP]
    refine List.sum_le_sum fun k hk => ?_
    rw [List.sum_toFinset _ (hSnd k hk)]
    exact hγ k hk
  have h2 : ∑ k ∈ P.toFinset, ∑ a ∈ (S k).toFinset, w a
      = ∑ a ∈ Finset.range n, ∑ k ∈ P.toFinset, if a ∈ S k then w a else 0 := by
    rw [Finset.sum_comm' (t' := Finset.range n) (s' := fun a => P.toFinset.filter fun k => a ∈ S k)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_filter]
    · intro k a
      simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hk, ha⟩; exact ⟨⟨hk, ha⟩, hSn k hk a ha⟩
      · rintro ⟨⟨hk, ha⟩, -⟩; exact ⟨hk, ha⟩
  have h3 : ∀ a ∈ Finset.range n, ∑ k ∈ P.toFinset, (if a ∈ S k then w a else 0) ≤ w a := by
    intro a _
    rw [← Finset.sum_filter]
    have hc : (P.toFinset.filter fun k => a ∈ S k).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro k hk k' hk'
      simp only [Finset.mem_filter, List.mem_toFinset] at hk hk'
      by_contra hne
      exact hcap a k hk.1 k' hk'.1 hne (hSsat k hk.1 a hk.2) (hSsat k' hk'.1 a hk'.2)
    rw [Finset.sum_const, smul_eq_mul]
    calc (P.toFinset.filter fun k => a ∈ S k).card * w a ≤ 1 * w a := Nat.mul_le_mul_right _ hc
      _ = w a := one_mul _
  calc (P.map γ).sum ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := Finset.sum_le_sum h3

/-! ## The generic exclusion theorem -/

/-- **Generic field certificate.**  Data: atoms (groups of grid points over `Q`) with weights
`wts`; positive cells `Pos` with thresholds `γ`; for each positive cell, the atom sets `optSets k`
a cover may use and the owned points `used k` it may use (owner, point); the conditional owners
`supp`.  Hypotheses are what the kernel checks: the covers `hcov`, the ownership `hown`, capacity
one of every atom `hcap`, the option data `hopt`, the owners `hused`.  For every sub-list `P` of
positive cells whose thresholds exceed the total weight, the case `supp ++ P` is excluded. -/
theorem field_generic {Q : ℕ} {s : ℝ} (atoms : List (List (List (ℕ × ℕ)))) (wts : List ℕ)
    (Pos supp : List ℕ) (γ : ℕ → ℕ) (optSets : ℕ → List (List ℕ)) (used : ℕ → List (ℕ × (ℕ × ℕ)))
    (hcov : ∀ k ∈ Pos, ∀ (c : ℝ × ℝ) (θ : ℝ), sq c θ 1 ⊆ box Ux → InCellU k c →
      (∃ S ∈ optSets k, ∀ a ∈ S, AtomSat Q (ScSq s c θ) (atoms.getD a [])) ∨
        ∃ e ∈ used k, ptQ Q e.2 ∈ ScSq s c θ)
    (hown : ∀ k ∈ Pos, ∀ e ∈ used k, ∀ (c : ℝ × ℝ) (θ : ℝ), sq c θ 1 ⊆ box Ux → InCellU e.1 c →
      ptQ Q e.2 ∈ ScSq s c θ)
    (hused : ∀ k ∈ Pos, ∀ e ∈ used k, e.1 ∈ supp ∧ e.1 ≠ k)
    (hcap : ∀ a < atoms.length, ∀ {A B : Set (ℝ × ℝ)}, Convex ℝ A → IsOpen A → Convex ℝ B →
      IsOpen B → Disjoint A B → AtomSat Q A (atoms.getD a []) → AtomSat Q B (atoms.getD a []) →
        False)
    (hopt : ∀ k ∈ Pos, ∀ S ∈ optSets k, S.Nodup ∧ (∀ a ∈ S, a < atoms.length) ∧
      γ k ≤ (S.map (wts.getD · 0)).sum)
    (P : List ℕ) (hP : P.Nodup) (hPsub : ∀ k ∈ P, k ∈ Pos)
    (hgap : ∑ a ∈ Finset.range atoms.length, wts.getD a 0 < (P.map γ).sum) :
    CaseExcluded (supp ++ P) := by
  classical
  rintro ⟨n, ctr, ang, hin, hd, σ, hσ, hc⟩
  set A : ℕ → Set (ℝ × ℝ) := fun k => ScSq s (ctr (σ k)) (ang (σ k))
  have hdist : ∀ k ∈ supp ++ P, ∀ k' ∈ supp ++ P, k ≠ k' → Disjoint (A k) (A k') := by
    intro k hk k' hk' hne
    exact disjoint_ScSq (hd _ _ fun h => hne (hσ k hk k' hk' h))
  have hk : ∀ k ∈ P, ∃ S ∈ optSets k, ∀ a ∈ S, AtomSat Q (A k) (atoms.getD a []) := by
    intro k hkP
    have hkJ : k ∈ supp ++ P := List.mem_append_right _ hkP
    rcases hcov k (hPsub k hkP) _ _ (hin (σ k)) (hc k hkJ) with h | ⟨e, he, hm⟩
    · exact h
    · obtain ⟨hes, hne⟩ := hused k (hPsub k hkP) e he
      have heJ : e.1 ∈ supp ++ P := List.mem_append_left _ hes
      have h1 := hown k (hPsub k hkP) e he _ _ (hin (σ e.1)) (hc e.1 heJ)
      exact (Set.disjoint_left.mp (hdist e.1 heJ k hkJ hne) h1 hm).elim
  choose! S hSmem hSsat using hk
  set sat : ℕ → ℕ → Prop := fun k a => a < atoms.length ∧ AtomSat Q (A k) (atoms.getD a [])
  have hcnt := field_count hP (n := atoms.length) (fun a => wts.getD a 0) γ sat
    (by
      intro a k hk k' hk' hne h1 h2
      exact hcap a h1.1 (convex_ScSq _ _ _) (isOpen_ScSq _ _ _) (convex_ScSq _ _ _)
        (isOpen_ScSq _ _ _)
        (hdist k (List.mem_append_right _ hk) k' (List.mem_append_right _ hk') hne) h1.2 h2.2)
    S (fun k hkP => (hopt k (hPsub k hkP) _ (hSmem k hkP)).1)
    (fun k hkP => (hopt k (hPsub k hkP) _ (hSmem k hkP)).2.1)
    (fun k hkP a ha => ⟨(hopt k (hPsub k hkP) _ (hSmem k hkP)).2.1 a ha, hSsat k hkP a ha⟩)
    (fun k hkP => (hopt k (hPsub k hkP) _ (hSmem k hkP)).2.2)
  omega


/-- **Applying a certificate to a case.**  If the certificate excludes `supp ++ P` whenever the
positive cells `P` exceed its total weight `W`, it excludes every case `J` containing `supp` whose
positive cells exceed `W`. -/
theorem excluded_of_applicable {supp pos : List ℕ} {γ : ℕ → ℕ} {W : ℕ}
    (hex : ∀ P : List ℕ, P.Nodup → (∀ k ∈ P, k ∈ pos) → W < (P.map γ).sum → CaseExcluded (supp ++ P))
    (hpos : pos.Nodup) {J : List ℕ} (hsupp : ∀ a ∈ supp, a ∈ J)
    (hgap : W < ((pos.filter (· ∈ J)).map γ).sum) : CaseExcluded J := by
  intro hR
  refine hex (pos.filter (· ∈ J)) (hpos.filter _) (fun k hk => (List.mem_filter.mp hk).1) hgap
    (hR.mono fun a ha => ?_)
  rcases List.mem_append.mp ha with h | h
  · exact hsupp a h
  · simpa using (List.mem_filter.mp h).2

end SquarePacking.S11Opt
