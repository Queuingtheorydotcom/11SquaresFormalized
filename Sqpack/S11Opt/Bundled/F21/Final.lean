import Sqpack.S11Opt.Bundled.F21.Coverage
import Sqpack.S11Opt.Bundled.Own.Mem
import Sqpack.S11Opt.FieldGen

namespace SquarePacking.S11Opt.Bundled.F21
open SquarePacking.S11Opt.F21

open FieldTree

lemma cover4 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 4 c) :
    (∃ S ∈ optSets4, ∀ a ∈ S, AtomSat G.Q (ScSq G.sc c θ) (atoms.getD a [])) ∨
      ∃ e ∈ used4, ptQ G.Q e.2 ∈ ScSq G.sc c θ := by
  obtain ⟨o, ho, hg⟩ := bridge G.Q_pos G.R_pos cov4p0_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP4 hc)
  simp only [opts4, List.mem_append, List.mem_map] at ho
  rcases ho with ⟨S, hS, rfl⟩ | ⟨e, he, rfl⟩
  · exact Or.inl ⟨S, hS, fun a ha g hg' => hg g (List.mem_flatMap.mpr ⟨a, ha, hg'⟩)⟩
  · obtain ⟨p, hp, hm⟩ := hg _ (List.mem_singleton_self _)
    simp only [List.mem_singleton] at hp
    subst hp
    exact Or.inr ⟨e, he, hm⟩

lemma cover9 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 9 c) :
    (∃ S ∈ optSets9, ∀ a ∈ S, AtomSat G.Q (ScSq G.sc c θ) (atoms.getD a [])) ∨
      ∃ e ∈ used9, ptQ G.Q e.2 ∈ ScSq G.sc c θ := by
  obtain ⟨o, ho, hg⟩ := bridge G.Q_pos G.R_pos cov9p0_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP9 hc)
  simp only [opts9, List.mem_append, List.mem_map] at ho
  rcases ho with ⟨S, hS, rfl⟩ | ⟨e, he, rfl⟩
  · exact Or.inl ⟨S, hS, fun a ha g hg' => hg g (List.mem_flatMap.mpr ⟨a, ha, hg'⟩)⟩
  · obtain ⟨p, hp, hm⟩ := hg _ (List.mem_singleton_self _)
    simp only [List.mem_singleton] at hp
    subst hp
    exact Or.inr ⟨e, he, hm⟩

lemma cover10 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 10 c) :
    (∃ S ∈ optSets10, ∀ a ∈ S, AtomSat G.Q (ScSq G.sc c θ) (atoms.getD a [])) ∨
      ∃ e ∈ used10, ptQ G.Q e.2 ∈ ScSq G.sc c θ := by
  obtain ⟨o, ho, hg⟩ := bridge G.Q_pos G.R_pos cov10g8 G.sc_pos G.sc_lt G.UM hin (G.cellHP10 hc)
  simp only [opts10, List.mem_append, List.mem_map] at ho
  rcases ho with ⟨S, hS, rfl⟩ | ⟨e, he, rfl⟩
  · exact Or.inl ⟨S, hS, fun a ha g hg' => hg g (List.mem_flatMap.mpr ⟨a, ha, hg'⟩)⟩
  · obtain ⟨p, hp, hm⟩ := hg _ (List.mem_singleton_self _)
    simp only [List.mem_singleton] at hp
    subst hp
    exact Or.inr ⟨e, he, hm⟩

lemma cover13 {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 13 c) :
    (∃ S ∈ optSets13, ∀ a ∈ S, AtomSat G.Q (ScSq G.sc c θ) (atoms.getD a [])) ∨
      ∃ e ∈ used13, ptQ G.Q e.2 ∈ ScSq G.sc c θ := by
  obtain ⟨o, ho, hg⟩ := bridge G.Q_pos G.R_pos cov13p0_1 G.sc_pos G.sc_lt G.UM hin (G.cellHP13 hc)
  simp only [opts13, List.mem_append, List.mem_map] at ho
  rcases ho with ⟨S, hS, rfl⟩ | ⟨e, he, rfl⟩
  · exact Or.inl ⟨S, hS, fun a ha g hg' => hg g (List.mem_flatMap.mpr ⟨a, ha, hg'⟩)⟩
  · obtain ⟨p, hp, hm⟩ := hg _ (List.mem_singleton_self _)
    simp only [List.mem_singleton] at hp
    subst hp
    exact Or.inr ⟨e, he, hm⟩

lemma hcov : ∀ k ∈ pos, ∀ (c : ℝ × ℝ) (θ : ℝ), sq c θ 1 ⊆ box Ux → InCellU k c →
    (∃ S ∈ optSets k, ∀ a ∈ S, AtomSat G.Q (ScSq G.sc c θ) (atoms.getD a [])) ∨
      ∃ e ∈ used k, ptQ G.Q e.2 ∈ ScSq G.sc c θ := by
  intro k hk c θ hin hc
  simp only [pos, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact cover4 hin hc
  · exact cover9 hin hc
  · exact cover10 hin hc
  · exact cover13 hin hc

lemma used_reg : ∀ k ∈ pos, ∀ e ∈ used k, e ∈ Own.reg := by decide +kernel

lemma hused : ∀ k ∈ pos, ∀ e ∈ used k, e.1 ∈ supp ∧ e.1 ≠ k := by decide +kernel

lemma hopt : ∀ k ∈ pos, ∀ S ∈ optSets k, S.Nodup ∧ (∀ a ∈ S, a < atoms.length) ∧
    gam.getD k 0 ≤ (S.map (wts.getD · 0)).sum := by decide +kernel

lemma cap0 {A B : Set (ℝ × ℝ)} (hAc : Convex ℝ A) (hAo : IsOpen A) (hBc : Convex ℝ B)
    (hBo : IsOpen B) (hAB : Disjoint A B) (hA : AtomSat G.Q A (atoms.getD 0 []))
    (hB : AtomSat G.Q B (atoms.getD 0 [])) : False := by
  exact pt_capacity (Q := G.Q) (p := (5744927232, 12377959296)) hAB hA hB

lemma cap1 {A B : Set (ℝ × ℝ)} (hAc : Convex ℝ A) (hAo : IsOpen A) (hBc : Convex ℝ B)
    (hBo : IsOpen B) (hAB : Disjoint A B) (hA : AtomSat G.Q A (atoms.getD 1 []))
    (hB : AtomSat G.Q B (atoms.getD 1 [])) : False := by
  exact pt_capacity (Q := G.Q) (p := (8588214336, 8576648064)) hAB hA hB

lemma cap2 {A B : Set (ℝ × ℝ)} (hAc : Convex ℝ A) (hAo : IsOpen A) (hBc : Convex ℝ B)
    (hBo : IsOpen B) (hAB : Disjoint A B) (hA : AtomSat G.Q A (atoms.getD 2 []))
    (hB : AtomSat G.Q B (atoms.getD 2 [])) : False := by
  have hb := baryAll_spec (sites := sites2) (subs := subs2)
    (groups := atoms.getD 2 []) (barys := barys2) (by decide +kernel)
  exact maj_capacity (Q := G.Q) (k := 2) (sites := sites2) (subs := subs2)
    (by decide +kernel) (by decide +kernel)
    hb.1 hb.2 hAc hAo hBc hBo hAB hA hB

lemma cap3 {A B : Set (ℝ × ℝ)} (hAc : Convex ℝ A) (hAo : IsOpen A) (hBc : Convex ℝ B)
    (hBo : IsOpen B) (hAB : Disjoint A B) (hA : AtomSat G.Q A (atoms.getD 3 []))
    (hB : AtomSat G.Q B (atoms.getD 3 [])) : False := by
  have hb := baryAll_spec (sites := sites3) (subs := subs3)
    (groups := atoms.getD 3 []) (barys := barys3) (by decide +kernel)
  exact maj_capacity (Q := G.Q) (k := 3) (sites := sites3) (subs := subs3)
    (by decide +kernel) (by decide +kernel)
    hb.1 hb.2 hAc hAo hBc hBo hAB hA hB

lemma hcap : ∀ a < atoms.length, ∀ {A B : Set (ℝ × ℝ)}, Convex ℝ A → IsOpen A → Convex ℝ B →
    IsOpen B → Disjoint A B → AtomSat G.Q A (atoms.getD a []) → AtomSat G.Q B (atoms.getD a []) →
      False := by
  intro a ha A B hAc hAo hBc hBo hAB hA hB
  have ha' : a < 4 := by simpa [atoms] using ha
  interval_cases a
  · exact cap0 hAc hAo hBc hBo hAB hA hB
  · exact cap1 hAc hAo hBc hBo hAB hA hB
  · exact cap2 hAc hAo hBc hBo hAB hA hB
  · exact cap3 hAc hAo hBc hBo hAB hA hB

/-- **Field certificate 21.**  For every list `P` of positive cells whose thresholds exceed
the total weight, the case `supp ++ P` is excluded. -/
theorem excluded (P : List ℕ) (hP : P.Nodup) (hPsub : ∀ k ∈ P, k ∈ pos)
    (hgap : ∑ a ∈ Finset.range atoms.length, wts.getD a 0 < (P.map (gam.getD · 0)).sum) :
    CaseExcluded (supp ++ P) :=
  field_generic atoms wts pos supp (gam.getD · 0) optSets used hcov
    (fun k hk e he _ _ hin hc => Own.reg_mem e (used_reg k hk e he) hin hc) hused hcap hopt P hP hPsub hgap

lemma pos_nodup : pos.Nodup := by decide

/-- The certificate applies to the case `J`: `J` contains the owners, and the positive cells
of `J` exceed the total weight. -/
noncomputable def applicable (J : List ℕ) : Bool :=
  supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range atoms.length, wts.getD a 0) <
      ((pos.filter (· ∈ J)).map (gam.getD · 0)).sum)

theorem applicable_sound {J : List ℕ} (h : applicable J = true) : CaseExcluded J := by
  simp only [applicable, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact excluded_of_applicable excluded pos_nodup h.1 h.2

end SquarePacking.S11Opt.Bundled.F21

namespace SquarePacking.S11Opt.F21
open FieldTree

example {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 4 c) :
    (∃ S ∈ optSets4, ∀ a ∈ S, AtomSat G.Q (ScSq G.sc c θ) (atoms.getD a [])) ∨
      ∃ e ∈ used4, ptQ G.Q e.2 ∈ ScSq G.sc c θ :=
  SquarePacking.S11Opt.Bundled.F21.cover4 hin hc

example {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 9 c) :
    (∃ S ∈ optSets9, ∀ a ∈ S, AtomSat G.Q (ScSq G.sc c θ) (atoms.getD a [])) ∨
      ∃ e ∈ used9, ptQ G.Q e.2 ∈ ScSq G.sc c θ :=
  SquarePacking.S11Opt.Bundled.F21.cover9 hin hc

example {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 10 c) :
    (∃ S ∈ optSets10, ∀ a ∈ S, AtomSat G.Q (ScSq G.sc c θ) (atoms.getD a [])) ∨
      ∃ e ∈ used10, ptQ G.Q e.2 ∈ ScSq G.sc c θ :=
  SquarePacking.S11Opt.Bundled.F21.cover10 hin hc

example {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU 13 c) :
    (∃ S ∈ optSets13, ∀ a ∈ S, AtomSat G.Q (ScSq G.sc c θ) (atoms.getD a [])) ∨
      ∃ e ∈ used13, ptQ G.Q e.2 ∈ ScSq G.sc c θ :=
  SquarePacking.S11Opt.Bundled.F21.cover13 hin hc

example : ∀ k ∈ pos, ∀ (c : ℝ × ℝ) (θ : ℝ), sq c θ 1 ⊆ box Ux → InCellU k c →
    (∃ S ∈ optSets k, ∀ a ∈ S, AtomSat G.Q (ScSq G.sc c θ) (atoms.getD a [])) ∨
      ∃ e ∈ used k, ptQ G.Q e.2 ∈ ScSq G.sc c θ :=
  SquarePacking.S11Opt.Bundled.F21.hcov

example (P : List ℕ) (hP : P.Nodup) (hPsub : ∀ k ∈ P, k ∈ pos)
    (hgap : ∑ a ∈ Finset.range atoms.length, wts.getD a 0 < (P.map (gam.getD · 0)).sum) :
    CaseExcluded (supp ++ P) :=
  SquarePacking.S11Opt.Bundled.F21.excluded P hP hPsub hgap

example (J : List ℕ) : SquarePacking.S11Opt.Bundled.F21.applicable J = (
  supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range atoms.length, wts.getD a 0) <
      ((pos.filter (· ∈ J)).map (gam.getD · 0)).sum)) := rfl

example {J : List ℕ} (h : SquarePacking.S11Opt.Bundled.F21.applicable J = true) : CaseExcluded J :=
  SquarePacking.S11Opt.Bundled.F21.applicable_sound h

end SquarePacking.S11Opt.F21

#print axioms SquarePacking.S11Opt.Bundled.F21.excluded
#print axioms SquarePacking.S11Opt.Bundled.F21.applicable_sound
