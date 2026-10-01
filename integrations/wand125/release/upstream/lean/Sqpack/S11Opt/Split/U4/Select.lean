import Sqpack.S11Opt.Split.U4.Dual

/-!
# U4 — branches and the enumeration of feature selections

A *branch* is a list of row ids with 66 certificates, one per signed coordinate (`branchOK`).
A *selection* chooses one available feature for every contacting pair; `selOK` checks that for
every selection some verified branch uses only wall rows and rows of the selected features.
`select_sound`: if the wall rows and the rows of some selection hold at a perturbation with
`|hv_k| ≤ τ r_k`, saturated at some coordinate, then `τ ≤ 0`.
-/

open Finset

namespace SquarePacking.S11Opt.Split.U4

def branchOK (rowsD : List (List ℤ)) (kts rI b : List ℕ) (cs : List (List ℕ)) : Bool :=
  (List.range 66).all fun t => certOK rowsD kts rI b (t / 2) (t % 2 == 1) (cs.getD t [])

theorem branch_sound {rowsS : List (List (ℕ × ℤ))} {rowsD : List (List ℤ)} {kts rI b : List ℕ}
    {cs : List (List ℕ)}
    (hD : rowsD = rowsS.map densify) (hS : ∀ sp ∈ rowsS, ∀ e ∈ sp, e.1 < 33)
    (hB : branchOK rowsD kts rI b cs = true)
    {hv : ℕ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hrows : ∀ i ∈ b, RowOK (rowsS.getD i []) (kts.getD i 0) hv τ)
    (hb : ∀ k < 33, |hv k| ≤ τ * rI.getD k 0 / DR)
    {j : ℕ} (hj : j < 33) (hsat : |hv j| = τ * rI.getD j 0 / DR) : False := by
  simp only [branchOK, List.all_eq_true, List.mem_range] at hB
  by_cases hs : hv j ≤ 0
  · have h := hB (2 * j + 1) (by omega)
    rw [show (2 * j + 1) / 2 = j by omega, show ((2 * j + 1) % 2 == 1) = true by
      simp [Nat.add_mod]] at h
    refine certOK_sound hD hS h hτ hrows hb hj ?_
    simp only [if_true]; rw [← hsat, abs_of_nonpos hs, neg_neg]
  · push Not at hs
    have h := hB (2 * j) (by omega)
    rw [show (2 * j) / 2 = j by omega, show ((2 * j) % 2 == 1) = false by simp] at h
    refine certOK_sound hD hS h hτ hrows hb hj ?_
    simp only [Bool.false_eq_true, if_false]; rw [← hsat, abs_of_pos hs]

/-- All selections: one index into each pair's list of available features. -/
def sels (featRows : List (List (List ℕ))) : List (List ℕ) :=
  (featRows.map fun fs => List.range fs.length).sections

def selOK (featRows : List (List (List ℕ))) (wallIds : List ℕ) (branches : List (List ℕ))
    (selBranch : List ℕ) : Bool :=
  ((sels featRows).length == selBranch.length) &&
    (((sels featRows).zip selBranch).all fun sb => decide (sb.2 < branches.length) &&
      (branches.getD sb.2 []).all fun id => wallIds.contains id ||
        (sb.1.zip featRows).any fun tf => (tf.2.getD tf.1 []).contains id)

/-- **Soundness of the selection enumeration.** -/
theorem select_sound {rowsS : List (List (ℕ × ℤ))} {rowsD : List (List ℤ)} {kts rI : List ℕ}
    {featRows : List (List (List ℕ))} {wallIds : List ℕ} {branches : List (List ℕ)}
    {selBranch : List ℕ} {certF : ℕ → List (List ℕ)}
    (hD : rowsD = rowsS.map densify) (hS : ∀ sp ∈ rowsS, ∀ e ∈ sp, e.1 < 33)
    (hsel : selOK featRows wallIds branches selBranch = true)
    (hall : ∀ bi < branches.length, branchOK rowsD kts rI (branches.getD bi []) (certF bi) = true)
    {hv : ℕ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hwall : ∀ id ∈ wallIds, RowOK (rowsS.getD id []) (kts.getD id 0) hv τ)
    (hfeat : ∀ q < featRows.length, ∃ t < (featRows.getD q []).length,
      ∀ id ∈ (featRows.getD q []).getD t [], RowOK (rowsS.getD id []) (kts.getD id 0) hv τ)
    (hb : ∀ k < 33, |hv k| ≤ τ * rI.getD k 0 / DR)
    {j : ℕ} (hj : j < 33) (hsat : |hv j| = τ * rI.getD j 0 / DR) : False := by
  choose! f hf1 hf2 using hfeat
  set s := (List.range featRows.length).map f with hsdef
  have hs : s ∈ sels featRows := by
    unfold sels
    rw [List.mem_sections, List.forall₂_iff_get]
    refine ⟨by simp [s], fun i h1 h2 => ?_⟩
    have hi : i < featRows.length := by simpa [s] using h1
    simp only [List.get_eq_getElem, s, List.getElem_map, List.getElem_range, List.mem_range]
    have := hf1 i hi
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
  simp only [selOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true] at hsel
  obtain ⟨hlen, hsb⟩ := hsel
  obtain ⟨n, hn, hns⟩ := List.mem_iff_getElem.mp hs
  have hn' : n < selBranch.length := hlen ▸ hn
  have hmem : (s, selBranch[n]) ∈ (sels featRows).zip selBranch := by
    rw [List.mem_iff_getElem]
    exact ⟨n, by simp [hn, hn'], by simp [List.getElem_zip, hns]⟩
  obtain ⟨hbi, hcov⟩ := hsb _ hmem
  refine branch_sound hD hS (hall _ hbi) hτ (fun id hid => ?_) hb hj hsat
  rcases hcov id hid with hw | ⟨tf, htf, hid'⟩
  · exact hwall id hw
  · obtain ⟨m, hm, hmt⟩ := List.mem_iff_getElem.mp htf
    have hm1 : m < s.length := by simp at hm; omega
    have hm2 : m < featRows.length := by simp at hm; omega
    rw [List.getElem_zip] at hmt
    rw [← hmt] at hid'
    have hq := hf2 m hm2 id
    simp only [s, List.getElem_map, List.getElem_range] at hid'
    rw [List.getD_eq_getElem?_getD (l := featRows), List.getElem?_eq_getElem hm2,
      Option.getD_some] at hq
    exact hq hid'

end SquarePacking.S11Opt.Split.U4
