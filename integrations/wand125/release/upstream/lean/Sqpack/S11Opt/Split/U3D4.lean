import Sqpack.S11Opt.Split.U3.Mem
import Sqpack.S11Opt.Split.U3.Ban
import Sqpack.S11Opt.Split.U3.Search

/-!
# U3 — the D4 bridge to case 438 (PROOF.md §6)

Owner: f1 (with `Split/U3/`).  Nothing of the author's data is read: the overlay regions are
recomputed from the sites `PU` (`scripts/u1u3/u3gen.py`; stage counts 16, 56, 124, 220 and 8 singletons,
as in `cover_overlay_exact.json`).

Suppose no packing in `cbox S` realizes `J438`.  Then, for each view `g < 4` (`U3/Defs`: the
identity, `x ↦ Ux − x`, the quarter-turn and the diagonal reflection), the view of the packing is a
packing in `cbox S` whose label list is one of the six raw masks of the other three candidates
(`mask_six`: the canonical form is some `maskAt i`; a non-candidate is excluded by
`NoncandidateExcluded`, and `438` by the supposition).  Every centre lies in one of the 220
overlay regions (`tuple_mem`, `U3/Pair*`, `U3/Mem`); two centres have distinct labels in every
view (U1) and are not in a banned pair of regions (`U3/Ban`).  So the finite search `ext` would
succeed (`ext_true`), but it fails for all 1,296 choices of masks (`search_unsat`).

Unlike the author's argument we do not half-turn the packing to make the identity-view mask
canonical: the search runs over all six identity-view masks.
-/

set_option linter.style.longLine false

namespace SquarePacking.S11Opt.Split

/-- A realization in `cbox S` is one in `[0, Ux]²`. -/
lemma RealizesIn.realizes {S : ℝ} (hS : S ≤ Ux) {J : List ℕ} (h : RealizesIn S J) :
    Realizes J := by
  obtain ⟨n, ctr, ang, ⟨hin, hd⟩, σ, hσ, hc⟩ := h
  refine ⟨n, ctr, ang, fun i q hq => ?_, hd, σ, hσ, hc⟩
  obtain ⟨h1, h2, h3, h4⟩ := hin i hq
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma hmask_hmask {J : List ℕ} (hJ : ∀ a ∈ J, a < 16) : hmask (hmask J) = J := by
  simp only [hmask, List.map_reverse, List.reverse_reverse, List.map_map]
  conv_rhs => rw [← List.map_id J]
  refine List.map_congr_left fun a ha => ?_
  have := hJ a ha
  simp only [Function.comp_apply, id_eq]
  omega

lemma lt16_of_mem {J : List ℕ} (hJ : J ∈ List.sublistsLen 11 (List.range 16)) {x : ℕ}
    (hx : x ∈ J) : x < 16 :=
  List.mem_range.mp ((List.mem_sublistsLen.mp hJ).1.subset hx)

/-- Under the hypotheses of the bridge, a realized 11-cell list is one of the six raw masks. -/
lemma mask_six (hNC : NoncandidateExcluded) {S : ℝ} (hS : S ≤ Ux) (hno : ¬ RealizesIn S J438)
    {J : List ℕ} (hJ : J ∈ List.sublistsLen 11 (List.range 16)) (hR : RealizesIn S J) :
    J ∈ six := by
  have hJ16 : ∀ x ∈ J, x < 16 := fun x hx => lt16_of_mem hJ hx
  -- the canonical form `K` of `J`, realized, is a candidate other than `438`
  have cand : ∀ K, K ∈ canonicalMasks → RealizesIn S K →
      K = maskAt 999 ∨ K = maskAt 1462 ∨ K = maskAt 1659 := by
    intro K hK hRK
    obtain ⟨i, hi, rfl⟩ := mem_canonical_iff_maskAt.mp hK
    have hc : i ∈ candIdx := by
      by_contra hn
      exact hNC i hi hn (hRK.realizes hS)
    simp only [candIdx, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · rw [maskAt_438] at hRK; exact absurd hRK hno
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases canonical_or_hmask hJ with hc | hc
  · rcases cand J hc hR with h | h | h
    · rw [h, maskAt_999]; decide
    · rw [h, maskAt_1462]; decide
    · rw [h, maskAt_1659]; decide
  · have hJ' := hmask_hmask hJ16
    rcases cand _ hc (hR.hmask hJ16) with h | h | h
    · rw [← hJ', h, maskAt_999]; decide
    · rw [← hJ', h, maskAt_1462]; decide
    · rw [← hJ', h, maskAt_1659]; decide

/-- The region test for an actual centre. -/
lemma inT_of {p : ℝ × ℝ} {a : ℕ → ℕ} (h : ∀ g, InCellU (a g) (vw g p)) :
    InT [a 0, a 1, a 2, a 3] p := by
  intro g hg
  interval_cases g <;> exact h _

/-- The entry of a region is in the table of its identity-view label. -/
lemma mem_domT {r o : ℕ} (hr : r < 220) (h0 : lab r 0 = o) (ho : o < 16) :
    (r, regs.getD r [], compatM.getD r 0) ∈ domT.getD o [] := by
  rw [domT_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ho]
  simp only [Option.map_some, Option.getD_some, List.mem_map, List.mem_filter, List.mem_range,
    beq_iff_eq]
  exact ⟨r, ⟨hr, h0⟩, rfl⟩

/-- **U3.**  If every non-candidate case is excluded, every packing of 11 unit squares in
`cbox S` has a D4 image (in the same `cbox S`) realizing exactly the cells of case 438. -/
theorem d4_bridge (hNC : NoncandidateExcluded) {S : ℝ} (hS : S ≤ Ux) {ctr : Fin 11 → ℝ × ℝ}
    {ang : Fin 11 → ℝ} (h : PackIn (cbox S) ctr ang) : RealizesIn S J438 := by
  by_contra hno
  have hP : ∀ g, PackIn (cbox S) (fun i => vw g (ctr i)) (fun i => va g (ang i)) :=
    fun g => h.vw g
  choose l hl16 hlc using fun (g : ℕ) (i : Fin 11) => exists_cell (vw g (ctr i))
  have hinj : ∀ g, Function.Injective (l g) := fun g => labels_injective hS (hP g) (hl16 g) (hlc g)
  have hsix : ∀ g, labList (l g) ∈ six := fun g =>
    mask_six hNC hS hno (labList_mem (hl16 g) (hinj g)) (realizesIn_labList (hP g) (hl16 g) (hlc g))
  have hb : ∀ i, InB (ctr i) := fun i => centre_inB hS (h.1 i)
  -- the region of each centre
  have ht : ∀ i, [l 0 i, l 1 i, l 2 i, l 3 i] ∈ regs := fun i => tuple_mem (hb i) (hl16 0 i)
    (hl16 1 i) (hl16 2 i) (hl16 3 i) (hlc 0 i) (hlc 1 i) (hlc 2 i) (hlc 3 i)
  obtain ⟨ridx, hrlt, hrt⟩ : ∃ ridx : Fin 11 → ℕ, (∀ i, ridx i < 220) ∧
      ∀ i, regs.getD (ridx i) [] = [l 0 i, l 1 i, l 2 i, l 3 i] := by
    refine ⟨fun i => regs.idxOf [l 0 i, l 1 i, l 2 i, l 3 i], fun i => ?_, fun i => ?_⟩
    · have := List.idxOf_lt_length_of_mem (ht i)
      rwa [regs_length] at this
    · have hl := List.idxOf_lt_length_of_mem (ht i)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
      exact List.getElem_idxOf hl
  have hin : ∀ i, InT (regs.getD (ridx i) []) (ctr i) := by
    intro i; rw [hrt i]; exact inT_of (a := fun g => l g i) fun g => hlc g i
  -- two centres are compatible
  have hcomp : ∀ i j, i ≠ j → (compatM.getD (ridx i) 0).testBit (ridx j) = true := by
    intro i j hij
    have hall := List.all_eq_true.mp (List.all_eq_true.mp compatM_ok (ridx i)
      (List.mem_range.mpr (hrlt i))) (ridx j) (List.mem_range.mpr (hrlt j))
    simp only [Bool.or_eq_true] at hall
    rcases hall with ((hbit | hsame) | hban) | hban
    · exact hbit
    · exfalso
      rw [hrt i, hrt j] at hsame
      simp only [sameAny, List.any_eq_true, List.mem_range, beq_iff_eq] at hsame
      obtain ⟨g, hg, he⟩ := hsame
      interval_cases g <;> exact hij (hinj _ he)
    · exfalso
      have hd := banL_ok _ (List.contains_iff_mem.mp hban) (ctr i) (ctr j) (hb i) (hb j) (hin i)
        (hin j)
      linarith [one_le_dist (h.2 i j hij)]
    · exfalso
      have hd := banL_ok _ (List.contains_iff_mem.mp hban) (ctr j) (ctr i) (hb j) (hb i) (hin j)
        (hin i)
      linarith [one_le_dist (h.2 j i (Ne.symm hij))]
  -- owners: the identity-view labels, each with its centre
  obtain ⟨cen, hcen⟩ : ∃ cen : ℕ → Fin 11, ∀ o ∈ labList (l 0), l 0 (cen o) = o := by
    refine ⟨fun o => if h : ∃ i, l 0 i = o then h.choose else 0, fun o ho => ?_⟩
    have hex := (mem_labList (hl16 0)).mp ho
    simp only [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Entry, ∀ o,
      F o = (ridx (cen o), regs.getD (ridx (cen o)) [], compatM.getD (ridx (cen o)) 0) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨rest, hrest_def⟩ : ∃ rest : List ℕ,
      rest = ownerOrder.filter fun o => (labList (l 0)).contains o := ⟨_, rfl⟩
  have hrest : ∀ o ∈ rest, o ∈ labList (l 0) := by
    intro o ho
    rw [hrest_def, List.mem_filter] at ho
    exact List.contains_iff_mem.mp ho.2
  have hs := search_unsat (hsix 0) (hsix 1) (hsix 2) (hsix 3)
  rw [← hrest_def] at hs
  have hext := ext_true domT [labList (l 1), labList (l 2), labList (l 3)] F rest (2 ^ 220 - 1)
    ?_ ?_ ?_
  · rw [hext] at hs
    exact absurd hs (by decide)
  · -- the entry of `o` is in its table and in the targets
    intro o ho
    replace ho := hrest o ho
    have ho16 : o < 16 := List.mem_range.mp (List.mem_of_mem_filter ho)
    obtain ⟨i, hi⟩ : ∃ i, cen o = i := ⟨_, rfl⟩
    have hlo : l 0 i = o := hi ▸ hcen o ho
    rw [hF, hi]
    refine ⟨mem_domT (hrlt i) ?_ ho16, ?_⟩
    · simp only [lab, hrt i, List.getD_cons_zero]
      exact hlo
    · rw [hrt i]
      simp only [inTargets, Bool.and_eq_true]
      exact ⟨⟨List.contains_iff_mem.mpr ((mem_labList (hl16 1)).mpr ⟨i, rfl⟩),
        List.contains_iff_mem.mpr ((mem_labList (hl16 2)).mpr ⟨i, rfl⟩)⟩,
        List.contains_iff_mem.mpr ((mem_labList (hl16 3)).mpr ⟨i, rfl⟩)⟩
  · -- every region is available at the start
    intro o _
    rw [hF, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (hrlt _)
  · -- the owners are pairwise compatible
    have hnd : rest.Nodup := hrest_def ▸ ownerOrder_nodup.filter _
    refine List.Pairwise.imp_of_mem ?_ hnd
    intro o o' ho ho' hne
    rw [hF, hF]
    refine hcomp _ _ fun he => hne ?_
    rw [← hcen o (hrest o ho), ← hcen o' (hrest o' ho'), he]

end SquarePacking.S11Opt.Split
