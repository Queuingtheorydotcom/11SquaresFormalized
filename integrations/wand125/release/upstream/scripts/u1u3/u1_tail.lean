/-- Two points of one closed cell, both in the centre box, are at distance `< 1`. -/
theorem same_cell {k : ℕ} (hk : k < 16) {p q : ℝ × ℝ} (hp : InCellU k p) (hq : InCellU k q)
    (hbp : InB p) (hbq : InB q) : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 < 1 := by
  interval_cases k
@@CASES@@

/-! ## 4.  Labels and the half-turn -/

lemma mem_cbox_hpt {S : ℝ} {p : ℝ × ℝ} : hpt p ∈ cbox S ↔ p ∈ cbox S := by
  simp only [cbox, hpt, Set.mem_ofPred_eq]; constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma sq_subset_cbox_hpt {S : ℝ} {c : ℝ × ℝ} {θ : ℝ} (h : sq c θ 1 ⊆ cbox S) :
    sq (hpt c) θ 1 ⊆ cbox S := by
  intro q hq
  rw [← hpt_hpt q] at hq ⊢
  exact mem_cbox_hpt.mpr (h (mem_sq_hpt.mp hq))

/-- The half-turn about the centre of `cbox S` transfers a realization to `hmask J`. -/
lemma RealizesIn.hmask {S : ℝ} {J : List ℕ} (hJ : ∀ a ∈ J, a < 16) (h : RealizesIn S J) :
    RealizesIn S (hmask J) := by
  obtain ⟨n, ctr, ang, ⟨hin, hd⟩, σ, hσ, hc⟩ := h
  have mem : ∀ b ∈ S11Opt.hmask J, 15 - b ∈ J ∧ 15 - (15 - b) = b := by
    intro b hb
    simp only [S11Opt.hmask, List.mem_reverse, List.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have := hJ a ha
    refine ⟨?_, by omega⟩
    rw [show 15 - (15 - a) = a by omega]; exact ha
  refine ⟨n, fun i => hpt (ctr i), ang, ⟨fun i => sq_subset_cbox_hpt (hin i),
    fun i j hij => disjoint_hpt (hd i j hij)⟩, fun b => σ (15 - b), ?_, ?_⟩
  · intro b hb b' hb' h
    have := hσ _ (mem b hb).1 _ (mem b' hb').1 h
    have e1 := (mem b hb).2
    have e2 := (mem b' hb').2
    omega
  · intro b hb
    have h1 := inCell_hpt (hJ _ (mem b hb).1) (hc _ (mem b hb).1)
    rwa [(mem b hb).2] at h1

/-- The test that `J` or its half-turn image is canonical. -/
def canOrH (J : List ℕ) : Bool :=
  (!decide (hmask J < J)) || ((hmask J).isSublist (List.range 16) && (hmask J).length == 11 &&
    !decide (hmask (hmask J) < hmask J))

/-- Every 11-cell set, or its half-turn image, is canonical (kernel check over 4,368 sets). -/
lemma canOrH_all : (List.sublistsLen 11 (List.range 16)).all canOrH = true := by decide +kernel

lemma canonical_or_hmask {J : List ℕ} (hJ : J ∈ List.sublistsLen 11 (List.range 16)) :
    J ∈ canonicalMasks ∨ hmask J ∈ canonicalMasks := by
  have h := List.all_eq_true.mp canOrH_all J hJ
  simp only [canOrH, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h | ⟨⟨h1, h2⟩, h3⟩
  · exact Or.inl (List.mem_filter.mpr ⟨hJ, h⟩)
  · refine Or.inr (List.mem_filter.mpr ⟨List.mem_sublistsLen.mpr ⟨?_, h2⟩, h3⟩)
    exact List.isSublist_iff_sublist.mp h1

/-- The sorted list of the labels `l i`. -/
def labList {n : ℕ} (l : Fin n → ℕ) : List ℕ :=
  (List.range 16).filter fun a => decide (∃ i, l i = a)

lemma mem_labList {n : ℕ} {l : Fin n → ℕ} (hl16 : ∀ i, l i < 16) {a : ℕ} :
    a ∈ labList l ↔ ∃ i, l i = a := by
  simp only [labList, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · rintro ⟨i, rfl⟩; exact ⟨hl16 i, i, rfl⟩

/-- Labels of a packing in `cbox S` are distinct, whichever containing closed cells are chosen. -/
theorem labels_injective {S : ℝ} (hS : S ≤ Ux) {ctr : Fin 11 → ℝ × ℝ} {ang : Fin 11 → ℝ}
    (h : PackIn (cbox S) ctr ang) {l : Fin 11 → ℕ} (hl16 : ∀ i, l i < 16)
    (hlc : ∀ i, InCellU (l i) (ctr i)) : Function.Injective l := by
  intro i j hij
  by_contra hne
  have h1 := one_le_dist (h.2 i j hne)
  have h2 := same_cell (hl16 i) (hlc i) (hij ▸ hlc j) (centre_inB hS (h.1 i))
    (centre_inB hS (h.1 j))
  linarith

lemma labList_mem {l : Fin 11 → ℕ} (hl16 : ∀ i, l i < 16) (hinj : Function.Injective l) :
    labList l ∈ List.sublistsLen 11 (List.range 16) := by
  refine List.mem_sublistsLen.mpr ⟨List.filter_sublist, ?_⟩
  have hnd : (labList l).Nodup := List.nodup_range.filter _
  have hfs : (labList l).toFinset = Finset.univ.image l := by
    ext a; simp [List.mem_toFinset, mem_labList hl16]
  rw [← List.toFinset_card_of_nodup hnd, hfs, Finset.card_image_of_injective _ hinj]
  simp

/-- A packing realizes the list of its labels. -/
theorem realizesIn_labList {S : ℝ} {ctr : Fin 11 → ℝ × ℝ} {ang : Fin 11 → ℝ}
    (h : PackIn (cbox S) ctr ang) {l : Fin 11 → ℕ} (hl16 : ∀ i, l i < 16)
    (hlc : ∀ i, InCellU (l i) (ctr i)) : RealizesIn S (labList l) := by
  let σ : ℕ → Fin 11 := fun a => if h : ∃ i, l i = a then h.choose else 0
  have hσ : ∀ a ∈ labList l, l (σ a) = a := by
    intro a ha
    have hex := (mem_labList hl16).mp ha
    simp only [σ, dif_pos hex]
    exact hex.choose_spec
  refine ⟨11, ctr, ang, h, σ, ?_, ?_⟩
  · intro a ha b hb e
    rw [← hσ a ha, ← hσ b hb, e]
  · intro a ha
    have := hlc (σ a)
    rwa [hσ a ha] at this

/-- **U1.**  A packing of 11 unit squares in `cbox S` (`S ≤ Ux`) realizes some canonical case. -/
theorem realizes_canonical {S : ℝ} (hS : S ≤ Ux) {ctr : Fin 11 → ℝ × ℝ} {ang : Fin 11 → ℝ}
    (h : PackIn (cbox S) ctr ang) : ∃ J ∈ canonicalMasks, RealizesIn S J := by
  choose l hl16 hlc using fun i => exists_cell (ctr i)
  have hinj := labels_injective hS h hl16 hlc
  have hR := realizesIn_labList h hl16 hlc
  have hJ16 : ∀ a ∈ labList l, a < 16 := fun a ha => List.mem_range.mp (List.mem_of_mem_filter ha)
  rcases canonical_or_hmask (labList_mem hl16 hinj) with hc | hc
  · exact ⟨labList l, hc, hR⟩
  · exact ⟨hmask (labList l), hc, hR.hmask hJ16⟩

end SquarePacking.S11Opt.Split
