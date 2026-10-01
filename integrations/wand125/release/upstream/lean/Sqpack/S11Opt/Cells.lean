import Sqpack.S11Opt.Basic

/-!
# Cells, cases and the half-turn (stage S0)

* `Ux` — the author's rational upper value `U` of the side (`T < Ux`, `T_lt_U`).
* `PU`, `InCellU` — the 16 closed Voronoi cells of the author's centre cover
  (`center-cover-symmetric-exact.json`, sha256 df7938d9…), in unit coordinates of `[0, Ux]²`:
  site `PU k = 1/2 + (Ux − 1) v_k` for the author's normalized site `v_k`.  Every point has a
  nearest site, so the cells cover the plane; the author's cell polygons are these Voronoi cells
  clipped to the container (checked exactly against all listed vertices).
* `Realizes J` — some packing of unit squares in `[0, Ux]²` has distinct squares with centres in
  the closed cells `a ∈ J`; `CaseExcluded J := ¬ Realizes J`.
* `hpt`, `hmask` — the half-turn about the centre of the container, on points and on cell sets
  (`a ↦ 15 − a`); `realizes_hmask` transfers a realization to the half-turn image.
* `canonicalMasks` — the 11-cell sets `J` with `J ≤ hmask J` (lexicographic); `2184` of them, in
  the same set as the author's `canonical_eleven_cell_subsets`.
-/

namespace SquarePacking.S11Opt

/-- The author's rational upper value of the side, `U = 3.87708359002281417731`. -/
noncomputable def Ux : ℝ := 387708359002281417731 / 10 ^ 20

/-- Voronoi sites of the 16 cells, unit coordinates. -/
noncomputable def PU : Fin 16 → ℝ × ℝ := ![((80206788320008528328995421 / 100000000000000000000000000 : ℝ), (176483527032089485245355847 / 200000000000000000000000000 : ℝ)), ((78686667498184714830022331 / 50000000000000000000000000 : ℝ), (63091593459680811351013693 / 100000000000000000000000000 : ℝ)), ((464596403987128110649685633 / 200000000000000000000000000 : ℝ), (22480315265430140099670659 / 25000000000000000000000000 : ℝ)), ((598058557561106414706741913 / 200000000000000000000000000 : ℝ), (19894392534717634717104431 / 25000000000000000000000000 : ℝ)), ((159319997167449384989195311 / 200000000000000000000000000 : ℝ), (165192385068974431749720049 / 100000000000000000000000000 : ℝ)), ((313569079679342521477316341 / 200000000000000000000000000 : ℝ), (140033439907660930894815023 / 100000000000000000000000000 : ℝ)), ((232768749014712286583541867 / 100000000000000000000000000 : ℝ), (67877260313210648443197979 / 40000000000000000000000000 : ℝ)), ((153156523725617232432678909 / 50000000000000000000000000 : ℝ), (73266817431299737482805753 / 50000000000000000000000000 : ℝ)), ((40697655775523476432821091 / 50000000000000000000000000 : ℝ), (120587362069840971382694247 / 50000000000000000000000000 : ℝ)), ((154939609987569131147458133 / 100000000000000000000000000 : ℝ), (87206083287701918649202021 / 40000000000000000000000000 : ℝ)), ((461847638325220313984683659 / 200000000000000000000000000 : ℝ), (247674919094620486836184977 / 100000000000000000000000000 : ℝ)), ((616096720837113450472804689 / 200000000000000000000000000 : ℝ), (222515973933306985981279951 / 100000000000000000000000000 : ℝ)), ((177358160443456420755258087 / 200000000000000000000000000 : ℝ), (77032697215852719715645569 / 25000000000000000000000000 : ℝ)), ((310820314017434724812314367 / 200000000000000000000000000 : ℝ), (74446774485140214333079341 / 25000000000000000000000000 : ℝ)), ((115167512002955994035477669 / 50000000000000000000000000 : ℝ), (324616765542600606379986307 / 100000000000000000000000000 : ℝ)), ((307501570682272889402004579 / 100000000000000000000000000 : ℝ), (598933190972473350216644153 / 200000000000000000000000000 : ℝ))]

/-- The site of cell `k` (indices mod 16). -/
noncomputable def PUn (k : ℕ) : ℝ × ℝ := PU ⟨k % 16, Nat.mod_lt _ (by norm_num)⟩

/-- The closed Voronoi cell `k`. -/
def InCellU (k : ℕ) (c : ℝ × ℝ) : Prop :=
  ∀ j : Fin 16, (c.1 - (PUn k).1) ^ 2 + (c.2 - (PUn k).2) ^ 2
    ≤ (c.1 - (PU j).1) ^ 2 + (c.2 - (PU j).2) ^ 2

/-- Every point lies in some cell. -/
theorem exists_cell (c : ℝ × ℝ) : ∃ k < 16, InCellU k c := by
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ
    (fun j : Fin 16 => (c.1 - (PU j).1) ^ 2 + (c.2 - (PU j).2) ^ 2) Finset.univ_nonempty
  refine ⟨j, j.isLt, fun i => ?_⟩
  have : PUn j = PU j := by simp [PUn, Nat.mod_eq_of_lt j.isLt]
  rw [this]
  exact hj i (Finset.mem_univ _)

/-! ## The half-turn -/

/-- The half-turn about the centre of `[0, Ux]²`. -/
noncomputable def hpt (p : ℝ × ℝ) : ℝ × ℝ := (Ux - p.1, Ux - p.2)

lemma PU_rev : ∀ j : Fin 16, PU (Fin.rev j) = hpt (PU j) := by
  intro j; fin_cases j <;> simp [PU, Ux, hpt, Fin.rev] <;> norm_num

lemma coord_hpt (c : ℝ × ℝ) (θ : ℝ) (p : ℝ × ℝ) :
    coord (hpt c) θ (hpt p) = (-(coord c θ p).1, -(coord c θ p).2) := by
  simp only [coord, hpt]; ext <;> simp <;> ring

lemma mem_sq_hpt {c p : ℝ × ℝ} {θ L : ℝ} : hpt p ∈ sq (hpt c) θ L ↔ p ∈ sq c θ L := by
  simp only [sq, Set.mem_ofPred_eq, coord_hpt, abs_neg]

lemma mem_sqInt_hpt {c p : ℝ × ℝ} {θ L : ℝ} : hpt p ∈ sqInt (hpt c) θ L ↔ p ∈ sqInt c θ L := by
  simp only [sqInt, Set.mem_ofPred_eq, coord_hpt, abs_neg]

lemma hpt_hpt (p : ℝ × ℝ) : hpt (hpt p) = p := by simp [hpt]

lemma mem_box_hpt {p : ℝ × ℝ} : hpt p ∈ box Ux ↔ p ∈ box Ux := by
  simp only [box, hpt, Set.mem_ofPred_eq]; constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma sq_subset_box_hpt {c : ℝ × ℝ} {θ : ℝ} (h : sq c θ 1 ⊆ box Ux) : sq (hpt c) θ 1 ⊆ box Ux := by
  intro q hq
  rw [← hpt_hpt q] at hq ⊢
  exact mem_box_hpt.mpr (h (mem_sq_hpt.mp hq))

lemma disjoint_hpt {c c' : ℝ × ℝ} {θ θ' : ℝ} (h : Disjoint (sqInt c θ 1) (sqInt c' θ' 1)) :
    Disjoint (sqInt (hpt c) θ 1) (sqInt (hpt c') θ' 1) := by
  rw [Set.disjoint_left] at h ⊢
  intro q h1 h2
  rw [← hpt_hpt q] at h1 h2
  exact h (mem_sqInt_hpt.mp h1) (mem_sqInt_hpt.mp h2)

lemma dist_hpt (p q : ℝ × ℝ) :
    ((hpt p).1 - (hpt q).1) ^ 2 + ((hpt p).2 - (hpt q).2) ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  simp only [hpt]; ring

lemma inCell_hpt {a : ℕ} (ha : a < 16) {c : ℝ × ℝ} (h : InCellU a c) : InCellU (15 - a) (hpt c) := by
  have e1 : PUn (15 - a) = hpt (PUn a) := by
    have := PU_rev ⟨a, ha⟩
    simp only [PUn, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show 15 - a < 16 by omega)]
    rw [← this]; congr 1; ext; simp [Fin.rev]
  intro j
  rw [e1, dist_hpt, ← hpt_hpt (PU j), ← PU_rev, dist_hpt]
  exact h (Fin.rev j)

/-! ## Cases -/

/-- A packing in `[0, Ux]²` has distinct squares with centres in the closed cells `a ∈ J`. -/
def Realizes (J : List ℕ) : Prop :=
  ∃ (n : ℕ) (ctr : Fin n → ℝ × ℝ) (ang : Fin n → ℝ), (∀ i, sq (ctr i) (ang i) 1 ⊆ box Ux) ∧
    (∀ i j, i ≠ j → Disjoint (sqInt (ctr i) (ang i) 1) (sqInt (ctr j) (ang j) 1)) ∧
    ∃ σ : ℕ → Fin n, (∀ a ∈ J, ∀ b ∈ J, σ a = σ b → a = b) ∧ ∀ a ∈ J, InCellU a (ctr (σ a))

/-- The case `J` is excluded. -/
def CaseExcluded (J : List ℕ) : Prop := ¬ Realizes J

lemma Realizes.mono {J K : List ℕ} (h : Realizes J) (hKJ : ∀ a ∈ K, a ∈ J) : Realizes K := by
  obtain ⟨n, ctr, ang, hin, hd, σ, hσ, hc⟩ := h
  exact ⟨n, ctr, ang, hin, hd, σ, fun a ha b hb => hσ a (hKJ a ha) b (hKJ b hb),
    fun a ha => hc a (hKJ a ha)⟩

/-- The half-turn image of a cell set. -/
def hmask (J : List ℕ) : List ℕ := (J.map (15 - ·)).reverse

lemma Realizes.hmask {J : List ℕ} (hJ : ∀ a ∈ J, a < 16) (h : Realizes J) :
    Realizes (hmask J) := by
  obtain ⟨n, ctr, ang, hin, hd, σ, hσ, hc⟩ := h
  have mem : ∀ b ∈ S11Opt.hmask J, 15 - b ∈ J ∧ 15 - (15 - b) = b := by
    intro b hb
    simp only [S11Opt.hmask, List.mem_reverse, List.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have := hJ a ha
    refine ⟨?_, by omega⟩
    rw [show 15 - (15 - a) = a by omega]; exact ha
  refine ⟨n, fun i => hpt (ctr i), ang, fun i => sq_subset_box_hpt (hin i),
    fun i j hij => disjoint_hpt (hd i j hij), fun b => σ (15 - b), ?_, ?_⟩
  · intro b hb b' hb' h
    have := hσ _ (mem b hb).1 _ (mem b' hb').1 h
    have e1 := (mem b hb).2
    have e2 := (mem b' hb').2
    omega
  · intro b hb
    have h1 := inCell_hpt (hJ _ (mem b hb).1) (hc _ (mem b hb).1)
    rwa [(mem b hb).2] at h1

/-- The canonical 11-cell sets: `J ≤ hmask J` lexicographically. -/
def canonicalMasks : List (List ℕ) :=
  (List.sublistsLen 11 (List.range 16)).filter fun J => !decide (hmask J < J)

lemma canonicalMasks_length : canonicalMasks.length = 2184 := by decide +kernel

lemma canonicalMasks_lt : ∀ J ∈ canonicalMasks, ∀ a ∈ J, a < 16 := by decide +kernel

end SquarePacking.S11Opt
