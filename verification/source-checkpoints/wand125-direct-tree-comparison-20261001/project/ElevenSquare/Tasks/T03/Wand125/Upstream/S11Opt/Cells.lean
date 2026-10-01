import ElevenSquare.Tasks.T03.KernelBoolRefl
import ElevenSquare.Tasks.T03.Wand125.Upstream.S11Opt.Basic

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

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

/-! ## Cases -/

/-- A packing in `[0, Ux]²` has distinct squares with centres in the closed cells `a ∈ J`. -/
def Realizes (J : List ℕ) : Prop :=
  ∃ (n : ℕ) (ctr : Fin n → ℝ × ℝ) (ang : Fin n → ℝ), (∀ i, sq (ctr i) (ang i) 1 ⊆ box Ux) ∧
    (∀ i j, i ≠ j → Disjoint (sqInt (ctr i) (ang i) 1) (sqInt (ctr j) (ang j) 1)) ∧
    ∃ σ : ℕ → Fin n, (∀ a ∈ J, ∀ b ∈ J, σ a = σ b → a = b) ∧ ∀ a ∈ J, InCellU a (ctr (σ a))

/-- The case `J` is excluded. -/
def CaseExcluded (J : List ℕ) : Prop := ¬ Realizes J

/-- The half-turn image of a cell set. -/
def hmask (J : List ℕ) : List ℕ := (J.map (15 - ·)).reverse

/-- The canonical 11-cell sets: `J ≤ hmask J` lexicographically. -/
def canonicalMasks : List (List ℕ) :=
  (List.sublistsLen 11 (List.range 16)).filter fun J => !decide (hmask J < J)

end SquarePacking.S11Opt
