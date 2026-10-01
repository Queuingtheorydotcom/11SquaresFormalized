import Sqpack.S11Opt.Split.Interface
import Sqpack.S11Opt.Split.U4.Pairs
import Sqpack.S11Opt.Split.U4.Certs

/-!
# U4 — local isolation of Trump's packing (PROOF.md §7)

Owner: c6.  The radii are those of the author's receipt
`global-math/focused1024-local-box-independent.json`.  The proof follows §7 with our own
remainder constants and dual vectors (the author's checker's inequalities are re-derived, not
imported):

* `U4/Sat.lean` — the separating-axis theorem, necessary direction (Hahn–Banach and an arc
  argument): two unit squares with disjoint interiors are weakly separated along an edge normal of
  one of them.
* `U4/Taylor.lean` — every corner gap and wall gap equals its value at Trump's packing, plus a
  linear form, plus a remainder at most `τ K` when every coordinate is at most `τ` times its radius.
* `U4/Pairs.lean`, `U4/Rows*.lean` (generated) — for each of the 14 contacting pairs, the 88
  unavailable features stay impossible in the rectangle; each of the 24 available ones gives its
  tied corner rows.  The 20 tied wall rows come from `Adm`.
* `U4/Dual.lean`, `U4/Select.lean`, `U4/Cert*.lean` — for each of the 512 selections, one of 128
  branches (42 rows each) has 66 non-negative dual vectors, checked exactly by the kernel:
  `∑ |residual_k| r_k + λ·K < r_j`.  With `τ = max_k |h_k|/r_k` and `j` saturated, this forces
  `τ = 0`.

Generator: `scripts/u4/gen_lean.py`.
-/

open Real

namespace SquarePacking.S11Opt.Split

/-- The radii `r₀ … r₃₂` of the focused rectangle (centre coordinates in unit lengths, angles in
radians; square `i` uses `r (3i)`, `r (3i+1)`, `r (3i+2)`), from the author's receipt. -/
noncomputable def focusedR : Fin 33 → ℝ := fun k => (U4.rI.getD k 0 : ℝ) / U4.DR

/-- The poses within the focused rectangle around Trump's packing (labels as in `S11Opt.ctr`). -/
def InFocused (c : Fin 11 → ℝ × ℝ) (θ : Fin 11 → ℝ) : Prop :=
  ∀ i : Fin 11, |(c i).1 - (S11Opt.ctr i).1| ≤ focusedR ⟨3 * i, by omega⟩ ∧
    |(c i).2 - (S11Opt.ctr i).2| ≤ focusedR ⟨3 * i + 1, by omega⟩ ∧
    |θ i - S11Opt.ang i| ≤ focusedR ⟨3 * i + 2, by omega⟩

namespace U4

lemma rI_pos : ∀ k < 33, 0 < rI.getD k 0 := by decide

/-- The rectangle bounds every perturbation coordinate by its radius. -/
lemma hv_le_of_focused {c : Fin 11 → ℝ × ℝ} {θ : Fin 11 → ℝ} (hf : InFocused c θ) :
    ∀ k < 33, |hvOf c θ k| ≤ (rI.getD k 0 : ℝ) / DR := by
  intro k hk
  obtain ⟨h0, h1, h2⟩ := hf ⟨k / 3, by omega⟩
  unfold hvOf
  rw [dif_pos hk]
  split_ifs with a b
  · have e : 3 * (k / 3) = k := by omega
    simpa [focusedR, e] using h0
  · have e : 3 * (k / 3) + 1 = k := by omega
    simpa [focusedR, e] using h1
  · have e : 3 * (k / 3) + 2 = k := by omega
    simpa [focusedR, e] using h2

end U4

open U4 in
/-- **U4.**  In `[0, T]²`, the only packing in the focused rectangle is Trump's. -/
theorem local_isolation {c : Fin 11 → ℝ × ℝ} {θ : Fin 11 → ℝ} (h : PackIn (box T) c θ)
    (hf : InFocused c θ) : c = S11Opt.ctr ∧ θ = S11Opt.ang := by
  obtain ⟨hin, hdis⟩ := h
  have hA : ∀ i : Fin 11, Adm T (c i) (θ i) := fun i => (sq_subset_box_iff T (c i) (θ i)).mp (hin i)
  set hv := hvOf c θ with hvdef
  set r : ℕ → ℝ := fun k => (rI.getD k 0 : ℝ) / DR with hrdef
  have hr : ∀ k < 33, 0 < r k := fun k hk => by
    have := rI_pos k hk
    simp only [r]; exact div_pos (by exact_mod_cast this) (by norm_num [DR])
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image (Finset.range 33) (fun k => |hv k| / r k)
    ⟨0, by simp⟩
  have hj' : j < 33 := Finset.mem_range.mp hj
  set τ := |hv j| / r j with hτdef
  have hb : ∀ k < 33, |hv k| ≤ τ * r k := by
    intro k hk
    have := hjmax k (Finset.mem_range.mpr hk)
    rwa [div_le_iff₀ (hr k hk)] at this
  have hτ0 : 0 ≤ τ := div_nonneg (abs_nonneg _) (hr j hj').le
  have hτ1 : τ ≤ 1 := by
    rw [hτdef, div_le_one (hr j hj')]; exact hv_le_of_focused hf j hj'
  have hb' : ∀ k < 33, |hv k| ≤ τ * rI.getD k 0 / DR := fun k hk => by
    rw [mul_div_assoc]; exact hb k hk
  rcases eq_or_lt_of_le hτ0 with h0 | hpos
  · -- every coordinate vanishes
    have hz : ∀ k < 33, hv k = 0 := fun k hk => by
      have := hb k hk; rw [← h0, zero_mul] at this; exact abs_nonpos_iff.mp this
    refine ⟨funext fun i => Prod.ext ?_ ?_, funext fun i => ?_⟩
    · have := hz (3 * i) (by omega); rw [hvdef, hv_x] at this; linarith
    · have := hz (3 * i + 1) (by omega); rw [hvdef, hv_y] at this; linarith
    · have := hz (3 * i + 2) (by omega); rw [hvdef, hv_t] at this; linarith
  · exfalso
    have H : Pert c θ τ := ⟨hτ0, hτ1, hb'⟩
    have hsat : |hv j| = τ * rI.getD j 0 / DR := by
      rw [mul_div_assoc]
      show |hv j| = |hv j| / r j * r j
      rw [div_mul_cancel₀ _ (hr j hj').ne']
    exact select_sound rowsD_eq rowsS_lt selOK_true all_branches hpos (walls_all H hA)
      (pairs_all H hdis) hb' hj' hsat

end SquarePacking.S11Opt.Split
