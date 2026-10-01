import Sqpack.S11Opt.Split.U4.Select

/-!
# U4 — the base pose, the perturbation vector and small evaluation lemmas

* `cos_q*`, `sin_q*`, `cos_dq*`, `sin_dq*`: trigonometry at quarter turns.
* `ctr_*`, `ang_*`: the centres and angles of Trump's packing, one lemma per square.
* `encl`: an interval enclosure of a rational polynomial at `u₀`, from `hIv`.
* `hvOf c θ`: the 33 perturbation coordinates of a pose `(c, θ)` (centre offsets and angle
  offsets, square by square), and `Pert`: all of them at most `τ` times the radii.
-/

open Real

namespace SquarePacking.S11Opt.Split.U4

open SquarePacking.S11Opt

/-! ## Quarter turns -/

lemma cos_q0 (t : ℝ) : cos (t + 0 * (π / 2)) = cos t := by simp
lemma cos_q1 (t : ℝ) : cos (t + 1 * (π / 2)) = -sin t := by rw [one_mul, cos_add_pi_div_two]
lemma cos_q2 (t : ℝ) : cos (t + 2 * (π / 2)) = -cos t := by
  rw [show (2 : ℝ) * (π / 2) = π by ring, cos_add_pi]
lemma cos_q3 (t : ℝ) : cos (t + 3 * (π / 2)) = sin t := by
  rw [show t + 3 * (π / 2) = (t + π) + π / 2 by ring, cos_add_pi_div_two, sin_add_pi, neg_neg]
lemma sin_q0 (t : ℝ) : sin (t + 0 * (π / 2)) = sin t := by simp
lemma sin_q1 (t : ℝ) : sin (t + 1 * (π / 2)) = cos t := by rw [one_mul, sin_add_pi_div_two]
lemma sin_q2 (t : ℝ) : sin (t + 2 * (π / 2)) = -sin t := by
  rw [show (2 : ℝ) * (π / 2) = π by ring, sin_add_pi]
lemma sin_q3 (t : ℝ) : sin (t + 3 * (π / 2)) = -cos t := by
  rw [show t + 3 * (π / 2) = (t + π) + π / 2 by ring, sin_add_pi_div_two, cos_add_pi]

lemma cos_dq0 (b t : ℝ) : cos (b - (t + 0 * (π / 2))) = cos (b - t) := by simp
lemma cos_dq1 (b t : ℝ) : cos (b - (t + 1 * (π / 2))) = sin (b - t) := by
  rw [show b - (t + 1 * (π / 2)) = (b - t) - π / 2 by ring, cos_sub_pi_div_two]
lemma cos_dq2 (b t : ℝ) : cos (b - (t + 2 * (π / 2))) = -cos (b - t) := by
  rw [show b - (t + 2 * (π / 2)) = (b - t) - π by ring, cos_sub_pi]
lemma cos_dq3 (b t : ℝ) : cos (b - (t + 3 * (π / 2))) = -sin (b - t) := by
  rw [show b - (t + 3 * (π / 2)) = ((b - t) - π) - π / 2 by ring, cos_sub_pi_div_two, sin_sub_pi]
lemma sin_dq0 (b t : ℝ) : sin (b - (t + 0 * (π / 2))) = sin (b - t) := by simp
lemma sin_dq1 (b t : ℝ) : sin (b - (t + 1 * (π / 2))) = -cos (b - t) := by
  rw [show b - (t + 1 * (π / 2)) = (b - t) - π / 2 by ring, sin_sub_pi_div_two]
lemma sin_dq2 (b t : ℝ) : sin (b - (t + 2 * (π / 2))) = -sin (b - t) := by
  rw [show b - (t + 2 * (π / 2)) = (b - t) - π by ring, sin_sub_pi]
lemma sin_dq3 (b t : ℝ) : sin (b - (t + 3 * (π / 2))) = cos (b - t) := by
  rw [show b - (t + 3 * (π / 2)) = ((b - t) - π) - π / 2 by ring, sin_sub_pi_div_two, cos_sub_pi,
    neg_neg]

/-! ## The base pose -/

lemma ctr_0 : ctr 0 = (x0, y0) := rfl
lemma ctr_1 : ctr 1 = (x1, y1) := rfl
lemma ctr_2 : ctr 2 = (x2, y2) := rfl
lemma ctr_3 : ctr 3 = (x3, y3) := rfl
lemma ctr_4 : ctr 4 = (x4, y4) := rfl
lemma ctr_5 : ctr 5 = (x5, y5) := rfl
lemma ctr_6 : ctr 6 = (x6, y6) := rfl
lemma ctr_7 : ctr 7 = (x7, y7) := rfl
lemma ctr_8 : ctr 8 = (x8, y8) := rfl
lemma ctr_9 : ctr 9 = (x9, y9) := rfl
lemma ctr_10 : ctr 10 = (x10, y10) := rfl
lemma ang_0 : ang 0 = 0 := rfl
lemma ang_1 : ang 1 = 0 := rfl
lemma ang_2 : ang 2 = 0 := rfl
lemma ang_3 : ang 3 = 0 := rfl
lemma ang_4 : ang 4 = 0 := rfl
lemma ang_5 : ang 5 = 0 := rfl
lemma ang_6 : ang 6 = a := rfl
lemma ang_7 : ang 7 = a := rfl
lemma ang_8 : ang 8 = a := rfl
lemma ang_9 : ang 9 = a := rfl
lemma ang_10 : ang 10 = a := rfl

/-- An enclosure of a rational polynomial at `u₀`, checked by `hIv`. -/
lemma encl (p : List ℚ) (L H : ℚ) (h : decide (L ≤ (hIv lo hi p).1 ∧ (hIv lo hi p).2 ≤ H) = true) :
    (L : ℝ) ≤ peQ p u₀ ∧ peQ p u₀ ≤ H := by
  have hs := hIv_sound lo hi u₀ u₀_bounds.1 u₀_bounds.2 p
  have h' := of_decide_eq_true h
  exact ⟨le_trans (by exact_mod_cast h'.1) hs.1, le_trans hs.2 (by exact_mod_cast h'.2)⟩

/-! ## The perturbation -/

/-- The perturbation coordinates: `3i`, `3i+1` the centre offsets and `3i+2` the angle offset of
square `i`. -/
noncomputable def hvOf (c : Fin 11 → ℝ × ℝ) (θ : Fin 11 → ℝ) (n : ℕ) : ℝ :=
  if h : n < 33 then
    if n % 3 = 0 then (c ⟨n / 3, by omega⟩).1 - (ctr ⟨n / 3, by omega⟩).1
    else if n % 3 = 1 then (c ⟨n / 3, by omega⟩).2 - (ctr ⟨n / 3, by omega⟩).2
    else θ ⟨n / 3, by omega⟩ - ang ⟨n / 3, by omega⟩
  else 0

lemma hv_x (c : Fin 11 → ℝ × ℝ) (θ : Fin 11 → ℝ) (i : Fin 11) :
    hvOf c θ (3 * i) = (c i).1 - (ctr i).1 := by
  have h1 : 3 * (i : ℕ) < 33 := by omega
  have h2 : (⟨3 * (i : ℕ) / 3, by omega⟩ : Fin 11) = i := Fin.ext (by simp)
  simp only [hvOf, h1, dif_pos, Nat.mul_mod_right, if_true, h2]

lemma hv_y (c : Fin 11 → ℝ × ℝ) (θ : Fin 11 → ℝ) (i : Fin 11) :
    hvOf c θ (3 * i + 1) = (c i).2 - (ctr i).2 := by
  have h1 : 3 * (i : ℕ) + 1 < 33 := by omega
  have h2 : (⟨(3 * (i : ℕ) + 1) / 3, by omega⟩ : Fin 11) = i := Fin.ext (by simp; omega)
  have h3 : (3 * (i : ℕ) + 1) % 3 = 1 := by omega
  simp only [hvOf, h1, dif_pos, h3, h2, one_ne_zero, if_false, if_true]

lemma hv_t (c : Fin 11 → ℝ × ℝ) (θ : Fin 11 → ℝ) (i : Fin 11) :
    hvOf c θ (3 * i + 2) = θ i - ang i := by
  have h1 : 3 * (i : ℕ) + 2 < 33 := by omega
  have h2 : (⟨(3 * (i : ℕ) + 2) / 3, by omega⟩ : Fin 11) = i := Fin.ext (by simp; omega)
  have h3 : (3 * (i : ℕ) + 2) % 3 = 2 := by omega
  simp only [hvOf, h1, dif_pos, h3, h2, two_ne_zero, if_false, OfNat.ofNat_ne_one]

/-- The radii, in units of `1/DR`. -/
def rI : List ℕ := [18767167, 22176635, 22681452, 16360330, 13760362, 17641130, 8962451, 10424794,
  22681452, 16350530, 10683139, 15120968, 16348076, 13962901, 20161291, 12900283, 10683060,
  15120968, 13565580, 8248658, 35312013, 11182451, 6465674, 35297932, 9356857, 8671199, 15099566,
  7338775, 10335557, 40352153, 7680628, 32891612, 67647473]

/-- A perturbation at most `τ ≤ 1` times the radii. -/
structure Pert (c : Fin 11 → ℝ × ℝ) (θ : Fin 11 → ℝ) (τ : ℝ) : Prop where
  τ0 : 0 ≤ τ
  τ1 : τ ≤ 1
  hb : ∀ k < 33, |hvOf c θ k| ≤ τ * rI.getD k 0 / DR

/-! ## Reductions used by every row -/

lemma pgap_add_int_two_pi (co cp : ℝ × ℝ) (α β s1 s2 : ℝ) (n : ℤ) :
    pgap co cp (α + n * (2 * π)) β s1 s2 = pgap co cp α β s1 s2 := by
  unfold pgap
  rw [show β - (α + n * (2 * π)) = (β - α) - n * (2 * π) by ring, cos_add_int_mul_two_pi,
    sin_add_int_mul_two_pi, cos_sub_int_mul_two_pi, sin_sub_int_mul_two_pi]

/-- A separation feature only depends on the edge normal modulo a full turn. -/
lemma feat_mod4 {co cp : ℝ × ℝ} {t β : ℝ} (k : ℤ) (h : Feat co cp (t + k * (π / 2)) β) :
    Feat co cp (t + ((k % 4 : ℤ) : ℝ) * (π / 2)) β := by
  have e : t + k * (π / 2) = (t + ((k % 4 : ℤ) : ℝ) * (π / 2)) + ((k / 4 : ℤ) : ℝ) * (2 * π) := by
    have h0 := congrArg (fun z : ℤ => (z : ℝ)) (Int.mul_ediv_add_emod k 4)
    have h' : (k : ℝ) = ((k % 4 : ℤ) : ℝ) + 4 * ((k / 4 : ℤ) : ℝ) := by
      simp only [Int.cast_add, Int.cast_mul] at h0; push_cast at h0; linarith
    rw [h']; ring
  rw [e] at h
  unfold Feat at h ⊢
  simp only [pgap_add_int_two_pi] at h
  exact h

lemma mod4_cases (k : ℤ) : ((k % 4 : ℤ) : ℝ) = 0 ∨ ((k % 4 : ℤ) : ℝ) = 1 ∨
    ((k % 4 : ℤ) : ℝ) = 2 ∨ ((k % 4 : ℤ) : ℝ) = 3 := by
  have h0 := Int.emod_nonneg k (by norm_num : (4 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 4)
  rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with e | e | e | e <;>
    rw [e] <;> norm_num

/-- Admissibility gives the sixteen corner-wall inequalities. -/
lemma wgap_nonneg {m : ℝ} {c : ℝ × ℝ} {θ s1 s2 : ℝ} (h : Adm m c θ) (h1 : s1 = 1 ∨ s1 = -1)
    (h2 : s2 = 1 ∨ s2 = -1) :
    0 ≤ wgap c.1 1 0 θ s1 s2 ∧ 0 ≤ wgap c.1 (-1) m θ s1 s2 ∧ 0 ≤ wgap c.2 1 0 θ s1 s2 ∧
      0 ≤ wgap c.2 (-1) m θ s1 s2 := by
  have h1' : -s1 = 1 ∨ -s1 = -1 := by rcases h1 with rfl | rfl <;> norm_num
  have h2' : -s2 = 1 ∨ -s2 = -1 := by rcases h2 with rfl | rfl <;> norm_num
  have hw := corner_proj_ge θ (-s1) (-s2) h1' h2'
  obtain ⟨a1, a2, a3, a4⟩ := h
  unfold wgap
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The linear form of a row is at most `τ` times the weighted radii. -/
lemma lin4_le {C S G Z a b x y τ A B W V : ℝ} (ha : |a| ≤ τ * A) (hb : |b| ≤ τ * B)
    (hx : |x| ≤ τ * W) (hy : |y| ≤ τ * V) :
    C * a + S * b + G * x + Z * y ≤ τ * (|C| * A + |S| * B + |G| * W + |Z| * V) := by
  have e1 : C * a ≤ |C| * (τ * A) :=
    le_trans (le_abs_self _) (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left ha (abs_nonneg _))
  have e2 : S * b ≤ |S| * (τ * B) :=
    le_trans (le_abs_self _) (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hb (abs_nonneg _))
  have e3 : G * x ≤ |G| * (τ * W) :=
    le_trans (le_abs_self _) (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _))
  have e4 : Z * y ≤ |Z| * (τ * V) :=
    le_trans (le_abs_self _) (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy (abs_nonneg _))
  linarith

/-- A perturbation coordinate at most `τ` times its radius, with the radius as a literal. -/
lemma Pert.bd {c : Fin 11 → ℝ × ℝ} {θ : Fin 11 → ℝ} {τ : ℝ} (H : Pert c θ τ) {k : ℕ} (hk : k < 33)
    {r : ℝ} (hr : ((rI.getD k 0 : ℕ) : ℝ) / DR = r) : |hvOf c θ k| ≤ τ * r := by
  have := H.hb k hk; rw [← hr]; rw [mul_div_assoc] at this; exact this

end SquarePacking.S11Opt.Split.U4
