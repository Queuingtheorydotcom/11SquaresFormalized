import Sqpack.S11Opt.Upper

/-!
# U4 — the separating-axis theorem, necessary direction

Two closed unit squares with disjoint interiors are weakly separated along an edge normal of one
of them (`sat_necessary`): all four corners of one square lie beyond an edge line of the other.

Proof.  Hahn–Banach separates the two open squares by a direction `φ`; projecting the extreme
corners gives `sepH φ ≥ 0`.  The eight edge normals cut the circle into arcs of length at most
`π/2`; on the arc containing `φ` the function `sepH` is `ψ ↦ (cos ψ, sin ψ) · G` for a fixed
vector `G`, and `(cos φ, sin φ)` is a non-negative combination of the directions at the two
ends of the arc.  So `sepH ≥ 0` at an end, which is an edge normal.
-/

open Real

namespace SquarePacking.S11Opt.Split

/-- The gap of the corner `(s₁/2, s₂/2)` of the square `(cp, β)` beyond the edge line of a
square centred at `co` whose outer edge normal is `(cos α, sin α)`. -/
noncomputable def pgap (co cp : ℝ × ℝ) (α β s1 s2 : ℝ) : ℝ :=
  cos α * (cp.1 - co.1) + sin α * (cp.2 - co.2) + (s1 * cos (β - α) - s2 * sin (β - α)) / 2
    - 1 / 2

/-- A separation feature: the four corners of `(cp, β)` lie beyond the edge line with outer
normal `(cos α, sin α)` of the unit square centred at `co`. -/
def Feat (co cp : ℝ × ℝ) (α β : ℝ) : Prop :=
  0 ≤ pgap co cp α β 1 1 ∧ 0 ≤ pgap co cp α β 1 (-1) ∧ 0 ≤ pgap co cp α β (-1) 1 ∧
    0 ≤ pgap co cp α β (-1) (-1)

/-- Separation along the direction `φ`, measured by the projections of the extreme corners. -/
noncomputable def sepH (ci cj : ℝ × ℝ) (θi θj φ : ℝ) : ℝ :=
  cos φ * (cj.1 - ci.1) + sin φ * (cj.2 - ci.2) - (wid (φ - θi) + wid (φ - θj)) / 2

lemma wid_add_int_mul (x : ℝ) (k : ℤ) : wid (x + k * (π / 2)) = wid x := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show x + ((n + 1 : ℤ) : ℝ) * (π / 2) = (x + (n : ℝ) * (π / 2)) + π / 2 by push_cast; ring,
      wid_add_pi_div_two, ← ih]
    norm_cast
  | pred n ih =>
    rw [← ih, show x + ((-(n : ℤ) : ℤ) : ℝ) * (π / 2) = (x + ((-(n : ℤ) - 1 : ℤ) : ℝ) * (π / 2)) + π / 2
      by push_cast; ring, wid_add_pi_div_two]

lemma wid_int_mul (k : ℤ) : wid (k * (π / 2)) = 1 := by
  simpa [wid_zero] using wid_add_int_mul 0 k

/-- The projection of a corner offset on a direction is at least `-wid/2`. -/
lemma corner_proj_ge (t s1 s2 : ℝ) (h1 : s1 = 1 ∨ s1 = -1) (h2 : s2 = 1 ∨ s2 = -1) :
    -(wid t) / 2 ≤ (s1 * cos t + s2 * sin t) / 2 := by
  have a1 := neg_abs_le (cos t); have a2 := le_abs_self (cos t)
  have b1 := neg_abs_le (sin t); have b2 := le_abs_self (sin t)
  unfold wid
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> linarith

lemma feat_of_sepH_left {ci cj : ℝ × ℝ} {θi θj : ℝ} (k : ℤ)
    (h : 0 ≤ sepH ci cj θi θj (θi + k * (π / 2))) : Feat ci cj (θi + k * (π / 2)) θj := by
  set ψ := θi + k * (π / 2) with hψ
  have hw : wid (ψ - θi) = 1 := by rw [hψ, add_sub_cancel_left, wid_int_mul]
  unfold sepH at h
  rw [hw] at h
  have key : ∀ s1 s2 : ℝ, (s1 = 1 ∨ s1 = -1) → (s2 = 1 ∨ s2 = -1) → 0 ≤ pgap ci cj ψ θj s1 s2 := by
    intro s1 s2 h1 h2
    have hc := corner_proj_ge (ψ - θj) s1 s2 h1 h2
    have e1 : cos (θj - ψ) = cos (ψ - θj) := by rw [← cos_neg, neg_sub]
    have e2 : sin (θj - ψ) = -sin (ψ - θj) := by rw [← sin_neg, neg_sub]
    unfold pgap; rw [e1, e2]; linarith
  exact ⟨key 1 1 (by norm_num) (by norm_num), key 1 (-1) (by norm_num) (by norm_num),
    key (-1) 1 (by norm_num) (by norm_num), key (-1) (-1) (by norm_num) (by norm_num)⟩

lemma feat_of_sepH_right {ci cj : ℝ × ℝ} {θi θj : ℝ} (k : ℤ)
    (h : 0 ≤ sepH ci cj θi θj (θj + k * (π / 2))) :
    Feat cj ci (θj + ((k + 2 : ℤ) : ℝ) * (π / 2)) θi := by
  set ψ := θj + k * (π / 2) with hψ
  have hw : wid (ψ - θj) = 1 := by rw [hψ, add_sub_cancel_left, wid_int_mul]
  have e : θj + ((k + 2 : ℤ) : ℝ) * (π / 2) = ψ + π := by rw [hψ]; push_cast; ring
  rw [e]
  unfold sepH at h
  rw [hw] at h
  have key : ∀ s1 s2 : ℝ, (s1 = 1 ∨ s1 = -1) → (s2 = 1 ∨ s2 = -1) →
      0 ≤ pgap cj ci (ψ + π) θi s1 s2 := by
    intro s1 s2 h1 h2
    have h1' : -s1 = 1 ∨ -s1 = -1 := by rcases h1 with rfl | rfl <;> norm_num
    have h2' : -s2 = 1 ∨ -s2 = -1 := by rcases h2 with rfl | rfl <;> norm_num
    have hc := corner_proj_ge (ψ - θi) (-s1) (-s2) h1' h2'
    have e1 : cos (θi - (ψ + π)) = -cos (ψ - θi) := by
      rw [show θi - (ψ + π) = -(ψ - θi) - π by ring, cos_sub_pi, cos_neg]
    have e2 : sin (θi - (ψ + π)) = sin (ψ - θi) := by
      rw [show θi - (ψ + π) = -(ψ - θi) - π by ring, sin_sub_pi, sin_neg, neg_neg]
    unfold pgap; rw [e1, e2, cos_add_pi, sin_add_pi]; linarith
  exact ⟨key 1 1 (by norm_num) (by norm_num), key 1 (-1) (by norm_num) (by norm_num),
    key (-1) 1 (by norm_num) (by norm_num), key (-1) (-1) (by norm_num) (by norm_num)⟩

/-- On an arc of length `≤ π/2` starting at `γ`, `wid (ψ - θ)` is linear in `(cos ψ, sin ψ)`. -/
lemma wid_on_arc {θ ψ : ℝ} (m : ℤ) (h1 : θ + m * (π / 2) ≤ ψ) (h2 : ψ ≤ θ + m * (π / 2) + π / 2) :
    wid (ψ - θ) = cos ψ * (cos (θ + m * (π / 2)) - sin (θ + m * (π / 2)))
      + sin ψ * (sin (θ + m * (π / 2)) + cos (θ + m * (π / 2))) := by
  set γ := θ + m * (π / 2) with hγ
  have e : ψ - θ = (ψ - γ) + m * (π / 2) := by rw [hγ]; ring
  rw [e, wid_add_int_mul]
  have hc : 0 ≤ cos (ψ - γ) := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith⟩
  have hs : 0 ≤ sin (ψ - γ) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  rw [wid, abs_of_nonneg hc, abs_of_nonneg hs, cos_sub, sin_sub]
  ring

/-- **The arc argument.** -/
lemma sepH_edge {ci cj : ℝ × ℝ} {θi θj φ : ℝ} (h : 0 ≤ sepH ci cj θi θj φ) :
    ∃ k : ℤ, 0 ≤ sepH ci cj θi θj (θi + k * (π / 2)) ∨ 0 ≤ sepH ci cj θi θj (θj + k * (π / 2)) := by
  have hp : (0 : ℝ) < π / 2 := by linarith [pi_pos]
  set m := ⌊(φ - θi) / (π / 2)⌋ with hm
  set n := ⌊(φ - θj) / (π / 2)⌋ with hn
  have fl : ∀ (θ : ℝ), θ + (⌊(φ - θ) / (π / 2)⌋ : ℝ) * (π / 2) ≤ φ ∧
      φ < θ + (⌊(φ - θ) / (π / 2)⌋ : ℝ) * (π / 2) + π / 2 := by
    intro θ
    have a := Int.floor_le ((φ - θ) / (π / 2))
    have b := Int.lt_floor_add_one ((φ - θ) / (π / 2))
    have a' := mul_le_mul_of_nonneg_right a hp.le
    have b' := mul_lt_mul_of_pos_right b hp
    rw [div_mul_cancel₀ _ hp.ne'] at a' b'
    constructor <;> nlinarith
  obtain ⟨hi1, hi2⟩ := fl θi
  obtain ⟨hj1, hj2⟩ := fl θj
  rw [← hm] at hi1 hi2
  rw [← hn] at hj1 hj2
  set γi := θi + (m : ℝ) * (π / 2) with hγi
  set γj := θj + (n : ℝ) * (π / 2) with hγj
  set α1 := max γi γj with hα1
  set α2 := min (γi + π / 2) (γj + π / 2) with hα2
  have h1φ : α1 ≤ φ := max_le hi1 hj1
  have hφ2 : φ ≤ α2 := le_min hi2.le hj2.le
  -- the linear form of `sepH` on `[α1, α2]`
  set Gx := (cj.1 - ci.1) - ((cos γi - sin γi) + (cos γj - sin γj)) / 2 with hGx
  set Gy := (cj.2 - ci.2) - ((sin γi + cos γi) + (sin γj + cos γj)) / 2 with hGy
  have lin : ∀ ψ, α1 ≤ ψ → ψ ≤ α2 → sepH ci cj θi θj ψ = cos ψ * Gx + sin ψ * Gy := by
    intro ψ ha hb
    have wi := wid_on_arc (θ := θi) (ψ := ψ) m (le_trans (le_max_left _ _) ha)
      (le_trans hb (min_le_left _ _))
    have wj := wid_on_arc (θ := θj) (ψ := ψ) n (le_trans (le_max_right _ _) ha)
      (le_trans hb (min_le_right _ _))
    unfold sepH; rw [wi, wj]; ring
  -- the ends of the arc are edge normals
  have end1 : 0 ≤ sepH ci cj θi θj α1 → ∃ k : ℤ,
      0 ≤ sepH ci cj θi θj (θi + k * (π / 2)) ∨ 0 ≤ sepH ci cj θi θj (θj + k * (π / 2)) := by
    intro hs
    rcases max_choice γi γj with e | e
    · exact ⟨m, Or.inl (by rw [← hγi, ← e]; exact hs)⟩
    · exact ⟨n, Or.inr (by rw [← hγj, ← e]; exact hs)⟩
  have end2 : 0 ≤ sepH ci cj θi θj α2 → ∃ k : ℤ,
      0 ≤ sepH ci cj θi θj (θi + k * (π / 2)) ∨ 0 ≤ sepH ci cj θi θj (θj + k * (π / 2)) := by
    intro hs
    rcases min_choice (γi + π / 2) (γj + π / 2) with e | e
    · refine ⟨m + 1, Or.inl ?_⟩
      rw [show θi + ((m + 1 : ℤ) : ℝ) * (π / 2) = γi + π / 2 by rw [hγi]; push_cast; ring, ← e]
      exact hs
    · refine ⟨n + 1, Or.inr ?_⟩
      rw [show θj + ((n + 1 : ℤ) : ℝ) * (π / 2) = γj + π / 2 by rw [hγj]; push_cast; ring, ← e]
      exact hs
  rcases eq_or_lt_of_le (le_trans h1φ hφ2) with heq | hlt
  · exact end1 (by rw [le_antisymm h1φ (heq ▸ hφ2)]; exact h)
  by_cases H1 : 0 ≤ sepH ci cj θi θj α1
  · exact end1 H1
  by_cases H2 : 0 ≤ sepH ci cj θi θj α2
  · exact end2 H2
  exfalso
  push Not at H1 H2
  have hw : α2 - α1 ≤ π / 2 := by
    have := min_le_left (γi + π / 2) (γj + π / 2)
    have := le_max_left γi γj
    linarith
  have sA : 0 < sin (α2 - α1) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have sa : 0 ≤ sin (α2 - φ) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  have sb : 0 ≤ sin (φ - α1) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  have sab : 0 < sin (α2 - φ) ∨ 0 < sin (φ - α1) := by
    rcases eq_or_lt_of_le h1φ with e | e
    · left; exact sin_pos_of_pos_of_lt_pi (by rw [← e]; linarith) (by linarith [pi_pos])
    · right; exact sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have comb : sin (α2 - α1) * sepH ci cj θi θj φ
      = sin (α2 - φ) * sepH ci cj θi θj α1 + sin (φ - α1) * sepH ci cj θi θj α2 := by
    rw [lin φ h1φ hφ2, lin α1 le_rfl hlt.le, lin α2 hlt.le le_rfl]
    simp only [sin_sub]; ring
  have lhs : 0 ≤ sin (α2 - α1) * sepH ci cj θi θj φ := mul_nonneg sA.le h
  rcases sab with p | p
  · nlinarith [mul_neg_of_pos_of_neg p H1, mul_nonpos_of_nonneg_of_nonpos sb H2.le]
  · nlinarith [mul_neg_of_pos_of_neg p H2, mul_nonpos_of_nonneg_of_nonpos sa H1.le]

/-! ## Hahn–Banach and the extreme corners -/

lemma coord_continuous (c : ℝ × ℝ) (θ : ℝ) : Continuous fun p : ℝ × ℝ => coord c θ p := by
  unfold coord; fun_prop

lemma sqInt_isOpen (c : ℝ × ℝ) (θ : ℝ) : IsOpen (sqInt c θ 1) := by
  have hc := coord_continuous c θ
  exact (isOpen_lt (continuous_abs.comp (continuous_fst.comp hc)) continuous_const).inter
    (isOpen_lt (continuous_abs.comp (continuous_snd.comp hc)) continuous_const)

lemma abs_comb_lt {X Y a b : ℝ} (hX : |X| < 1 / 2) (hY : |Y| < 1 / 2) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : |a * X + b * Y| < 1 / 2 := by
  have e : |a * X + b * Y| ≤ a * |X| + b * |Y| := by
    calc |a * X + b * Y| ≤ |a * X| + |b * Y| := abs_add_le _ _
      _ = a * |X| + b * |Y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  rcases eq_or_lt_of_le ha with h | h
  · subst h; simp at hab; subst hab; linarith
  · nlinarith [mul_le_mul_of_nonneg_left hY.le hb]

lemma sqInt_convex (c : ℝ × ℝ) (θ : ℝ) : Convex ℝ (sqInt c θ 1) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  have e1 : (coord c θ (a • p + b • q)).1 = a * (coord c θ p).1 + b * (coord c θ q).1 := by
    simp only [coord, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (c.1 * cos θ + c.2 * sin θ) * hab
  have e2 : (coord c θ (a • p + b • q)).2 = a * (coord c θ p).2 + b * (coord c θ q).2 := by
    simp only [coord, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (c.2 * cos θ - c.1 * sin θ) * hab
  exact ⟨by rw [e1]; exact abs_comb_lt hp1 hq1 ha hb hab,
    by rw [e2]; exact abs_comb_lt hp2 hq2 ha hb hab⟩

lemma centre_mem_sqInt (c : ℝ × ℝ) (θ : ℝ) : c ∈ sqInt c θ 1 := by
  simp [sqInt, coord]

/-- The point at rotated offset `(x, y)` from `c`. -/
noncomputable def offs (c : ℝ × ℝ) (θ x y : ℝ) : ℝ × ℝ :=
  (c.1 + (x * cos θ - y * sin θ), c.2 + (x * sin θ + y * cos θ))

lemma offs_mem_sqInt (c : ℝ × ℝ) (θ x y : ℝ) (hx : |x| < 1 / 2) (hy : |y| < 1 / 2) :
    offs c θ x y ∈ sqInt c θ 1 := by
  have hCS : cos θ ^ 2 + sin θ ^ 2 = 1 := cos_sq_add_sin_sq θ
  have h1 : (coord c θ (offs c θ x y)).1 = x * (cos θ ^ 2 + sin θ ^ 2) := by
    simp only [coord, offs]; ring
  have h2 : (coord c θ (offs c θ x y)).2 = y * (cos θ ^ 2 + sin θ ^ 2) := by
    simp only [coord, offs]; ring
  exact ⟨by rw [h1, hCS, mul_one]; exact hx, by rw [h2, hCS, mul_one]; exact hy⟩

/-- A linear functional below `u` on the open square is `≤ u` at every closed offset. -/
lemma le_of_open {f : ℝ × ℝ → ℝ} {c : ℝ × ℝ} {θ u x y : ℝ}
    (hf : ∀ p q : ℝ × ℝ, ∀ t : ℝ, f (p + t • (q - p)) = f p + t * (f q - f p))
    (hA : ∀ p ∈ sqInt c θ 1, f p < u) (hx : |x| ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    f (offs c θ x y) ≤ u := by
  have hc := hA c (centre_mem_sqInt c θ)
  have line : ∀ t : ℝ, 0 ≤ t → t < 1 → f c + t * (f (offs c θ x y) - f c) < u := by
    intro t ht0 ht1
    have hmem : c + t • (offs c θ x y - c) ∈ sqInt c θ 1 := by
      have e : c + t • (offs c θ x y - c) = offs c θ (t * x) (t * y) := by
        ext <;> simp [offs] <;> ring
      rw [e]
      refine offs_mem_sqInt c θ _ _ ?_ ?_
      · rw [abs_mul, abs_of_nonneg ht0]; nlinarith [abs_nonneg x]
      · rw [abs_mul, abs_of_nonneg ht0]; nlinarith [abs_nonneg y]
    rw [← hf]; exact hA _ hmem
  by_contra hcon
  push Not at hcon
  have hpos : 0 < f (offs c θ x y) - f c := by linarith
  have := line ((u - f c) / (f (offs c θ x y) - f c)) (div_nonneg (by linarith) hpos.le)
    ((div_lt_one hpos).mpr (by linarith))
  rw [div_mul_cancel₀ _ hpos.ne'] at this
  linarith

/-- The extreme offset: its projection on `(cos φ, sin φ)` is `wid (φ - θ) / 2`. -/
lemma offs_proj (c : ℝ × ℝ) (θ φ x y : ℝ) :
    cos φ * ((offs c θ x y).1 - c.1) + sin φ * ((offs c θ x y).2 - c.2)
      = x * cos (φ - θ) + y * sin (φ - θ) := by
  simp only [offs, cos_sub, sin_sub]; ring

lemma sgn_mul (t : ℝ) : (if 0 ≤ t then (1 / 2 : ℝ) else -1 / 2) * t = |t| / 2 := by
  split_ifs with h
  · rw [abs_of_nonneg h]; ring
  · rw [abs_of_neg (not_le.mp h)]; ring

lemma abs_sgn (t : ℝ) : |(if 0 ≤ t then (1 / 2 : ℝ) else -1 / 2)| ≤ 1 / 2 := by
  split_ifs <;> norm_num [abs_div]

/-- **Separating axis, necessary direction.** -/
theorem sat_necessary {ci cj : ℝ × ℝ} {θi θj : ℝ}
    (hdis : Disjoint (sqInt ci θi 1) (sqInt cj θj 1)) :
    ∃ k : ℤ, Feat ci cj (θi + k * (π / 2)) θj ∨ Feat cj ci (θj + k * (π / 2)) θi := by
  obtain ⟨f, u, hA, hB⟩ := geometric_hahn_banach_open_open (sqInt_convex ci θi)
    (sqInt_isOpen ci θi) (sqInt_convex cj θj) (sqInt_isOpen cj θj) hdis
  set fa := f (1, 0)
  set fb := f (0, 1)
  have hf : ∀ p : ℝ × ℝ, f p = fa * p.1 + fb * p.2 := by
    intro p
    have : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
  have hlin : ∀ p q : ℝ × ℝ, ∀ t : ℝ, f (p + t • (q - p)) = f p + t * (f q - f p) := by
    intro p q t; rw [hf, hf, hf]; simp; ring
  have hci := hA ci (centre_mem_sqInt ci θi)
  have hcj := hB cj (centre_mem_sqInt cj θj)
  -- polar form of `(fa, fb)`
  set z : ℂ := ⟨fa, fb⟩
  have hz : z ≠ 0 := by
    intro h0
    have h1 : fa = 0 := congrArg Complex.re h0
    have h2 : fb = 0 := congrArg Complex.im h0
    have : fa * ci.1 + fb * ci.2 < fa * cj.1 + fb * cj.2 := by rw [← hf, ← hf]; linarith
    rw [h1, h2] at this; simp at this
  set ρ := ‖z‖
  have hρ : 0 < ρ := norm_pos_iff.mpr hz
  set φ := Complex.arg z
  have hcos : fa = ρ * cos φ := by
    have e : z.re = fa := rfl
    rw [Complex.cos_arg hz, e]; field_simp; rfl
  have hsin : fb = ρ * sin φ := by
    have e : z.im = fb := rfl
    rw [Complex.sin_arg, e]; field_simp; rfl
  -- extreme corners
  set xi := (if 0 ≤ cos (φ - θi) then (1 / 2 : ℝ) else -1 / 2)
  set yi := (if 0 ≤ sin (φ - θi) then (1 / 2 : ℝ) else -1 / 2)
  set xj := (if 0 ≤ cos (φ - θj) then (1 / 2 : ℝ) else -1 / 2)
  set yj := (if 0 ≤ sin (φ - θj) then (1 / 2 : ℝ) else -1 / 2)
  have hAi := le_of_open hlin hA (abs_sgn _) (abs_sgn _) (c := ci) (θ := θi) (x := xi) (y := yi)
  have hneg : ∀ p ∈ sqInt cj θj 1, (fun q => -f q) p < -u := fun p hp => by
    simp only; linarith [hB p hp]
  have hlin' : ∀ p q : ℝ × ℝ, ∀ t : ℝ,
      (fun q => -f q) (p + t • (q - p)) = (fun q => -f q) p + t * ((fun q => -f q) q - (fun q => -f q) p) := by
    intro p q t; simp only; rw [hlin]; ring
  have hBj := le_of_open hlin' hneg (c := cj) (θ := θj) (x := -xj) (y := -yj)
    (by rw [abs_neg]; exact abs_sgn _) (by rw [abs_neg]; exact abs_sgn _)
  have pi' := offs_proj ci θi φ xi yi
  have pj' := offs_proj cj θj φ (-xj) (-yj)
  rw [sgn_mul, sgn_mul] at pi'
  have pj'' : cos φ * ((offs cj θj (-xj) (-yj)).1 - cj.1) + sin φ * ((offs cj θj (-xj) (-yj)).2 - cj.2)
      = -(|cos (φ - θj)| / 2 + |sin (φ - θj)| / 2) := by
    rw [pj', ← sgn_mul (cos (φ - θj)), ← sgn_mul (sin (φ - θj))]; ring
  have hH : 0 ≤ sepH ci cj θi θj φ := by
    simp only [hf] at hAi hBj hci hcj
    have eA : fa * (offs ci θi xi yi).1 + fb * (offs ci θi xi yi).2
        = fa * ci.1 + fb * ci.2 + ρ * (|cos (φ - θi)| / 2 + |sin (φ - θi)| / 2) := by
      rw [hcos, hsin]; linear_combination ρ * pi'
    have eB : fa * (offs cj θj (-xj) (-yj)).1 + fb * (offs cj θj (-xj) (-yj)).2
        = fa * cj.1 + fb * cj.2 - ρ * (|cos (φ - θj)| / 2 + |sin (φ - θj)| / 2) := by
      rw [hcos, hsin]; linear_combination ρ * pj''
    have eH : ρ * sepH ci cj θi θj φ = (fa * cj.1 + fb * cj.2) - (fa * ci.1 + fb * ci.2)
        - ρ * ((|cos (φ - θi)| + |sin (φ - θi)|) + (|cos (φ - θj)| + |sin (φ - θj)|)) / 2 := by
      unfold sepH wid; rw [hcos, hsin]; ring
    have : 0 ≤ ρ * sepH ci cj θi θj φ := by rw [eH]; linarith
    exact (mul_nonneg_iff_of_pos_left hρ).mp this
  obtain ⟨k, hk | hk⟩ := sepH_edge hH
  · exact ⟨k, Or.inl (feat_of_sepH_left k hk)⟩
  · exact ⟨k + 2, Or.inr (feat_of_sepH_right k hk)⟩

end SquarePacking.S11Opt.Split
