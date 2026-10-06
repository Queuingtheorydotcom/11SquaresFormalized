import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Sqpack.Packing

/-!
# `s(11) ≤ T`: the exact layer

Tools for the upper bound `minSide 11 ≤ T` (Trump's packing), independent of any certificate
data of the optimality proof.

* `pe`/`peQ` — polynomials as coefficient lists (low degree first), Horner evaluation.
* `hIv` — interval Horner enclosure over `ℚ`, computed by the kernel (`decide +kernel`);
  `hIv_sound` proves the enclosure.  `peQ_pos_of_hIv`, `peQ_nonneg_of_hIv` turn a computed
  positive lower bound into a sign on the whole interval.
* `disjoint_of_dir` — the sufficient direction of the separating-axis theorem, for any
  direction `(cos φ, sin φ)`: if the centres' projections are at least the sum of the two
  half-widths apart, the open squares are disjoint.
* `P`, `u₀`, `T` — the endpoint polynomial, its unique root in `(9/25, 37/100)`, and
  `T = (6u₀ + 4)/(1 + 2u₀ − u₀²)`.
-/

open scoped Classical

namespace SquarePacking.S11Opt

/-! ## 1.  Polynomials and the interval Horner check -/

/-- Horner evaluation of a real coefficient list (low degree first). -/
def pe (p : List ℝ) (x : ℝ) : ℝ := p.foldr (fun c acc => c + x * acc) 0

/-- Horner evaluation of a rational coefficient list at a real point. -/
def peQ (p : List ℚ) (x : ℝ) : ℝ := p.foldr (fun c acc => (c : ℝ) + x * acc) 0

lemma peQ_nil (x : ℝ) : peQ [] x = 0 := rfl

lemma peQ_cons (c : ℚ) (p : List ℚ) (x : ℝ) : peQ (c :: p) x = (c : ℝ) + x * peQ p x := rfl

/-- Interval enclosure of `p` on `[lo, hi]`, by Horner's scheme with interval products. -/
def hIv (lo hi : ℚ) : List ℚ → ℚ × ℚ
  | [] => (0, 0)
  | c :: p =>
    let q := hIv lo hi p
    (c + min (min (lo * q.1) (lo * q.2)) (min (hi * q.1) (hi * q.2)),
     c + max (max (lo * q.1) (lo * q.2)) (max (hi * q.1) (hi * q.2)))

/-- A product of two interval members lies between the least and greatest corner products. -/
lemma mul_mem_corners {a b c d x y : ℝ} (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  -- `x * y` lies between `x * c` and `x * d`; each of those between the corner products
  have hxc : min (a * c) (b * c) ≤ x * c ∧ x * c ≤ max (a * c) (b * c) := by
    rcases le_total 0 c with h | h
    · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
    · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩
  have hxd : min (a * d) (b * d) ≤ x * d ∧ x * d ≤ max (a * d) (b * d) := by
    rcases le_total 0 d with h | h
    · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
    · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩
  have hy : min (x * c) (x * d) ≤ x * y ∧ x * y ≤ max (x * c) (x * d) := by
    rcases le_total 0 x with h | h
    · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
    · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩
  constructor
  · have e1 : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ min (a * c) (b * c) :=
      le_min (min_le_of_left_le (min_le_left _ _)) (min_le_of_right_le (min_le_left _ _))
    have e2 : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ min (a * d) (b * d) :=
      le_min (min_le_of_left_le (min_le_right _ _)) (min_le_of_right_le (min_le_right _ _))
    rcases min_choice (x * c) (x * d) with h | h <;> rw [h] at hy <;> linarith [hxc.1, hxd.1, hy.1]
  · have e1 : max (a * c) (b * c) ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
      max_le (le_max_of_le_left (le_max_left _ _)) (le_max_of_le_right (le_max_left _ _))
    have e2 : max (a * d) (b * d) ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) :=
      max_le (le_max_of_le_left (le_max_right _ _)) (le_max_of_le_right (le_max_right _ _))
    rcases max_choice (x * c) (x * d) with h | h <;> rw [h] at hy <;> linarith [hxc.2, hxd.2, hy.2]

/-- **Soundness of the interval Horner enclosure.** -/
theorem hIv_sound (lo hi : ℚ) (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) :
    ∀ p : List ℚ, ((hIv lo hi p).1 : ℝ) ≤ peQ p x ∧ peQ p x ≤ (hIv lo hi p).2
  | [] => by simp [hIv, peQ]
  | c :: p => by
    obtain ⟨h1, h2⟩ := hIv_sound lo hi x hlo hhi p
    have hq : ((hIv lo hi p).1 : ℝ) ≤ (hIv lo hi p).2 := le_trans h1 h2
    obtain ⟨m1, m2⟩ := mul_mem_corners hlo hhi h1 h2
    have e : peQ (c :: p) x = (c : ℝ) + x * peQ p x := by simp [peQ]
    rw [e]
    simp only [hIv, Rat.cast_add, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
    constructor <;> linarith

theorem peQ_pos_of_hIv (lo hi : ℚ) (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) (p : List ℚ)
    (h : decide (0 < (hIv lo hi p).1) = true) : 0 < peQ p x := by
  have h' : (0 : ℝ) < (hIv lo hi p).1 := by exact_mod_cast of_decide_eq_true h
  linarith [(hIv_sound lo hi x hlo hhi p).1]

theorem peQ_nonneg_of_hIv (lo hi : ℚ) (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) (p : List ℚ)
    (h : decide (0 ≤ (hIv lo hi p).1) = true) : 0 ≤ peQ p x := by
  have h' : (0 : ℝ) ≤ (hIv lo hi p).1 := by exact_mod_cast of_decide_eq_true h
  linarith [(hIv_sound lo hi x hlo hhi p).1]

/-! ## 2.  Separation along a direction -/

/-- The projection of a point of a square on the direction `φ`, measured from the centre,
is at most the half-width `wid (θ - φ) / 2`, strictly for the open square. -/
lemma proj_lt_of_mem_sqInt {c p : ℝ × ℝ} {θ : ℝ} (φ : ℝ) (hp : p ∈ sqInt c θ 1) :
    |Real.cos φ * (p.1 - c.1) + Real.sin φ * (p.2 - c.2)| < wid (θ - φ) / 2 := by
  obtain ⟨hX, hY⟩ := hp
  obtain ⟨e1, e2⟩ := sub_eq_of_coord c θ p
  set X := (coord c θ p).1
  set Y := (coord c θ p).2
  have hproj : Real.cos φ * (p.1 - c.1) + Real.sin φ * (p.2 - c.2)
      = X * Real.cos (θ - φ) - Y * Real.sin (θ - φ) := by
    rw [e1, e2, Real.cos_sub, Real.sin_sub]; ring
  rw [hproj]
  have hCS := Real.cos_sq_add_sin_sq (θ - φ)
  set C := Real.cos (θ - φ)
  set S := Real.sin (θ - φ)
  have hC0 := abs_nonneg C
  have hS0 := abs_nonneg S
  have hX0 := abs_nonneg X
  have hY0 := abs_nonneg Y
  have htri : |X * C - Y * S| ≤ |X| * |C| + |Y| * |S| := by
    calc |X * C - Y * S| ≤ |X * C| + |Y * S| := abs_sub _ _
      _ = |X| * |C| + |Y| * |S| := by rw [abs_mul, abs_mul]
  have hpos : 0 < |C| ∨ 0 < |S| := by
    by_contra hcon
    push Not at hcon
    have h1 : |C| = 0 := le_antisymm hcon.1 hC0
    have h2 : |S| = 0 := le_antisymm hcon.2 hS0
    rw [abs_eq_zero] at h1 h2
    rw [h1, h2] at hCS; norm_num at hCS
  have hw : wid (θ - φ) = |C| + |S| := rfl
  rw [hw]
  rcases hpos with h | h
  · have : |X| * |C| < 1 / 2 * |C| := mul_lt_mul_of_pos_right hX h
    have : |Y| * |S| ≤ 1 / 2 * |S| := mul_le_mul_of_nonneg_right hY.le hS0
    linarith
  · have : |X| * |C| ≤ 1 / 2 * |C| := mul_le_mul_of_nonneg_right hX.le hC0
    have : |Y| * |S| < 1 / 2 * |S| := mul_lt_mul_of_pos_right hY h
    linarith

/-- **Separating axis, sufficient direction.**  If along the direction `(cos φ, sin φ)` the
centres are at least the sum of the half-widths apart, the open squares are disjoint. -/
theorem disjoint_of_dir {ci cj : ℝ × ℝ} {θi θj : ℝ} (φ : ℝ)
    (h : (wid (θi - φ) + wid (θj - φ)) / 2
        ≤ Real.cos φ * (cj.1 - ci.1) + Real.sin φ * (cj.2 - ci.2)) :
    Disjoint (sqInt ci θi 1) (sqInt cj θj 1) := by
  rw [Set.disjoint_left]
  intro p hpi hpj
  have hi := (abs_lt.mp (proj_lt_of_mem_sqInt φ hpi)).2
  have hj := (abs_lt.mp (proj_lt_of_mem_sqInt φ hpj)).1
  have e : Real.cos φ * (cj.1 - ci.1) + Real.sin φ * (cj.2 - ci.2)
      = (Real.cos φ * (p.1 - ci.1) + Real.sin φ * (p.2 - ci.2))
        - (Real.cos φ * (p.1 - cj.1) + Real.sin φ * (p.2 - cj.2)) := by ring
  linarith

lemma wid_zero : wid 0 = 1 := by simp [wid]

lemma wid_neg' (θ : ℝ) : wid (-θ) = wid θ := by simp [wid, Real.cos_neg, Real.sin_neg, abs_neg]

lemma wid_add_pi_div_two (θ : ℝ) : wid (θ + Real.pi / 2) = wid θ := by
  simp [wid, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, abs_neg, add_comm]

lemma wid_sub_add_pi_div_two (x y : ℝ) : wid (x - (y + Real.pi / 2)) = wid (x - y) := by
  rw [show x - (y + Real.pi / 2) = -((y - x) + Real.pi / 2) by ring, wid_neg',
    wid_add_pi_div_two, ← wid_neg', neg_sub]

lemma wid_sub_add_pi (x y : ℝ) : wid (x - (y + Real.pi)) = wid (x - y) := by
  rw [show x - (y + Real.pi) = x - ((y + Real.pi / 2) + Real.pi / 2) by ring,
    wid_sub_add_pi_div_two, wid_sub_add_pi_div_two]

lemma wid_sub_sub_pi_div_two (x y : ℝ) : wid (x - (y - Real.pi / 2)) = wid (x - y) := by
  rw [show x - y = x - ((y - Real.pi / 2) + Real.pi / 2) by ring, wid_sub_add_pi_div_two]

lemma wid_sub_pi_div_two (x : ℝ) : wid (x - Real.pi / 2) = wid x := by
  simpa using wid_sub_add_pi_div_two x 0

lemma wid_sub_pi (x : ℝ) : wid (x - Real.pi) = wid x := by
  simpa using wid_sub_add_pi x 0

lemma wid_add_pi (x : ℝ) : wid (x + Real.pi) = wid x := by
  rw [show x + Real.pi = (x + Real.pi / 2) + Real.pi / 2 by ring, wid_add_pi_div_two,
    wid_add_pi_div_two]

lemma wid_pi_div_two : wid (Real.pi / 2) = 1 := by
  have h := wid_add_pi_div_two 0
  rw [zero_add, wid_zero] at h
  exact h

lemma wid_pi : wid Real.pi = 1 := by
  have h := wid_sub_add_pi 0 0
  simp only [zero_add, zero_sub, sub_zero, wid_neg', wid_zero] at h
  exact h

/-! ## 3.  The endpoint polynomial and its root -/

/-- `P(u) = 5u⁸ − 10u⁷ − 2u⁶ + 14u⁵ + 12u⁴ − 6u³ + 2u² + 2u − 1`; `u = tan(θ/2)` for the tilt. -/
def P (u : ℝ) : ℝ := 5*u^8 - 10*u^7 - 2*u^6 + 14*u^5 + 12*u^4 - 6*u^3 + 2*u^2 + 2*u - 1

/-- `P'`. -/
def P' (u : ℝ) : ℝ := 40*u^7 - 70*u^6 - 12*u^5 + 70*u^4 + 48*u^3 - 18*u^2 + 4*u + 2

lemma hasDerivAt_P (x : ℝ) : HasDerivAt P (P' x) x := by
  have h := ((((((((((hasDerivAt_pow 8 x).const_mul 5).sub ((hasDerivAt_pow 7 x).const_mul 10)).sub
    ((hasDerivAt_pow 6 x).const_mul 2)).add ((hasDerivAt_pow 5 x).const_mul 14)).add
    ((hasDerivAt_pow 4 x).const_mul 12)).sub ((hasDerivAt_pow 3 x).const_mul 6)).add
    ((hasDerivAt_pow 2 x).const_mul 2)).add ((hasDerivAt_id x).const_mul 2)).sub_const 1)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)).congr_deriv ?_
  · simp [P]
  · simp only [P']; push_cast; ring

lemma P_eq_peQ (x : ℝ) : P x = peQ [-1, 2, 2, -6, 12, 14, -2, -10, 5] x := by
  simp [P, peQ]; ring

lemma P'_eq_peQ (x : ℝ) : P' x = peQ [2, 4, -18, 48, 70, -12, -70, 40] x := by
  simp [P', peQ]; ring

/-- `P' > 0` on `[9/25, 37/100]`, by the interval check on two halves. -/
lemma P'_pos {x : ℝ} (h1 : (9 / 25 : ℝ) ≤ x) (h2 : x ≤ 37 / 100) : 0 < P' x := by
  rw [P'_eq_peQ]
  rcases le_total x (73 / 200) with h | h
  · exact peQ_pos_of_hIv (9 / 25) (73 / 200) x (by push_cast; linarith) (by push_cast; linarith)
      _ (by decide +kernel)
  · exact peQ_pos_of_hIv (73 / 200) (37 / 100) x (by push_cast; linarith) (by push_cast; linarith)
      _ (by decide +kernel)

lemma P_strictMonoOn : StrictMonoOn P (Set.Icc (9 / 25) (37 / 100)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact fun x _ => (hasDerivAt_P x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_P x).deriv]
    exact P'_pos hx.1.le hx.2.le

lemma continuous_P : Continuous P := by unfold P; fun_prop

/-- A root of `P` strictly inside `(lo, hi) ⊆ [9/25, 37/100]` once `P lo < 0 < P hi`. -/
lemma exists_root_Ioo {lo hi : ℝ} (hlh : lo ≤ hi) (hlo : P lo < 0) (hhi : 0 < P hi) :
    ∃ u ∈ Set.Ioo lo hi, P u = 0 := by
  have := intermediate_value_Ioo hlh continuous_P.continuousOn
  exact this ⟨hlo, hhi⟩

/-- **The root is unique** in `(9/25, 37/100)`. -/
theorem existsUnique_root : ∃! u : ℝ, u ∈ Set.Ioo (9 / 25 : ℝ) (37 / 100) ∧ P u = 0 := by
  obtain ⟨u, hu, hPu⟩ := exists_root_Ioo (lo := 9 / 25) (hi := 37 / 100) (by norm_num)
    (by norm_num [P]) (by norm_num [P])
  refine ⟨u, ⟨hu, hPu⟩, fun v ⟨hv, hPv⟩ => ?_⟩
  exact P_strictMonoOn.injOn ⟨hv.1.le, hv.2.le⟩ ⟨hu.1.le, hu.2.le⟩ (by rw [hPu, hPv])

/-- `u₀ = tan(θ/2)` for Trump's tilt `θ ≈ 40.18°`. -/
noncomputable def u₀ : ℝ := Classical.choose existsUnique_root.exists

lemma u₀_spec : u₀ ∈ Set.Ioo (9 / 25 : ℝ) (37 / 100) ∧ P u₀ = 0 :=
  Classical.choose_spec existsUnique_root.exists

lemma P_u₀ : P u₀ = 0 := u₀_spec.2

/-- Any sign change of `P` inside `[9/25, 37/100]` brackets `u₀`. -/
lemma u₀_mem_of_sign {lo hi : ℝ} (h1 : 9 / 25 ≤ lo) (h2 : hi ≤ 37 / 100) (hlh : lo ≤ hi)
    (hlo : P lo < 0) (hhi : 0 < P hi) : lo < u₀ ∧ u₀ < hi := by
  obtain ⟨u, hu, hPu⟩ := exists_root_Ioo hlh hlo hhi
  have : u = u₀ := existsUnique_root.unique
    ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, hPu⟩ u₀_spec
  rw [← this]; exact hu

/-- The container side `T = (6u₀ + 4)/(1 + 2u₀ − u₀²) ≈ 3.8770835900`. -/
noncomputable def T : ℝ := (6 * u₀ + 4) / (1 + 2 * u₀ - u₀ ^ 2)

/-- The tilt `θ = 2·arctan u₀`. -/
noncomputable def a : ℝ := 2 * Real.arctan u₀

end SquarePacking.S11Opt
