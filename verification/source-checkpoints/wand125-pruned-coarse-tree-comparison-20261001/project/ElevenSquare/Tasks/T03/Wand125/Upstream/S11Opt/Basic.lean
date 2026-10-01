import ElevenSquare.Tasks.T03.KernelBoolRefl
import ElevenSquare.Tasks.T03.Wand125.Upstream.Packing

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# `s(11) ≤ T`: the exact layer

Tools for the upper bound `minSide 11 ≤ T` (Trump's packing), independent of any certificate
data of the optimality proof.

* `pe`/`peQ` — polynomials as coefficient lists (low degree first), Horner evaluation.
* `hIv` — interval Horner enclosure over `ℚ`, computed by the kernel (`exact of_decide_eq_true (by t03_bool_refl)`);
  `hIv_sound` proves the enclosure.  `peQ_pos_of_hIv`, `peQ_nonneg_of_hIv` turn a computed
  positive lower bound into a sign on the whole interval.
* `disjoint_of_dir` — the sufficient direction of the separating-axis theorem, for any
  direction `(cos φ, sin φ)`: if the centres' projections are at least the sum of the two
  half-widths apart, the open squares are disjoint.
The independent endpoint-root and upper-bound construction is preserved in
the original upstream source and omitted from this case-checker closure.
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
    have hcon : |C| ≤ 0 ∧ |S| ≤ 0 :=
      ⟨le_of_not_gt (not_or.mp hcon).1, le_of_not_gt (not_or.mp hcon).2⟩
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

end SquarePacking.S11Opt
