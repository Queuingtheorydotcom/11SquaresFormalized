import Sqpack.S11Opt.Split.Interface

/-!
# U1 — labels: every small packing realizes a canonical case (PROOF.md §4)

Owner: the U1/U3 session.  Input: the 16 sites `PU` of `Cells` (the author's
`center-cover-symmetric-exact.json`, sha256 df7938d9…); nothing else is read.

1. `one_le_dist` — centres of interior-disjoint unit squares are at distance `≥ 1`: the open
   disk of radius `1/2` about the centre lies in the open square.
2. `centre_inB` — a unit square in `cbox S`, `S ≤ Ux`, has its centre in `[1/2, Ux − 1/2]²`
   (the closed disk of radius `1/2` lies in the closed square).
3. `cell_disk_k` — the part of the closed cell `k` in `[1/2, Ux − 1/2]²` lies in the disk of
   squared radius `6/25` about a rational point.  Each cell is cut by at most one rational line;
   on each piece `6/25 − |p − c|²` is a nonnegative combination of the piece's linear
   constraints and of their pairwise products (degree-2 Handelman certificate, found by an LP
   and re-found exactly by `linarith`).  Hence two points of one cell are at squared distance
   `≤ 2·(6/25) + 2·(6/25) = 24/25 < 1` (`same_cell`).
4. So the 11 labels are distinct; their sorted list `J` or its half-turn `hmask J` is canonical
   (`canonical_or_hmask`, a kernel check over the 4,368 sublists), and the half-turn about the
   centre maps `cbox S` to itself.
-/

set_option linter.style.longLine false

namespace SquarePacking.S11Opt.Split

/-! ## 1–2.  Centres -/

lemma coord_sq (c : ℝ × ℝ) (θ : ℝ) (p : ℝ × ℝ) :
    (coord c θ p).1 ^ 2 + (coord c θ p).2 ^ 2 = (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 := by
  simp only [coord]
  linear_combination ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) * Real.cos_sq_add_sin_sq θ

lemma mem_sqInt_of_dist {c p : ℝ × ℝ} {θ : ℝ} (h : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 < 1 / 4) :
    p ∈ sqInt c θ 1 := by
  have e := coord_sq c θ p
  have h1 := sq_nonneg (coord c θ p).1
  have h2 := sq_nonneg (coord c θ p).2
  exact ⟨abs_lt_of_sq_lt_sq (by linarith) (by norm_num),
    abs_lt_of_sq_lt_sq (by linarith) (by norm_num)⟩

lemma mem_sq_of_dist {c p : ℝ × ℝ} {θ : ℝ} (h : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 ≤ 1 / 4) :
    p ∈ sq c θ 1 := by
  have e := coord_sq c θ p
  have h1 := sq_nonneg (coord c θ p).1
  have h2 := sq_nonneg (coord c θ p).2
  exact ⟨abs_le_of_sq_le_sq (by linarith) (by norm_num),
    abs_le_of_sq_le_sq (by linarith) (by norm_num)⟩

/-- Centres of two interior-disjoint unit squares are at distance at least `1`. -/
lemma one_le_dist {c c' : ℝ × ℝ} {θ θ' : ℝ} (h : Disjoint (sqInt c θ 1) (sqInt c' θ' 1)) :
    1 ≤ (c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 := by
  by_contra hlt
  push Not at hlt
  set m : ℝ × ℝ := ((c.1 + c'.1) / 2, (c.2 + c'.2) / 2)
  have h1 : m ∈ sqInt c θ 1 := mem_sqInt_of_dist (by simp only [m]; nlinarith)
  have h2 : m ∈ sqInt c' θ' 1 := mem_sqInt_of_dist (by simp only [m]; nlinarith)
  exact Set.disjoint_left.mp h h1 h2

/-- The centre box `[1/2, Ux − 1/2]²`. -/
def InB (p : ℝ × ℝ) : Prop := 1 / 2 ≤ p.1 ∧ p.1 ≤ Ux - 1 / 2 ∧ 1 / 2 ≤ p.2 ∧ p.2 ≤ Ux - 1 / 2

lemma centre_inB {S : ℝ} (hS : S ≤ Ux) {c : ℝ × ℝ} {θ : ℝ} (h : sq c θ 1 ⊆ cbox S) : InB c := by
  have m1 := h (mem_sq_of_dist (c := c) (p := (c.1 - 1 / 2, c.2)) (θ := θ) (by norm_num))
  have m2 := h (mem_sq_of_dist (c := c) (p := (c.1 + 1 / 2, c.2)) (θ := θ) (by norm_num))
  have m3 := h (mem_sq_of_dist (c := c) (p := (c.1, c.2 - 1 / 2)) (θ := θ) (by norm_num))
  have m4 := h (mem_sq_of_dist (c := c) (p := (c.1, c.2 + 1 / 2)) (θ := θ) (by norm_num))
  simp only [cbox, Set.mem_ofPred_eq] at m1 m2 m3 m4
  exact ⟨by linarith [m1.1], by linarith [m2.2.1], by linarith [m3.2.2.1], by linarith [m4.2.2.2]⟩

/-! ## 3.  Cells are small -/

/-- The bisector inequality of the cell `k` against the site `j`, as a linear inequality. -/
lemma cell_lin {k : ℕ} {c : ℝ × ℝ} (h : InCellU k c) (j : Fin 16) (xk yk xj yj : ℝ)
    (hk : PUn k = (xk, yk)) (hj : PU j = (xj, yj)) :
    0 ≤ (xj ^ 2 + yj ^ 2 - xk ^ 2 - yk ^ 2) - 2 * (xj - xk) * c.1 - 2 * (yj - yk) * c.2 := by
  have := h j
  rw [hk, hj] at this
  simp only at this
  nlinarith [this]

lemma diam_of_disk {p q : ℝ × ℝ} {cx cy : ℝ} (hp : (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 ≤ 6 / 25)
    (hq : (q.1 - cx) ^ 2 + (q.2 - cy) ^ 2 ≤ 6 / 25) : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 < 1 := by
  nlinarith [sq_nonneg (p.1 + q.1 - 2 * cx), sq_nonneg (p.2 + q.2 - 2 * cy)]

