import ElevenSquare.Tasks.T03.Wand125.Upstream.ZeroMargin

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! General packing definitions and lemmas extracted without statement changes
from evand/square-packing, revision 6e1223cf7ef2be4c70baaa36c0e7e7197076735a,
Sqpack/S32.lean. The independent 32-square certificate is not required here.
See integrations/wand125/EVAND-LICENSE.txt. -/

open Finset
open scoped Classical

namespace SquarePacking

/-! ## 1.  Packings and `s(n)` -/

/-- `n` closed unit squares with pairwise disjoint interiors fit in the square `[0,s]²`. -/
def Packs (n : ℕ) (s : ℝ) : Prop :=
  ∃ (ctr : Fin n → ℝ × ℝ) (ang : Fin n → ℝ), (∀ i, sq (ctr i) (ang i) 1 ⊆ box s) ∧
    ∀ i j, i ≠ j → Disjoint (sqInt (ctr i) (ang i) 1) (sqInt (ctr j) (ang j) 1)

/-- `s(n)`: the infimum of the sides of the squares into which `n` unit squares can be packed. -/
noncomputable def minSide (n : ℕ) : ℝ := sInf {s | Packs n s}

/-- A unit square's axis-parallel bounding box has side `w(θ) ≥ 1`. -/
lemma one_le_wid (θ : ℝ) : 1 ≤ wid θ := by
  have h := Real.cos_sq_add_sin_sq θ
  have hc := Real.abs_cos_le_one θ
  have hs := Real.abs_sin_le_one θ
  have hc0 := abs_nonneg (Real.cos θ)
  have hs0 := abs_nonneg (Real.sin θ)
  rw [← sq_abs (Real.cos θ), ← sq_abs (Real.sin θ)] at h
  unfold wid
  nlinarith

/-- Scaling by `μ > 0`: `q` is in the `μ`-square about `μ c` iff `q/μ` is in the unit square
about `c`. -/
lemma mem_sq_scale_iff {μ : ℝ} (hμ : 0 < μ) (c : ℝ × ℝ) (θ : ℝ) (q : ℝ × ℝ) :
    q ∈ sq (μ * c.1, μ * c.2) θ μ ↔ (q.1 / μ, q.2 / μ) ∈ sq c θ 1 := by
  have e1 : (coord (μ * c.1, μ * c.2) θ q).1 = μ * (coord c θ (q.1 / μ, q.2 / μ)).1 := by
    simp only [coord]; field_simp
  have e2 : (coord (μ * c.1, μ * c.2) θ q).2 = μ * (coord c θ (q.1 / μ, q.2 / μ)).2 := by
    simp only [coord]; field_simp
  simp only [sq, Set.mem_setOf_eq, e1, e2, abs_mul, abs_of_pos hμ]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- The same for interiors. -/
lemma mem_sqInt_scale_iff {μ : ℝ} (hμ : 0 < μ) (c : ℝ × ℝ) (θ : ℝ) (q : ℝ × ℝ) :
    q ∈ sqInt (μ * c.1, μ * c.2) θ μ ↔ (q.1 / μ, q.2 / μ) ∈ sqInt c θ 1 := by
  have e1 : (coord (μ * c.1, μ * c.2) θ q).1 = μ * (coord c θ (q.1 / μ, q.2 / μ)).1 := by
    simp only [coord]; field_simp
  have e2 : (coord (μ * c.1, μ * c.2) θ q).2 = μ * (coord c θ (q.1 / μ, q.2 / μ)).2 := by
    simp only [coord]; field_simp
  simp only [sqInt, Set.mem_setOf_eq, e1, e2, abs_mul, abs_of_pos hμ]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- **Lower bounds from a weighted cover.**  If every closed unit square inside `box m` captures
weight `≥ 1` from a weighted point set of total weight `< n`, then `n` unit squares cannot be
packed in `box s` for any `s < m`: scale such a packing by `m/s > 1` and apply
`packing_le_weight`. -/
theorem not_packs_of_cover (m : ℝ) (A : Finset (ℝ × ℝ)) (w : ℝ × ℝ → ℝ)
    (hw : ∀ a ∈ A, 0 ≤ w a)
    (hcover : ∀ (c : ℝ × ℝ) (θ : ℝ), sq c θ 1 ⊆ box m →
        1 ≤ ∑ a ∈ A.filter (fun a => a ∈ sq c θ 1), w a)
    (n : ℕ) (htot : ∑ a ∈ A, w a < n) {s : ℝ} (hs : s < m) : ¬ Packs n s := by
  rintro ⟨ctr, ang, hin, hdisj⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := Finset.sum_nonneg hw
    simp only [Nat.cast_zero] at htot
    linarith
  -- a unit square fits, so `s ≥ 1`
  have hs1 : 1 ≤ s := by
    obtain ⟨h1, h2, _, _⟩ := (sq_subset_box_iff s _ _).mp (hin ⟨0, hn⟩)
    linarith [one_le_wid (ang ⟨0, hn⟩)]
  have hs0 : 0 < s := by linarith
  set μ := m / s with hμdef
  have hμ : 1 < μ := (one_lt_div hs0).mpr hs
  have hμ0 : 0 < μ := by linarith
  have hμs : μ * s = m := by rw [hμdef]; field_simp
  have h := packing_le_weight A w hw (box m) hcover n μ hμ
    (fun i => (μ * (ctr i).1, μ * (ctr i).2)) ang ?_ ?_
  · linarith
  · intro i q hq
    rw [mem_sq_scale_iff hμ0] at hq
    obtain ⟨h1, h2, h3, h4⟩ := hin i hq
    simp only at h1 h2 h3 h4
    have e1 : q.1 = μ * (q.1 / μ) := by field_simp
    have e2 : q.2 = μ * (q.2 / μ) := by field_simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1]; positivity
    · rw [e1, ← hμs]; exact mul_le_mul_of_nonneg_left h2 hμ0.le
    · rw [e2]; positivity
    · rw [e2, ← hμs]; exact mul_le_mul_of_nonneg_left h4 hμ0.le
  · intro i j hij
    rw [Set.disjoint_left]
    intro q hqi hqj
    rw [mem_sqInt_scale_iff hμ0] at hqi hqj
    exact Set.disjoint_left.mp (hdisj i j hij) hqi hqj

/-! ## 2.  The grid packing -/

lemma mem_sq_zero (c p : ℝ × ℝ) (L : ℝ) :
    p ∈ sq c 0 L ↔ |p.1 - c.1| ≤ L / 2 ∧ |p.2 - c.2| ≤ L / 2 := by
  simp [sq, coord]

lemma mem_sqInt_zero (c p : ℝ × ℝ) (L : ℝ) :
    p ∈ sqInt c 0 L ↔ |p.1 - c.1| < L / 2 ∧ |p.2 - c.2| < L / 2 := by
  simp [sqInt, coord]

/-- Two open unit intervals `(a, a+1)`, `(b, b+1)` with `a ≠ b` natural numbers are disjoint. -/
lemma nat_eq_of_abs_lt {a b : ℕ} {x : ℝ} (ha : |x - ((a : ℝ) + 1 / 2)| < 1 / 2)
    (hb : |x - ((b : ℝ) + 1 / 2)| < 1 / 2) : a = b := by
  rw [abs_lt] at ha hb
  have h1 : (a : ℝ) < b + 1 := by linarith
  have h2 : (b : ℝ) < a + 1 := by linarith
  have h1' : a < b + 1 := by exact_mod_cast h1
  have h2' : b < a + 1 := by exact_mod_cast h2
  omega

/-- **The grid packing.**  The `n × n` grid of axis-parallel unit squares packs any `k ≤ n²` of
them in `[0,n]²`. -/
theorem packs_grid (n k : ℕ) (hk : k ≤ n * n) : Packs k n := by
  refine ⟨fun i => ((((i : ℕ) / n : ℕ) : ℝ) + 1 / 2, (((i : ℕ) % n : ℕ) : ℝ) + 1 / 2),
    fun _ => 0, ?_, ?_⟩
  · intro i p hp
    rw [mem_sq_zero] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [abs_le] at h1 h2
    have hi : (i : ℕ) < n * n := lt_of_lt_of_le i.2 hk
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h] at hi
      · exact h
    have hq : (i : ℕ) / n + 1 ≤ n := Nat.div_lt_of_lt_mul hi
    have hr : (i : ℕ) % n + 1 ≤ n := Nat.mod_lt _ hn
    have hq' : ((((i : ℕ) / n : ℕ) : ℝ)) + 1 ≤ n := by exact_mod_cast hq
    have hr' : ((((i : ℕ) % n : ℕ) : ℝ)) + 1 ≤ n := by exact_mod_cast hr
    have hq0 : (0 : ℝ) ≤ (((i : ℕ) / n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hr0 : (0 : ℝ) ≤ (((i : ℕ) % n : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only at h1 h2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro p hpi hpj
    rw [mem_sqInt_zero] at hpi hpj
    have e1 := nat_eq_of_abs_lt (by simpa using hpi.1) (by simpa using hpj.1)
    have e2 := nat_eq_of_abs_lt (by simpa using hpi.2) (by simpa using hpj.2)
    apply hij
    apply Fin.ext
    rw [← Nat.div_add_mod (i : ℕ) n, ← Nat.div_add_mod (j : ℕ) n, e1, e2]


end SquarePacking
