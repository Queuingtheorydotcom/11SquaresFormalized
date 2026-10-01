import ElevenSquare.Tasks.T07.Ext.Check

/-! Convex polygons given by their vertices.

`convexB V` checks that the rational vertex list `V` (at least three points) is
strictly convex and counter-clockwise: every vertex not on an edge lies strictly
to the left of it.  Then the intersection of the edge half-planes is contained in
the convex hull of `V` (`edges_subset_hull`), by a fan triangulation from `V[0]`. -/
namespace ElevenSquare.Tasks.T07.Ext
open ElevenSquare ElevenSquare.Pending
noncomputable section

/-- `cross o a b = (a - o) × (b - o)`. -/
def crossQ (o a b : QPoint) : ℚ := (a.1 - o.1) * (b.2 - o.2) - (a.2 - o.2) * (b.1 - o.1)

def crossR (o a b : Point) : ℝ := (a.1 - o.1) * (b.2 - o.2) - (a.2 - o.2) * (b.1 - o.1)

/-- The edge half-plane of `a → b`: points on the left. -/
def edgeH (a b : QPoint) : Halfplane := ⟨b.2 - a.2, a.1 - b.1, (b.2 - a.2) * a.1 + (a.1 - b.1) * a.2⟩

lemma edgeH_contains_iff (a b : QPoint) (p : Point) :
    (edgeH a b).contains p ↔ 0 ≤ crossR (realPoint a) (realPoint b) p := by
  unfold Halfplane.contains edgeH crossR realPoint
  push_cast
  constructor <;> intro h <;> nlinarith

def vtx (V : List QPoint) (k : ℕ) : QPoint := V.getD (k % V.length) (0, 0)

def edges (V : List QPoint) : Polygon := (List.range V.length).map fun k => edgeH (vtx V k) (vtx V (k + 1))

/-- Strict convexity: each vertex off an edge is strictly left of it. -/
def convexB (V : List QPoint) : Bool :=
  decide (3 ≤ V.length) &&
    (List.range V.length).all fun k => (List.range V.length).all fun m =>
      decide (m = k) || decide (m = (k + 1) % V.length) ||
        decide (0 < crossQ (vtx V k) (vtx V (k + 1)) (vtx V m))

lemma crossR_cast (o a b : QPoint) :
    crossR (realPoint o) (realPoint a) (realPoint b) = ((crossQ o a b : ℚ) : ℝ) := by
  unfold crossR crossQ realPoint; push_cast; ring

def vpts (V : List QPoint) : Set Point := {p | ∃ v ∈ V, p = realPoint v}

lemma vtx_mem (V : List QPoint) (hV : 0 < V.length) (k : ℕ) : vtx V k ∈ V := by
  unfold vtx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.mod_lt _ hV), Option.getD_some]
  exact List.getElem_mem _

/-- A point on the left of the three sides of a positively oriented triangle is a
convex combination of its vertices. -/
lemma tri_hull {a b c p : Point} (hdet : 0 < crossR a b c) (h1 : 0 ≤ crossR a b p)
    (h2 : 0 ≤ crossR b c p) (h3 : 0 ≤ crossR c a p) :
    p ∈ convexHull ℝ ({a, b, c} : Set Point) := by
  have hD : (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) ≠ 0 := hdet.ne'
  have hsum : crossR b c p / crossR a b c + crossR c a p / crossR a b c + crossR a b p / crossR a b c = 1 := by
    simp only [crossR]; field_simp; ring
  have hp : p = (crossR b c p / crossR a b c) • a + (crossR c a p / crossR a b c) • b
      + (crossR a b p / crossR a b c) • c := by
    ext
    · simp only [crossR, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp; ring
    · simp only [crossR, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp; ring
  rw [hp]
  exact conv3 (convex_convexHull ℝ _) (subset_convexHull ℝ _ (by simp))
    (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
    (div_nonneg h2 hdet.le) (div_nonneg h3 hdet.le) (div_nonneg h1 hdet.le) hsum

/-- **The edge half-planes of a strictly convex polygon lie in its hull.** -/
theorem edges_subset_hull {V : List QPoint} (hV : convexB V = true) :
    (edges V).carrier ⊆ convexHull ℝ (vpts V) := by
  intro p hp
  simp only [convexB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at hV
  obtain ⟨hn, hcv⟩ := hV
  set n := V.length with hndef
  have hn0 : 0 < n := by omega
  let w : ℕ → Point := fun k => realPoint (vtx V k)
  -- the edge inequalities
  have hedge : ∀ k < n, 0 ≤ crossR (w k) (w (k + 1)) p := by
    intro k hk
    have hmem : edgeH (vtx V k) (vtx V (k + 1)) ∈ edges V :=
      List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
    exact (edgeH_contains_iff _ _ p).mp (hp _ hmem)
  -- strict convexity at a vertex off an edge
  have hstrict : ∀ k < n, ∀ m < n, m ≠ k → m ≠ (k + 1) % n →
      0 < crossR (w k) (w (k + 1)) (w m) := by
    intro k hk m hm h1 h2
    rcases hcv k hk m hm with (h | h) | h
    · exact absurd h h1
    · exact absurd h h2
    · rw [crossR_cast]; exact_mod_cast h
  have hwn : w n = w 0 := by
    show realPoint (vtx V n) = realPoint (vtx V 0)
    unfold vtx; rw [← hndef, Nat.mod_self, Nat.zero_mod]
  -- cyclic and antisymmetric rules
  have cyc : ∀ a b c : Point, crossR a b c = crossR b c a := by intros; simp only [crossR]; ring
  have anti : ∀ a b c : Point, crossR a b c = -crossR a c b := by intros; simp only [crossR]; ring
  let f : ℕ → ℝ := fun k => crossR (w 0) (w k) p
  have f1 : 0 ≤ f 1 := by simpa [f] using hedge 0 hn0
  have flast : f (n - 1) ≤ 0 := by
    have := hedge (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega, hwn, cyc, anti] at this
    simp only [f]; linarith
  -- the first fan index where `f` turns non-positive
  have hex : ∃ m, 1 ≤ m ∧ m + 1 ≤ n - 1 ∧ f (m + 1) ≤ 0 :=
    ⟨n - 2, by omega, by omega, by rw [show n - 2 + 1 = n - 1 by omega]; exact flast⟩
  classical
  let m := Nat.find hex
  obtain ⟨hm1, hm2, hfm⟩ := Nat.find_spec hex
  have hfm0 : 0 ≤ f m := by
    rcases Nat.lt_or_ge 1 m with hlt | hle
    · have hmin := Nat.find_min hex (show m - 1 < m by omega)
      push Not at hmin
      have := hmin (by omega) (by omega)
      rw [show m - 1 + 1 = m by omega] at this
      exact this.le
    · have : m = 1 := by omega
      rw [this]; exact f1
  have hdet : 0 < crossR (w 0) (w m) (w (m + 1)) := by
    have := hstrict m (by omega) 0 hn0 (by omega) (by
      rw [Nat.mod_eq_of_lt (by omega : m + 1 < n)]; omega)
    rw [cyc]; exact this
  have h3 : 0 ≤ crossR (w (m + 1)) (w 0) p := by
    rw [cyc, anti]; simp only [f] at hfm; linarith
  have hin := tri_hull hdet hfm0 (hedge m (by omega)) h3
  refine convexHull_mono ?_ hin
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> exact ⟨_, vtx_mem V hn0 _, rfl⟩

end
end ElevenSquare.Tasks.T07.Ext
