import ElevenSquare.Tasks.T07.Ext.Trace
import Mathlib.Analysis.Convex.Combination

/-! Convex polygons given by their vertices.

`convexB V` checks that the rational vertex list `V` (at least three points) is
strictly convex and counter-clockwise: every vertex not on an edge lies strictly
to the left of it.  Then the intersection of the edge half-planes is contained in
the convex hull of `V` (`edges_subset_hull`), by a fan triangulation from `V[0]`. -/
namespace ElevenSquare.Tasks.T07.Ext
open ElevenSquare ElevenSquare.Pending
noncomputable section

lemma conv3 {S : Set Point} (hS : Convex ℝ S) {x y z : Point} (hx : x ∈ S) (hy : y ∈ S)
    (hz : z ∈ S) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) :
    a • x + b • y + c • z ∈ S := by
  have := hS.sum_mem (t := Finset.univ) (w := ![a, b, c]) (z := ![x, y, z])
    (by intro i _; fin_cases i <;> simp [ha, hb, hc])
    (by simp [Fin.sum_univ_three, habc])
    (by intro i _; fin_cases i <;> simp [hx, hy, hz])
  simpa [Fin.sum_univ_three] using this

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

/-! ## Linear bounds on hulls -/

/-- A half-plane holding at every vertex holds on the hull. -/
theorem hull_contains {V : List QPoint} {g : Halfplane} (h : ∀ v ∈ V, g.contains (realPoint v))
    {x : Point} (hx : x ∈ convexHull ℝ (vpts V)) : g.contains x := by
  have hconv : Convex ℝ {y : Point | g.contains y} := by
    intro a ha b hb s t hs ht hst
    simp only [Set.mem_ofPred_eq, Halfplane.contains, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at ha hb ⊢
    have e : (g.a : ℝ) * (s * a.1 + t * b.1) + g.b * (s * a.2 + t * b.2)
        = s * (g.a * a.1 + g.b * a.2) + t * (g.a * b.1 + g.b * b.2) := by ring
    have e2 : s * (g.c : ℝ) + t * g.c = g.c := by rw [← add_mul, hst, one_mul]
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left ha hs, mul_le_mul_of_nonneg_left hb ht]
  have hsub : vpts V ⊆ {y : Point | g.contains y} := by
    rintro y ⟨v, hv, rfl⟩; exact h v hv
  exact convexHull_min hsub hconv hx

/-! ## Minkowski differences of cores -/

def lowKey (p : QPoint) (q : QPoint) : Bool := decide (p.2 < q.2 ∨ (p.2 = q.2 ∧ p.1 < q.1))

/-- The index of the lowest vertex (least `y`, then least `x`). -/
def lowIdx (V : List QPoint) : ℕ :=
  ((List.range V.length).foldl (fun acc k => if lowKey (vtx V k) (vtx V acc) then k else acc) 0)

def rotL (V : List QPoint) (k : ℕ) : List QPoint := V.drop k ++ V.take k

def negL (V : List QPoint) : List QPoint := V.map fun p => (-p.1, -p.2)

/-- Merge of the edge sequences of two counter-clockwise polygons, both starting at
their lowest vertex.  Returns pairs `(a, b)` with `a ∈ A`, `b ∈ B`; the polygon of
the Minkowski sum has the vertices `a + b`. -/
def mergeAux (A B : List QPoint) : ℕ → ℕ → ℕ → List (QPoint × QPoint)
  | 0, _, _ => []
  | f + 1, i, j =>
    if A.length ≤ i ∧ B.length ≤ j then [] else
      (vtx A i, vtx B j) ::
        (if A.length ≤ i then mergeAux A B f i (j + 1)
         else if B.length ≤ j then mergeAux A B f (i + 1) j
         else
           let ea : QPoint := ((vtx A (i + 1)).1 - (vtx A i).1, (vtx A (i + 1)).2 - (vtx A i).2)
           let eb : QPoint := ((vtx B (j + 1)).1 - (vtx B j).1, (vtx B (j + 1)).2 - (vtx B j).2)
           let c := ea.1 * eb.2 - ea.2 * eb.1
           if 0 < c then mergeAux A B f (i + 1) j
           else if c < 0 then mergeAux A B f i (j + 1)
           else mergeAux A B f (i + 1) (j + 1))

/-- The candidate vertices of `hull A - hull B`, labelled. -/
def minkPairs (A B : List QPoint) : List (QPoint × QPoint) :=
  let A' := rotL A (lowIdx A)
  let B' := rotL (negL B) (lowIdx (negL B))
  mergeAux A' B' (A.length + B.length) 0 0

def minkPts (A B : List QPoint) : List QPoint :=
  (minkPairs A B).map fun ab => (ab.1.1 + ab.2.1, ab.1.2 + ab.2.2)

lemma mem_rotL {V : List QPoint} {k : ℕ} {x : QPoint} (h : x ∈ rotL V k) : x ∈ V := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_of_mem_drop h
  · exact List.mem_of_mem_take h

lemma mergeAux_mem (A B : List QPoint) (hA : 0 < A.length) (hB : 0 < B.length) :
    ∀ (f i j : ℕ), ∀ ab ∈ mergeAux A B f i j, ab.1 ∈ A ∧ ab.2 ∈ B
  | 0, _, _, ab, h => by simp [mergeAux] at h
  | f + 1, i, j, ab, h => by
    unfold mergeAux at h
    by_cases h0 : A.length ≤ i ∧ B.length ≤ j
    · simp [h0] at h
    simp only [h0, ↓reduceIte] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨vtx_mem A hA i, vtx_mem B hB j⟩
    try dsimp only at h
    split_ifs at h <;> exact mergeAux_mem A B hA hB _ _ _ ab h

lemma minkPairs_mem {A B : List QPoint} (hA : 0 < A.length) (hB : 0 < B.length) :
    ∀ ab ∈ minkPairs A B, ab.1 ∈ A ∧ (-ab.2.1, -ab.2.2) ∈ B := by
  intro ab h
  have hA' : 0 < (rotL A (lowIdx A)).length := by simp [rotL]; omega
  have hB' : 0 < (rotL (negL B) (lowIdx (negL B))).length := by simp [rotL, negL]; omega
  obtain ⟨h1, h2⟩ := mergeAux_mem _ _ hA' hB' _ _ _ ab h
  refine ⟨mem_rotL h1, ?_⟩
  obtain ⟨b, hb, e⟩ := List.mem_map.mp (mem_rotL h2)
  rw [← e]; simpa using hb

open scoped Pointwise in
/-- **A point of the hull of the labelled differences is a difference of hull points.** -/
theorem mink_hull {A B : List QPoint} (hA : 0 < A.length) (hB : 0 < B.length) {z : Point}
    (hz : z ∈ convexHull ℝ (vpts (minkPts A B))) :
    ∃ a ∈ convexHull ℝ (vpts A), ∃ b ∈ convexHull ℝ (vpts B), z = a - b := by
  have hconv : Convex ℝ {z : Point | ∃ a ∈ convexHull ℝ (vpts A), ∃ b ∈ convexHull ℝ (vpts B), z = a - b} := by
    have : {z : Point | ∃ a ∈ convexHull ℝ (vpts A), ∃ b ∈ convexHull ℝ (vpts B), z = a - b}
        = convexHull ℝ (vpts A) - convexHull ℝ (vpts B) := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_sub]; constructor
      · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
    rw [this]; exact (convex_convexHull ℝ _).sub (convex_convexHull ℝ _)
  have hsub : vpts (minkPts A B) ⊆ {z : Point | ∃ a ∈ convexHull ℝ (vpts A), ∃ b ∈ convexHull ℝ (vpts B), z = a - b} := by
    rintro y ⟨v, hv, rfl⟩
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hv
    obtain ⟨h1, h2⟩ := minkPairs_mem hA hB ab hab
    refine ⟨realPoint ab.1, subset_convexHull ℝ _ ⟨_, h1, rfl⟩,
      realPoint (-ab.2.1, -ab.2.2), subset_convexHull ℝ _ ⟨_, h2, rfl⟩, ?_⟩
    ext <;> simp [realPoint]
  exact convexHull_min hsub hconv hz

/-! ## Fast forms of the polygon checks -/

def edgesF (V : List QPoint) : Polygon := List.zipWith edgeH V (V.tail ++ V.take 1)

lemma vtx_eq_getElem (V : List QPoint) {k : ℕ} (hk : k < V.length) : vtx V k = V[k] := by
  unfold vtx; rw [Nat.mod_eq_of_lt hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl

lemma rot1_getElem (V : List QPoint) {k : ℕ} (hk : k < V.length) :
    (V.tail ++ V.take 1)[k]'(by simp; omega) = vtx V (k + 1) := by
  cases V with
  | nil => simp at hk
  | cons x V =>
    simp only [List.tail_cons, List.take_succ_cons, List.take_zero]
    by_cases h : k < V.length
    · rw [List.getElem_append_left h, vtx_eq_getElem _ (by simp; omega)]; simp
    · have hk' : k = V.length := by simp at hk; omega
      subst hk'
      rw [List.getElem_append_right (by omega)]
      simp [vtx]

lemma edgesF_eq (V : List QPoint) : edgesF V = edges V := by
  apply List.ext_getElem
  · cases V <;> simp [edgesF, edges]
  · intro k h1 h2
    have hk : k < V.length := by simpa [edges] using h2
    simp only [edgesF, List.getElem_zipWith, edges, List.getElem_map, List.getElem_range]
    rw [rot1_getElem V hk, vtx_eq_getElem V hk]

/-- Strict convexity, `O(n²)`: every vertex off an edge is strictly inside it. -/
def convexF (V : List QPoint) : Bool :=
  decide (3 ≤ V.length) &&
    ((edgesF V).zipIdx.all fun ek => V.zipIdx.all fun vm =>
      decide (vm.2 = ek.2) || decide (vm.2 = (ek.2 + 1) % V.length) ||
        decide (ek.1.a * vm.1.1 + ek.1.b * vm.1.2 < ek.1.c))

lemma convexF_imp {V : List QPoint} (h : convexF V = true) : convexB V = true := by
  simp only [convexF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨hn, hall⟩ := h
  simp only [convexB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true]
  refine ⟨hn, fun k hk m hm => ?_⟩
  have hkE : k < (edgesF V).length := by rw [edgesF_eq]; simpa [edges] using hk
  have hek : ((edgesF V)[k], k) ∈ (edgesF V).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]; simp [hkE]
  have hvm : (V[m], m) ∈ V.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]; simp [hm]
  rcases hall _ hek _ hvm with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · right
    have he : (edgesF V)[k] = edgeH (vtx V k) (vtx V (k + 1)) := by
      simp only [edgesF_eq, edges, List.getElem_map, List.getElem_range]
    have h' := h
    rw [he, ← vtx_eq_getElem V hm] at h'
    simp only [edgeH, crossQ] at h' ⊢
    linarith

/-- Labelled differences `A[a] - B[b]`. -/
def diffs (A B : List QPoint) (L : List (ℕ × ℕ)) : List QPoint :=
  L.map fun ab => ((A.getD ab.1 (0, 0)).1 - (B.getD ab.2 (0, 0)).1,
    (A.getD ab.1 (0, 0)).2 - (B.getD ab.2 (0, 0)).2)

open scoped Pointwise in
theorem diffs_hull {A B : List QPoint} {L : List (ℕ × ℕ)}
    (hL : ∀ ab ∈ L, ab.1 < A.length ∧ ab.2 < B.length) {z : Point}
    (hz : z ∈ convexHull ℝ (vpts (diffs A B L))) :
    ∃ a ∈ convexHull ℝ (vpts A), ∃ b ∈ convexHull ℝ (vpts B), z = a - b := by
  have hset : {z : Point | ∃ a ∈ convexHull ℝ (vpts A), ∃ b ∈ convexHull ℝ (vpts B), z = a - b}
      = convexHull ℝ (vpts A) - convexHull ℝ (vpts B) := by
    ext z; simp only [Set.mem_ofPred_eq, Set.mem_sub]; constructor
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  have hconv : Convex ℝ {z : Point | ∃ a ∈ convexHull ℝ (vpts A), ∃ b ∈ convexHull ℝ (vpts B), z = a - b} := by
    rw [hset]; exact (convex_convexHull ℝ _).sub (convex_convexHull ℝ _)
  have hsub : vpts (diffs A B L) ⊆ {z : Point | ∃ a ∈ convexHull ℝ (vpts A), ∃ b ∈ convexHull ℝ (vpts B), z = a - b} := by
    rintro y ⟨v, hv, rfl⟩
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hv
    obtain ⟨h1, h2⟩ := hL ab hab
    have m1 : A.getD ab.1 (0, 0) ∈ A := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; exact List.getElem_mem h1
    have m2 : B.getD ab.2 (0, 0) ∈ B := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; exact List.getElem_mem h2
    refine ⟨realPoint (A.getD ab.1 (0, 0)), subset_convexHull ℝ _ ⟨_, m1, rfl⟩,
      realPoint (B.getD ab.2 (0, 0)), subset_convexHull ℝ _ ⟨_, m2, rfl⟩, ?_⟩
    ext <;> simp [realPoint]
  exact convexHull_min hsub hconv hz

theorem edgesF_subset_hull {V : List QPoint} (hV : convexF V = true) :
    (edgesF V).carrier ⊆ convexHull ℝ (vpts V) := by
  rw [edgesF_eq]; exact edges_subset_hull (convexF_imp hV)

end
end ElevenSquare.Tasks.T07.Ext
