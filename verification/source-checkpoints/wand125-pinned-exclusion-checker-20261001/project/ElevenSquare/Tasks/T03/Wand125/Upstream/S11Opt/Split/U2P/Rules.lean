import ElevenSquare.Tasks.T03.Wand125.Upstream.S11Opt.Split.U2Rules

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# U2 (prior) — owned hulls: triangles of owned points, promotion of several targets at once

`U2Rules` forbids single owned points.  Here the owned set of a square is used through its convex
hull (the open square is convex):

* `owned_of_tri` — a grid point certified in the hull of three owned points (`triGroupOk`) is owned.
* A *triangle option* `[g]` forbids every pose capturing some point of the group `g`, when `g` lies
  in the hull of three points owned by another square.
* `owned_all_of_tris` (**promotion**): a cover whose leaves are walls, cells, triangle options, or the
  target option `targets.map (fun p => [p])` (all targets at once) proves every target owned.
* `excluded_of_tris` (**terminal**): a cover by triangle options alone excludes the case.

A triangle is `(o', a, b, c, g, ls)`: owner `o'`, vertices `a b c`, lattice points `g` with their
barycentric weights `ls` over the common denominator `bm`.
-/

namespace SquarePacking.S11Opt.Split.U2P

open FieldTree

/-- The common barycentric denominator of the triangle lattices. -/
def bm : ℕ := 65536

/-- A triangle of owned points with certified points in its hull. -/
abbrev Tri := ℕ × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × List (ℕ × ℕ) × List (List ℕ)

/-- The triangle is certified: its lattice points are the stated convex combinations. -/
def Tri.ok (t : Tri) : Bool := triGroupOk bm t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2

/-- Its vertices are owned by its owner, another square of `J` than `o`. -/
def Tri.Valid (S : ℝ) (J : List ℕ) (o : ℕ) (t : Tri) : Prop :=
  t.1 ∈ J ∧ t.1 ≠ o ∧ Owned S J t.1 t.2.1 ∧ Owned S J t.1 t.2.2.1 ∧ Owned S J t.1 t.2.2.2.1 ∧
    t.ok = true

/-- The options of a step: one per triangle, then (if any) all targets at once. -/
def triOpts (tris : List Tri) : List (List (List (ℕ × ℕ))) := tris.map fun t => [t.2.2.2.2.1]

def stepOpts (tris : List Tri) (targets : List (ℕ × ℕ)) : List (List (List (ℕ × ℕ))) :=
  triOpts tris ++ [targets.map fun p => [p]]

/-- A point certified in the hull of three owned points is owned. -/
theorem owned_of_tri {S : ℝ} {J : List ℕ} {o : ℕ} {a b c w : ℕ × ℕ} (ha : Owned S J o a)
    (hb : Owned S J o b) (hc : Owned S J o c)
    (hw : ptQ G.Q w ∈ convexHull ℝ ({ptQ G.Q a, ptQ G.Q b, ptQ G.Q c} : Set (ℝ × ℝ))) :
    Owned S J o w := by
  intro r
  refine (convex_ScSq _ _ _).convexHull_subset_iff.mpr ?_ hw
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · exact ha r
  · exact hb r
  · exact hc r

/-- A pose of `o` capturing a point of a valid triangle's group does not occur. -/
lemma tri_forbidden {S : ℝ} {J : List ℕ} {o : ℕ} (ho : o ∈ J) {t : Tri}
    (ht : t.Valid S J o) (r : Real S J) {w : ℕ × ℕ} (hw : w ∈ t.2.2.2.2.1)
    (hm : ptQ G.Q w ∈ ScSq G.sc (r.ctr (r.σ o)) (r.ang (r.σ o))) : False := by
  obtain ⟨hJ, hne, ha, hb, hc, hok⟩ := ht
  have hwh := triGroupOk_mem (Q := G.Q) (by norm_num [bm] : 0 < bm) _ _ hok w hw
  have hown := owned_of_tri ha hb hc hwh r
  have hne' : r.σ t.1 ≠ r.σ o := fun h => hne (r.inj _ hJ _ ho h)
  exact Set.disjoint_left.mp (disjoint_ScSq (r.pack.2 _ _ hne')) hown hm

/-- **Promotion of several targets.** -/
theorem owned_all_of_tris {S : ℝ} (hS : S ≤ Ux) (hS0 : 0 ≤ S) {J : List ℕ} {o : ℕ} (ho : o ∈ J)
    (ho16 : o < 16) {tris : List Tri} (htris : ∀ t ∈ tris, t.Valid S J o)
    {targets : List (ℕ × ℕ)}
    (hcov : CovF G.Q G.M G.R (hpsC o) (stepOpts tris targets) 0 G.M 0 G.M 0 G.R) :
    ∀ p ∈ targets, Owned S J o p := by
  intro p hp r
  have hin : sq (r.ctr (r.σ o)) (r.ang (r.σ o)) 1 ⊆ box Ux :=
    (r.pack.1 _).trans (cbox_subset hS hS0)
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos hcov G.sc_pos G.sc_lt G.UM hin
    (cellHP_all ho16 (r.cell o ho))
  simp only [stepOpts, triOpts, List.mem_append, List.mem_map, List.mem_singleton] at hop
  rcases hop with ⟨t, ht, rfl⟩ | rfl
  · obtain ⟨w, hw, hm⟩ := hg _ (List.mem_singleton_self _)
    exact (tri_forbidden ho (htris t ht) r hw hm).elim
  · obtain ⟨q, hq, hm⟩ := hg [p] (List.mem_map.mpr ⟨p, hp, rfl⟩)
    rw [List.mem_singleton] at hq
    subst hq
    exact hm

/-- **Terminal.**  A cover by triangle options alone excludes the case. -/
theorem excluded_of_tris {S : ℝ} (hS : S ≤ Ux) (hS0 : 0 ≤ S) {J : List ℕ} {o : ℕ} (ho : o ∈ J)
    (ho16 : o < 16) {tris : List Tri} (htris : ∀ t ∈ tris, t.Valid S J o)
    (hcov : CovF G.Q G.M G.R (hpsC o) (triOpts tris) 0 G.M 0 G.M 0 G.R) :
    ¬ RealizesIn S J := by
  rw [realizesIn_iff]
  rintro ⟨r⟩
  have hin : sq (r.ctr (r.σ o)) (r.ang (r.σ o)) 1 ⊆ box Ux :=
    (r.pack.1 _).trans (cbox_subset hS hS0)
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos hcov G.sc_pos G.sc_lt G.UM hin
    (cellHP_all ho16 (r.cell o ho))
  simp only [triOpts, List.mem_map] at hop
  obtain ⟨t, ht, rfl⟩ := hop
  obtain ⟨w, hw, hm⟩ := hg _ (List.mem_singleton_self _)
  exact tri_forbidden ho (htris t ht) r hw hm

end SquarePacking.S11Opt.Split.U2P
