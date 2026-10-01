import ElevenSquare.Tasks.T03.Wand125.Upstream.S11Opt.Split.U2P.Rules

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# U2 (prior) — branches: the induction under centre half-planes

A *condition* `(o, h)` asks the (scaled) centre of the square of cell `o` to lie in the grid
half-plane `h` (as the cell half-planes `hpsC o`).  Under a list of conditions `cs`:

* `OwnedC S J cs o p` — `p` is in the open square of `o` in every realization satisfying `cs`;
* `owned_all_of_trisC`, `excluded_of_trisC` — promotion and terminal step, the tree of owner `o`
  running over the region `hpsC o ++ condsOf cs o`;
* `split_excl` — a half-plane and its complement cover the plane, so two excluded branches
  exclude their parent;
* `OwnedC.of_owned`, `OwnedC.mono` — unconditional ownership, and ownership under fewer
  conditions, hold under more conditions.
-/

namespace SquarePacking.S11Opt.Split.U2P

open FieldTree

/-- A condition: owner, grid half-plane of its scaled centre. -/
abbrev Cond := ℕ × (ℤ × ℤ × ℤ)

/-- The realization satisfies the conditions. -/
def Holds {S : ℝ} {J : List ℕ} (r : Real S J) (cs : List Cond) : Prop :=
  ∀ c ∈ cs, InHP G.Q c.2 ((r.ctr (r.σ c.1)).1 / G.sc, (r.ctr (r.σ c.1)).2 / G.sc)

/-- Ownership under conditions. -/
def OwnedC (S : ℝ) (J : List ℕ) (cs : List Cond) (o : ℕ) (p : ℕ × ℕ) : Prop :=
  ∀ r : Real S J, Holds r cs → ptQ G.Q p ∈ ScSq G.sc (r.ctr (r.σ o)) (r.ang (r.σ o))

/-- The branch is empty. -/
def Excl (S : ℝ) (J : List ℕ) (cs : List Cond) : Prop := ∀ r : Real S J, Holds r cs → False

lemma OwnedC.of_owned {S : ℝ} {J : List ℕ} {cs : List Cond} {o : ℕ} {p : ℕ × ℕ}
    (h : Owned S J o p) : OwnedC S J cs o p := fun r _ => h r

lemma OwnedC.mono {S : ℝ} {J : List ℕ} {cs cs' : List Cond} {o : ℕ} {p : ℕ × ℕ}
    (h : OwnedC S J cs o p) (hsub : ∀ c ∈ cs, c ∈ cs') : OwnedC S J cs' o p :=
  fun r hr => h r fun c hc => hr c (hsub c hc)

/-- The half-planes of the conditions on owner `o`. -/
def condsOf (cs : List Cond) (o : ℕ) : List (ℤ × ℤ × ℤ) := (cs.filter fun c => c.1 == o).map (·.2)

/-- A valid triangle under conditions. -/
def Tri.ValidC (S : ℝ) (J : List ℕ) (cs : List Cond) (o : ℕ) (t : Tri) : Prop :=
  t.1 ∈ J ∧ t.1 ≠ o ∧ OwnedC S J cs t.1 t.2.1 ∧ OwnedC S J cs t.1 t.2.2.1 ∧
    OwnedC S J cs t.1 t.2.2.2.1 ∧ t.ok = true

lemma owned_of_triC {S : ℝ} {J : List ℕ} {cs : List Cond} {o : ℕ} {a b c w : ℕ × ℕ}
    (ha : OwnedC S J cs o a) (hb : OwnedC S J cs o b) (hc : OwnedC S J cs o c)
    (hw : ptQ G.Q w ∈ convexHull ℝ ({ptQ G.Q a, ptQ G.Q b, ptQ G.Q c} : Set (ℝ × ℝ))) :
    OwnedC S J cs o w := by
  intro r hr
  refine (convex_ScSq _ _ _).convexHull_subset_iff.mpr ?_ hw
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · exact ha r hr
  · exact hb r hr
  · exact hc r hr

lemma tri_forbiddenC {S : ℝ} {J : List ℕ} {cs : List Cond} {o : ℕ} (ho : o ∈ J) {t : Tri}
    (ht : t.ValidC S J cs o) (r : Real S J) (hr : Holds r cs) {w : ℕ × ℕ}
    (hw : w ∈ t.2.2.2.2.1) (hm : ptQ G.Q w ∈ ScSq G.sc (r.ctr (r.σ o)) (r.ang (r.σ o))) :
    False := by
  obtain ⟨hJ, hne, ha, hb, hc, hok⟩ := ht
  have hwh := triGroupOk_mem (Q := G.Q) (by norm_num [bm] : 0 < bm) _ _ hok w hw
  have hown := owned_of_triC ha hb hc hwh r hr
  have hne' : r.σ t.1 ≠ r.σ o := fun h => hne (r.inj _ hJ _ ho h)
  exact Set.disjoint_left.mp (disjoint_ScSq (r.pack.2 _ _ hne')) hown hm

/-- The scaled centre of `o` satisfies its cell and its conditions. -/
lemma region_of {S : ℝ} {J : List ℕ} {cs : List Cond} {o : ℕ} (ho : o ∈ J) (ho16 : o < 16)
    (r : Real S J) (hr : Holds r cs) :
    ∀ h ∈ hpsC o ++ condsOf cs o,
      InHP G.Q h ((r.ctr (r.σ o)).1 / G.sc, (r.ctr (r.σ o)).2 / G.sc) := by
  intro h hh
  rcases List.mem_append.mp hh with hh | hh
  · exact cellHP_all ho16 (r.cell o ho) h hh
  · simp only [condsOf, List.mem_map, List.mem_filter, beq_iff_eq] at hh
    obtain ⟨c, ⟨hc, rfl⟩, rfl⟩ := hh
    exact hr c hc

/-- **Promotion under conditions.** -/
theorem owned_all_of_trisC {S : ℝ} (hS : S ≤ Ux) (hS0 : 0 ≤ S) {J : List ℕ} {cs : List Cond}
    {o : ℕ} (ho : o ∈ J) (ho16 : o < 16) {tris : List Tri} (htris : ∀ t ∈ tris, t.ValidC S J cs o)
    {targets : List (ℕ × ℕ)}
    (hcov : CovF G.Q G.M G.R (hpsC o ++ condsOf cs o) (stepOpts tris targets) 0 G.M 0 G.M 0 G.R) :
    ∀ p ∈ targets, OwnedC S J cs o p := by
  intro p hp r hr
  have hin : sq (r.ctr (r.σ o)) (r.ang (r.σ o)) 1 ⊆ box Ux :=
    (r.pack.1 _).trans (cbox_subset hS hS0)
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos hcov G.sc_pos G.sc_lt G.UM hin
    (region_of ho ho16 r hr)
  simp only [stepOpts, triOpts, List.mem_append, List.mem_map, List.mem_singleton] at hop
  rcases hop with ⟨t, ht, rfl⟩ | rfl
  · obtain ⟨w, hw, hm⟩ := hg _ (List.mem_singleton_self _)
    exact (tri_forbiddenC ho (htris t ht) r hr hw hm).elim
  · obtain ⟨q, hq, hm⟩ := hg [p] (List.mem_map.mpr ⟨p, hp, rfl⟩)
    rw [List.mem_singleton] at hq
    subst hq
    exact hm

/-- **Terminal under conditions.** -/
theorem excluded_of_trisC {S : ℝ} (hS : S ≤ Ux) (hS0 : 0 ≤ S) {J : List ℕ} {cs : List Cond}
    {o : ℕ} (ho : o ∈ J) (ho16 : o < 16) {tris : List Tri} (htris : ∀ t ∈ tris, t.ValidC S J cs o)
    (hcov : CovF G.Q G.M G.R (hpsC o ++ condsOf cs o) (triOpts tris) 0 G.M 0 G.M 0 G.R) :
    Excl S J cs := by
  intro r hr
  have hin : sq (r.ctr (r.σ o)) (r.ang (r.σ o)) 1 ⊆ box Ux :=
    (r.pack.1 _).trans (cbox_subset hS hS0)
  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos hcov G.sc_pos G.sc_lt G.UM hin
    (region_of ho ho16 r hr)
  simp only [triOpts, List.mem_map] at hop
  obtain ⟨t, ht, rfl⟩ := hop
  obtain ⟨w, hw, hm⟩ := hg _ (List.mem_singleton_self _)
  exact tri_forbiddenC ho (htris t ht) r hr hw hm

/-- **Split.**  A half-plane and its complement: two excluded branches exclude the parent. -/
theorem split_excl {S : ℝ} {J : List ℕ} {cs : List Cond} (o : ℕ) (A B C : ℤ)
    (h1 : Excl S J ((o, (A, B, C)) :: cs)) (h2 : Excl S J ((o, (-A, -B, -C)) :: cs)) :
    Excl S J cs := by
  intro r hr
  set c := ((r.ctr (r.σ o)).1 / G.sc, (r.ctr (r.σ o)).2 / G.sc)
  rcases le_total ((A : ℝ) * (G.Q * c.1) + (B : ℝ) * (G.Q * c.2)) C with h | h
  · refine h1 r fun d hd => ?_
    rcases List.mem_cons.mp hd with rfl | hd
    · exact h
    · exact hr d hd
  · refine h2 r fun d hd => ?_
    rcases List.mem_cons.mp hd with rfl | hd
    · show ((-A : ℤ) : ℝ) * (G.Q * c.1) + ((-B : ℤ) : ℝ) * (G.Q * c.2) ≤ ((-C : ℤ) : ℝ)
      push_cast; linarith
    · exact hr d hd

/-- The root: an excluded empty condition list excludes the case. -/
theorem not_in_of_excl {S : ℝ} {J : List ℕ} (h : Excl S J []) : ¬ RealizesIn S J := by
  rw [realizesIn_iff]
  rintro ⟨r⟩
  exact h r fun c hc => by simp at hc

end SquarePacking.S11Opt.Split.U2P
