import Sqpack.S11Opt.FieldTree
import Sqpack.S11Opt.Majority

/-!
# From box-tree covers to statements about packings

* `exists_u` — every angle gives the same closed and open unit squares as some `2 arctan u`,
  `u ∈ [0, 1]` (a quarter turn).
* `bridge` — a `CovF` claim over the whole scaled container, in the world scaled by `1/s`,
  yields for every admissible square with centre in the region an option whose groups each
  have a point `p` with `s • p/Q` in the *open* square.
* `ScSq` — the open square scaled by `1/s`; open, convex, and disjoint for a packing.
* `triGroupOk`/`segGroupOk` — barycentric checks that every candidate of a group lies in the
  convex hull of a triangle / segment.
* `TrueIdx`, `majority_capacity_idx` — the capacity-one lemma with index sets.
-/

open Finset

namespace SquarePacking.S11Opt

open FieldTree

/-! ## Angles -/

lemma sq_eq_of_add_int (c : ℝ × ℝ) (θ : ℝ) (L : ℝ) :
    ∀ n : ℕ, sq c (θ + n * (Real.pi / 2)) L = sq c θ L
  | 0 => by simp
  | n + 1 => by
    have := sq_add_pi_div_two c (θ + n * (Real.pi / 2)) L
    rw [show θ + ((n + 1 : ℕ) : ℝ) * (Real.pi / 2) = θ + n * (Real.pi / 2) + Real.pi / 2 by
      push_cast; ring, this, sq_eq_of_add_int c θ L n]

lemma sq_eq_of_int (c : ℝ × ℝ) (θ : ℝ) (L : ℝ) (z : ℤ) :
    sq c (θ + z * (Real.pi / 2)) L = sq c θ L := by
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · exact_mod_cast sq_eq_of_add_int c θ L n
  · have := sq_eq_of_add_int c (θ - n * (Real.pi / 2)) L n
    rw [sub_add_cancel] at this
    push_cast
    rw [show θ + -(n : ℝ) * (Real.pi / 2) = θ - n * (Real.pi / 2) by ring, this]

/-- Every angle is a quarter-turn translate of some `2 arctan u`, `u ∈ [0, 1]`. -/
lemma exists_u (θ : ℝ) : ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ ∃ z : ℤ, θ = 2 * Real.arctan u + z * (Real.pi / 2) := by
  have hp : (0 : ℝ) < Real.pi / 2 := by positivity
  have f1 := Int.floor_le (θ / (Real.pi / 2))
  have f2 := Int.lt_floor_add_one (θ / (Real.pi / 2))
  rw [le_div_iff₀ hp] at f1
  rw [div_lt_iff₀ hp] at f2
  set z : ℤ := ⌊θ / (Real.pi / 2)⌋
  set θ0 := θ - z * (Real.pi / 2) with hθ0
  have h0 : 0 ≤ θ0 := by rw [hθ0]; linarith
  have h1 : θ0 < Real.pi / 2 := by rw [hθ0]; nlinarith
  refine ⟨Real.tan (θ0 / 2), ?_, ?_, z, ?_⟩
  · exact Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith [Real.pi_pos])
  · rw [← Real.tan_pi_div_four]
    exact (Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
      (by linarith)).le
  · rw [Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith)]
    simp only [θ0]; ring

/-! ## The scaled open square -/

/-- Points `q` with `s • q` in the open unit square. -/
def ScSq (s : ℝ) (c : ℝ × ℝ) (θ : ℝ) : Set (ℝ × ℝ) := {q | s • q ∈ sqInt c θ 1}

lemma convex_ScSq (s : ℝ) (c : ℝ × ℝ) (θ : ℝ) : Convex ℝ (ScSq s c θ) := by
  intro p hp q hq a b ha hb hab
  show s • (a • p + b • q) ∈ sqInt c θ 1
  rw [smul_add, smul_comm s a p, smul_comm s b q]
  exact convex_sqInt c θ hp hq ha hb hab

lemma isOpen_ScSq (s : ℝ) (c : ℝ × ℝ) (θ : ℝ) : IsOpen (ScSq s c θ) := by
  have e : ScSq s c θ = (fun q : ℝ × ℝ => s • q) ⁻¹' sqInt c θ 1 := rfl
  have hc : Continuous (fun q : ℝ × ℝ => s • q) := continuous_const_smul s
  rw [e]
  exact (isOpen_sqInt c θ).preimage hc

lemma disjoint_ScSq {s : ℝ} {c c' : ℝ × ℝ} {θ θ' : ℝ} (h : Disjoint (sqInt c θ 1) (sqInt c' θ' 1)) :
    Disjoint (ScSq s c θ) (ScSq s c' θ') :=
  Set.disjoint_left.mpr fun _ h1 h2 => Set.disjoint_left.mp h h1 h2

/-- The closed unit square about `c/s` lies in `ScSq s c θ` when `0 < s < 1`. -/
lemma mem_ScSq_of_mem_sq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {c : ℝ × ℝ} {θ : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ sq (c.1 / s, c.2 / s) θ 1) : q ∈ ScSq s c θ := by
  obtain ⟨h1, h2⟩ := hq
  have e1 : (coord c θ (s • q)).1 = s * (coord (c.1 / s, c.2 / s) θ q).1 := by
    simp only [coord, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; field_simp
  have e2 : (coord c θ (s • q)).2 = s * (coord (c.1 / s, c.2 / s) θ q).2 := by
    simp only [coord, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; field_simp
  show |(coord c θ (s • q)).1| < 1 / 2 ∧ |(coord c θ (s • q)).2| < 1 / 2
  rw [e1, e2, abs_mul, abs_mul, abs_of_pos hs0]
  constructor <;> nlinarith

/-! ## The bridge -/

/-- **Bridge.**  A cover of the whole scaled container gives, for every admissible unit square
in `[0, U]²` whose scaled centre lies in the region, an option all of whose groups have a point
in the scaled open square. -/
theorem bridge {Q M R : ℕ} (hQ : 0 < Q) (hR : 0 < R) {hps : List (ℤ × ℤ × ℤ)}
    {opts : List (List (List (ℕ × ℕ)))} (hcov : CovF Q M R hps opts 0 M 0 M 0 R)
    {s U : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hUM : U / s ≤ (M : ℝ) / Q)
    {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box U)
    (hcell : ∀ h ∈ hps, InHP Q h (c.1 / s, c.2 / s)) :
    ∃ o ∈ opts, ∀ g ∈ o, ∃ p ∈ g, ((p.1 : ℝ) / Q, (p.2 : ℝ) / Q) ∈ ScSq s c θ := by
  obtain ⟨u, hu0, hu1, z, hz⟩ := exists_u θ
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  set c' : ℝ × ℝ := (c.1 / s, c.2 / s)
  have hsq : sq c' θ 1 = sq c' (2 * Real.arctan u) 1 := by rw [hz, sq_eq_of_int]
  obtain ⟨a1, a2, a3, a4⟩ := (sq_subset_box_iff U c θ).mp hin
  have hw := one_le_wid θ
  have hwz : wid θ = wid (2 * Real.arctan u) := by
    rw [hz]; clear hz
    rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
    · induction n with
      | zero => simp
      | succ n ih =>
        push_cast at ih ⊢
        rw [show 2 * Real.arctan u + (n + 1) * (Real.pi / 2)
            = 2 * Real.arctan u + n * (Real.pi / 2) + Real.pi / 2 by ring, wid_add_pi_div_two, ih]
    · induction n with
      | zero => simp
      | succ n ih =>
        push_cast at ih ⊢
        rw [← wid_add_pi_div_two, show 2 * Real.arctan u + -(n + 1 : ℝ) * (Real.pi / 2) + Real.pi / 2
            = 2 * Real.arctan u + -(n : ℝ) * (Real.pi / 2) by ring, ih]
  -- admissibility in the scaled container
  have hc'1 : wid θ / 2 ≤ c'.1 := by
    show wid θ / 2 ≤ c.1 / s
    rw [le_div_iff₀ hs0]; nlinarith
  have hc'2 : c'.1 ≤ (M : ℝ) / Q - wid θ / 2 := by
    show c.1 / s ≤ _
    have : c.1 / s ≤ U / s - wid θ / 2 := by
      rw [div_le_iff₀ hs0, sub_mul, div_mul_cancel₀ _ hs0.ne']; nlinarith
    linarith
  have hc'3 : wid θ / 2 ≤ c'.2 := by
    show wid θ / 2 ≤ c.2 / s
    rw [le_div_iff₀ hs0]; nlinarith
  have hc'4 : c'.2 ≤ (M : ℝ) / Q - wid θ / 2 := by
    show c.2 / s ≤ _
    have : c.2 / s ≤ U / s - wid θ / 2 := by
      rw [div_le_iff₀ hs0, sub_mul, div_mul_cancel₀ _ hs0.ne']; nlinarith
    linarith
  have hadm : sq c' (2 * Real.arctan u) 1 ⊆ box ((M : ℝ) / Q) :=
    (sq_subset_box_iff _ _ _).mpr ⟨by rw [← hwz]; exact hc'1, by rw [← hwz]; exact hc'2,
      by rw [← hwz]; exact hc'3, by rw [← hwz]; exact hc'4⟩
  have hx0 : ((0 : ℕ) : ℝ) / Q ≤ c'.1 := by simp; linarith
  have hx1 : c'.1 ≤ (M : ℝ) / Q := by linarith
  have hy0 : ((0 : ℕ) : ℝ) / Q ≤ c'.2 := by simp; linarith
  have hy1 : c'.2 ≤ (M : ℝ) / Q := by linarith
  have hu0' : ((0 : ℕ) : ℝ) / R ≤ u := by simp; exact hu0
  have hu1' : u ≤ (R : ℝ) / R := by rw [div_self hRr.ne']; exact hu1
  obtain ⟨o, ho, hg⟩ := hcov c' u hx0 hx1 hy0 hy1 hu0' hu1' hadm hcell
  refine ⟨o, ho, fun g hgm => ?_⟩
  obtain ⟨p, hp, hpsq⟩ := hg g hgm
  rw [← hsq] at hpsq
  exact ⟨p, hp, mem_ScSq_of_mem_sq hs0 hs1 hpsq⟩

/-! ## Barycentric checks -/

/-- `m • w = l₀ a + l₁ b + l₂ c` with `l₀ + l₁ + l₂ = m`. -/
def triOkB (m : ℕ) (a b c w : ℕ × ℕ) : List ℕ → Bool
  | [l0, l1, l2] => l0 + l1 + l2 == m && m * w.1 == l0 * a.1 + l1 * b.1 + l2 * c.1 &&
      m * w.2 == l0 * a.2 + l1 * b.2 + l2 * c.2
  | _ => false

/-- `m • w = l₀ a + l₁ b` with `l₀ + l₁ = m`. -/
def segOkB (m : ℕ) (a b w : ℕ × ℕ) : List ℕ → Bool
  | [l0, l1] => l0 + l1 == m && m * w.1 == l0 * a.1 + l1 * b.1 && m * w.2 == l0 * a.2 + l1 * b.2
  | _ => false

def triGroupOk (m : ℕ) (a b c : ℕ × ℕ) : List (ℕ × ℕ) → List (List ℕ) → Bool
  | [], [] => true
  | w :: g, l :: ls => triOkB m a b c w l && triGroupOk m a b c g ls
  | _, _ => false

def segGroupOk (m : ℕ) (a b : ℕ × ℕ) : List (ℕ × ℕ) → List (List ℕ) → Bool
  | [], [] => true
  | w :: g, l :: ls => segOkB m a b w l && segGroupOk m a b g ls
  | _, _ => false

/-- The grid point `(X/Q, Y/Q)`. -/
noncomputable def ptQ (Q : ℕ) (p : ℕ × ℕ) : ℝ × ℝ := ((p.1 : ℝ) / Q, (p.2 : ℝ) / Q)

lemma triOkB_mem {Q m : ℕ} (hm : 0 < m) {a b c w : ℕ × ℕ} {l : List ℕ} (h : triOkB m a b c w l = true) :
    ptQ Q w ∈ convexHull ℝ ({ptQ Q a, ptQ Q b, ptQ Q c} : Set (ℝ × ℝ)) := by
  match l, h with
  | [l0, l1, l2], h =>
    simp only [triOkB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hs, h1⟩, h2⟩ := h
    have hmr : (0 : ℝ) < m := by exact_mod_cast hm
    have hs' : (l0 : ℝ) + l1 + l2 = m := by exact_mod_cast hs
    have h1' : (m : ℝ) * w.1 = l0 * a.1 + l1 * b.1 + l2 * c.1 := by exact_mod_cast h1
    have h2' : (m : ℝ) * w.2 = l0 * a.2 + l1 * b.2 + l2 * c.2 := by exact_mod_cast h2
    have hcv := convex_convexHull ℝ ({ptQ Q a, ptQ Q b, ptQ Q c} : Set (ℝ × ℝ))
    have ha := subset_convexHull ℝ ({ptQ Q a, ptQ Q b, ptQ Q c} : Set (ℝ × ℝ))
      (show ptQ Q a ∈ ({ptQ Q a, ptQ Q b, ptQ Q c} : Set (ℝ × ℝ)) by simp)
    have hb := subset_convexHull ℝ ({ptQ Q a, ptQ Q b, ptQ Q c} : Set (ℝ × ℝ))
      (show ptQ Q b ∈ ({ptQ Q a, ptQ Q b, ptQ Q c} : Set (ℝ × ℝ)) by simp)
    have hc := subset_convexHull ℝ ({ptQ Q a, ptQ Q b, ptQ Q c} : Set (ℝ × ℝ))
      (show ptQ Q c ∈ ({ptQ Q a, ptQ Q b, ptQ Q c} : Set (ℝ × ℝ)) by simp)
    have key : ptQ Q w = ((l0 : ℝ) / m) • ptQ Q a + ((l1 : ℝ) / m) • ptQ Q b + ((l2 : ℝ) / m) • ptQ Q c := by
      have k1 : (w.1 : ℝ) = (l0 : ℝ) / m * a.1 + (l1 : ℝ) / m * b.1 + (l2 : ℝ) / m * c.1 := by
        field_simp; linarith
      have k2 : (w.2 : ℝ) = (l0 : ℝ) / m * a.2 + (l1 : ℝ) / m * b.2 + (l2 : ℝ) / m * c.2 := by
        field_simp; linarith
      simp only [ptQ, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      rw [k1, k2]
      ext <;> simp only <;> ring
    rw [key]
    have h0 : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        (0 : ℝ) ≤ (![(l0 : ℝ) / m, (l1 : ℝ) / m, (l2 : ℝ) / m] : Fin 3 → ℝ) i := by
      intro i _; fin_cases i <;> simp <;> positivity
    have h1 : ∑ i ∈ (Finset.univ : Finset (Fin 3)),
        (![(l0 : ℝ) / m, (l1 : ℝ) / m, (l2 : ℝ) / m] : Fin 3 → ℝ) i = 1 := by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      field_simp; linarith
    have hz : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        (![ptQ Q a, ptQ Q b, ptQ Q c] : Fin 3 → ℝ × ℝ) i
          ∈ convexHull ℝ ({ptQ Q a, ptQ Q b, ptQ Q c} : Set (ℝ × ℝ)) := by
      intro i _; fin_cases i
      · exact ha
      · exact hb
      · exact hc
    have hmem := hcv.sum_mem h0 h1 hz
    simpa only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using hmem

lemma segOkB_mem {Q m : ℕ} (hm : 0 < m) {a b w : ℕ × ℕ} {l : List ℕ} (h : segOkB m a b w l = true) :
    ptQ Q w ∈ convexHull ℝ ({ptQ Q a, ptQ Q b} : Set (ℝ × ℝ)) := by
  match l, h with
  | [l0, l1], h =>
    simp only [segOkB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hs, h1⟩, h2⟩ := h
    have hmr : (0 : ℝ) < m := by exact_mod_cast hm
    have hs' : (l0 : ℝ) + l1 = m := by exact_mod_cast hs
    have h1' : (m : ℝ) * w.1 = l0 * a.1 + l1 * b.1 := by exact_mod_cast h1
    have h2' : (m : ℝ) * w.2 = l0 * a.2 + l1 * b.2 := by exact_mod_cast h2
    rw [convexHull_pair]
    refine ⟨(l0 : ℝ) / m, (l1 : ℝ) / m, by positivity, by positivity, by field_simp; linarith, ?_⟩
    have k1 : (w.1 : ℝ) = (l0 : ℝ) / m * a.1 + (l1 : ℝ) / m * b.1 := by field_simp; linarith
    have k2 : (w.2 : ℝ) = (l0 : ℝ) / m * a.2 + (l1 : ℝ) / m * b.2 := by field_simp; linarith
    simp only [ptQ, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    rw [k1, k2]
    ext <;> simp only <;> ring

lemma triGroupOk_mem {Q m : ℕ} (hm : 0 < m) {a b c : ℕ × ℕ} :
    ∀ (g : List (ℕ × ℕ)) (ls : List (List ℕ)), triGroupOk m a b c g ls = true →
      ∀ w ∈ g, ptQ Q w ∈ convexHull ℝ ({ptQ Q a, ptQ Q b, ptQ Q c} : Set (ℝ × ℝ))
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [triGroupOk] at h
  | w :: g, l :: ls, h => by
    simp only [triGroupOk, Bool.and_eq_true] at h
    intro w' hw'
    rcases List.mem_cons.mp hw' with rfl | hw'
    · exact triOkB_mem hm h.1
    · exact triGroupOk_mem hm g ls h.2 w' hw'

lemma segGroupOk_mem {Q m : ℕ} (hm : 0 < m) {a b : ℕ × ℕ} :
    ∀ (g : List (ℕ × ℕ)) (ls : List (List ℕ)), segGroupOk m a b g ls = true →
      ∀ w ∈ g, ptQ Q w ∈ convexHull ℝ ({ptQ Q a, ptQ Q b} : Set (ℝ × ℝ))
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [segGroupOk] at h
  | w :: g, l :: ls, h => by
    simp only [segGroupOk, Bool.and_eq_true] at h
    intro w' hw'
    rcases List.mem_cons.mp hw' with rfl | hw'
    · exact segOkB_mem hm h.1
    · exact segGroupOk_mem hm g ls h.2 w' hw'

/-! ## Capacity one, with index sets -/

/-- `A` meets the hull of the points of every `k`-element index set. -/
def TrueIdx {n : ℕ} (k : ℕ) (pt : Fin n → ℝ × ℝ) (A : Set (ℝ × ℝ)) : Prop :=
  ∀ I : Finset (Fin n), I.card = k → (A ∩ convexHull ℝ (pt '' (I : Set (Fin n)))).Nonempty

theorem majority_capacity_idx {n k : ℕ} (hn : n + 1 = 2 * k) {pt : Fin n → ℝ × ℝ}
    {A B : Set (ℝ × ℝ)} (hAc : Convex ℝ A) (hAo : IsOpen A) (hBc : Convex ℝ B) (hBo : IsOpen B)
    (hAB : Disjoint A B) (hA : TrueIdx k pt A) (hB : TrueIdx k pt B) : False := by
  obtain ⟨f, u, hfA, hfB⟩ := geometric_hahn_banach_open_open hAc hAo hBc hBo hAB
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => u ≤ f (pt i))
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  by_cases hge : k ≤ (Finset.univ.filter fun i => u ≤ f (pt i)).card
  · obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hge
    obtain ⟨x, hxA, hxS⟩ := hA S hScard
    have hhull : convexHull ℝ (pt '' (S : Set (Fin n))) ⊆ {x | u ≤ f x} := by
      refine convexHull_min ?_ (convex_halfSpace_ge f.isLinear u)
      rintro _ ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp (hSsub hi)).2
    exact absurd (hhull hxS) (not_le.mpr (hfA x hxA))
  · have hlt : k ≤ (Finset.univ.filter fun i => ¬ u ≤ f (pt i)).card := by omega
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hlt
    obtain ⟨x, hxB, hxS⟩ := hB S hScard
    have hhull : convexHull ℝ (pt '' (S : Set (Fin n))) ⊆ {x | f x < u} := by
      refine convexHull_min ?_ (convex_halfSpace_lt f.isLinear u)
      rintro _ ⟨i, hi, rfl⟩
      exact not_le.mp (Finset.mem_filter.mp (hSsub hi)).2
    exact absurd (hhull hxS) (not_lt.mpr (hfB x hxB).le)

end SquarePacking.S11Opt
