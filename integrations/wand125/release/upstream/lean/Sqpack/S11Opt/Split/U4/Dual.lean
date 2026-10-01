import Sqpack.S11Opt.Split.U4.Taylor

/-!
# U4 — the dual certificates and their checker

A *row* is a sparse integer vector `A` and a natural number `kt`; it holds at a perturbation
`hv : ℕ → ℝ` with scale `τ` when `0 ≤ (∑ A_k hv_k) / DA + τ kt / DK` (`RowOK`).  A certificate
for the signed coordinate `σ e_j` over a list of rows is a list of non-negative integer
multipliers `λ`; `certOK` computes the residual `r = λᵀA - σ DA DL e_j` exactly and checks

  `∑ |r_k| rI_k DK + (λ · kt) DA DR < rI_j DA DL DK`,

where `rI_k / DR` are the radii.  `certOK_sound`: if every row holds, `|hv_k| ≤ τ rI_k / DR`,
and the coordinate `j` is saturated with the sign opposite to `σ`, then `τ ≤ 0`.
-/

open Finset

namespace SquarePacking.S11Opt.Split.U4

def DA : ℕ := 10 ^ 20
def DL : ℕ := 10 ^ 12
def DK : ℕ := 10 ^ 20
def DR : ℕ := 10 ^ 10

/-- The value of a sparse row. -/
noncomputable def spVal (sp : List (ℕ × ℤ)) (hv : ℕ → ℝ) : ℝ :=
  (sp.map fun e => (e.2 : ℝ) * hv e.1).sum

/-- A row holds. -/
def RowOK (sp : List (ℕ × ℤ)) (kt : ℕ) (hv : ℕ → ℝ) (τ : ℝ) : Prop :=
  0 ≤ spVal sp hv / DA + τ * kt / DK

/-- The dense form of a sparse row (33 coordinates). -/
def densify (sp : List (ℕ × ℤ)) : List ℤ :=
  (List.range 33).map fun k => ((sp.filter fun e => e.1 == k).map Prod.snd).sum

lemma densify_length (sp : List (ℕ × ℤ)) : (densify sp).length = 33 := by simp [densify]

lemma densify_getD (sp : List (ℕ × ℤ)) {k : ℕ} (hk : k < 33) :
    (densify sp).getD k 0 = ((sp.filter fun e => e.1 == k).map Prod.snd).sum := by
  simp [densify, List.getD_eq_getElem?_getD, hk]

lemma spVal_eq_dense (sp : List (ℕ × ℤ)) (hsp : ∀ e ∈ sp, e.1 < 33) (hv : ℕ → ℝ) :
    spVal sp hv = ∑ k ∈ range 33, ((densify sp).getD k 0 : ℝ) * hv k := by
  rw [Finset.sum_congr rfl fun k hk => by rw [densify_getD sp (Finset.mem_range.mp hk)]]
  induction sp with
  | nil => simp [spVal]
  | cons e sp ih =>
    have he : e.1 < 33 := hsp e List.mem_cons_self
    have ih' := ih fun x hx => hsp x (List.mem_cons_of_mem _ hx)
    have split : ∀ k, (((e :: sp).filter fun x => x.1 == k).map Prod.snd).sum
        = (if e.1 = k then e.2 else 0) + ((sp.filter fun x => x.1 == k).map Prod.snd).sum := by
      intro k
      by_cases h : e.1 = k
      · simp [h]
      · simp [h]
    simp only [split, Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [← ih']
    have : ∑ k ∈ range 33, ((if e.1 = k then e.2 else 0 : ℤ) : ℝ) * hv k = (e.2 : ℝ) * hv e.1 := by
      rw [Finset.sum_eq_single e.1]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_range.mpr he) h
    rw [this]; simp [spVal]

/-! ## Linear combinations of dense rows -/

def combo : List ℕ → List (List ℤ) → List ℤ
  | l :: ls, r :: rs => List.zipWith (· + ·) (r.map fun a => (l : ℤ) * a) (combo ls rs)
  | _, _ => List.replicate 33 0

lemma combo_length : ∀ (lam : List ℕ) (R : List (List ℤ)), (∀ r ∈ R, r.length = 33) →
    (combo lam R).length = 33
  | l :: ls, r :: rs, h => by
    simp only [combo, List.length_zipWith, List.length_map]
    rw [h r List.mem_cons_self, combo_length ls rs fun x hx => h x (List.mem_cons_of_mem _ hx)]
    simp
  | [], _, _ => by simp [combo]
  | _ :: _, [], _ => by simp [combo]

lemma getD_zipWith_add {a b : List ℤ} {k : ℕ} (ha : a.length = 33) (hb : b.length = 33)
    (hk : k < 33) : (List.zipWith (· + ·) a b).getD k 0 = a.getD k 0 + b.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, ha, hb, hk]

lemma getD_map_mul (r : List ℤ) (l : ℤ) (k : ℕ) :
    (r.map fun a => l * a).getD k 0 = l * r.getD k 0 := by
  rcases lt_or_ge k r.length with h | h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

/-- `∑ᵢ λᵢ (∑ₖ Rᵢₖ hvₖ) = ∑ₖ (λᵀR)ₖ hvₖ`. -/
lemma sum_combo : ∀ (lam : List ℕ) (R : List (List ℤ)), (∀ r ∈ R, r.length = 33) →
    ∀ hv : ℕ → ℝ, ((lam.zip R).map fun p => (p.1 : ℝ) * ∑ k ∈ range 33, (p.2.getD k 0 : ℝ) * hv k).sum
      = ∑ k ∈ range 33, ((combo lam R).getD k 0 : ℝ) * hv k
  | l :: ls, r :: rs, h, hv => by
    have hr : r.length = 33 := h r List.mem_cons_self
    have hrs : ∀ x ∈ rs, x.length = 33 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, combo]
    rw [sum_combo ls rs hrs hv, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [getD_zipWith_add (by simp [hr]) (combo_length ls rs hrs) hk', getD_map_mul]
    push_cast; ring
  | [], R, _, hv => by
    simp only [List.zip_nil_left, List.map_nil, List.sum_nil, combo]
    symm; refine Finset.sum_eq_zero fun k hk => ?_
    have h0 : (List.replicate 33 (0 : ℤ)).getD k 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
    rw [h0]; simp
  | _ :: _, [], _, hv => by
    simp only [List.zip_nil_right, List.map_nil, List.sum_nil, combo]
    symm; refine Finset.sum_eq_zero fun k hk => ?_
    have h0 : (List.replicate 33 (0 : ℤ)).getD k 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
    rw [h0]; simp

/-! ## The certificate check -/

lemma list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- `∑ₖ |Sₖ - [k = j] t| rIₖ`. -/
def absDot (S : List ℤ) (j : ℕ) (t : ℤ) (rI : List ℕ) : ℤ :=
  ((List.range 33).map fun k => |S.getD k 0 - (if k = j then t else 0)| * (rI.getD k 0 : ℤ)).sum

def natDot (a b : List ℕ) : ℕ := ((a.zip b).map fun p => p.1 * p.2).sum

def certOK (rowsD : List (List ℤ)) (kts rI b : List ℕ) (j : ℕ) (σ : Bool) (lam : List ℕ) : Bool :=
  (lam.length == b.length) && (b.all fun i => decide (i < rowsD.length)) &&
    ((b.map fun i => rowsD.getD i []).all fun r => r.length == 33) &&
    decide (absDot (combo lam (b.map fun i => rowsD.getD i [])) j
        ((if σ then 1 else -1) * ((DA * DL : ℕ) : ℤ)) rI * DK
      + (natDot lam (b.map fun i => kts.getD i 0) : ℤ) * DA * DR
      < (rI.getD j 0 : ℤ) * DA * DL * DK)

lemma natDot_cast (a b : List ℕ) (τ : ℝ) :
    ((a.zip b).map fun p => (p.1 : ℝ) * (τ * p.2 / DK)).sum = τ * natDot a b / DK := by
  induction a generalizing b with
  | nil => simp [natDot]
  | cons x xs ih =>
    cases b with
    | nil => simp [natDot]
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, ih, natDot]
      push_cast; ring

lemma sum_zip_map_nonneg (a : List ℕ) (b : List ℕ) (g : ℕ → ℝ) (h : ∀ i ∈ b, 0 ≤ g i) :
    0 ≤ ((a.zip b).map fun p => (p.1 : ℝ) * g p.2).sum := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (h y List.mem_cons_self))
        (ih ys fun i hi => h i (List.mem_cons_of_mem _ hi))

lemma zip_map_congr (a : List ℕ) (b : List ℕ) (f g : ℕ → ℝ) (h : ∀ i ∈ b, f i = g i) :
    ((a.zip b).map fun p => (p.1 : ℝ) * f p.2).sum = ((a.zip b).map fun p => (p.1 : ℝ) * g p.2).sum := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      rw [h y List.mem_cons_self, ih ys fun i hi => h i (List.mem_cons_of_mem _ hi)]

lemma zip_map_split (a : List ℕ) (b : List ℕ) (f g : ℕ → ℝ) :
    ((a.zip b).map fun p => (p.1 : ℝ) * (f p.2 + g p.2)).sum
      = ((a.zip b).map fun p => (p.1 : ℝ) * f p.2).sum + ((a.zip b).map fun p => (p.1 : ℝ) * g p.2).sum := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, ih]; ring

lemma zip_map_comp {β : Type*} (a : List ℕ) (b : List ℕ) (F : ℕ → β) (g : β → ℝ) :
    ((a.zip (b.map F)).map fun p => (p.1 : ℝ) * g p.2).sum
      = ((a.zip b).map fun p => (p.1 : ℝ) * g (F p.2)).sum := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys => simp only [List.map_cons, List.zip_cons_cons, List.sum_cons, ih]

lemma zip_map_mul_right (a : List ℕ) (b : List ℕ) (f : ℕ → ℝ) (c : ℝ) :
    ((a.zip b).map fun p => (p.1 : ℝ) * (f p.2 * c)).sum
      = ((a.zip b).map fun p => (p.1 : ℝ) * f p.2).sum * c := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, ih]; ring

/-- **Soundness of a certificate.** -/
theorem certOK_sound {rowsS : List (List (ℕ × ℤ))} {rowsD : List (List ℤ)} {kts rI b : List ℕ}
    {j : ℕ} {σ : Bool} {lam : List ℕ}
    (hD : rowsD = rowsS.map densify) (hS : ∀ sp ∈ rowsS, ∀ e ∈ sp, e.1 < 33)
    (h : certOK rowsD kts rI b j σ lam = true)
    {hv : ℕ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hrows : ∀ i ∈ b, RowOK (rowsS.getD i []) (kts.getD i 0) hv τ)
    (hb : ∀ k < 33, |hv k| ≤ τ * rI.getD k 0 / DR)
    (hj : j < 33) (hsat : (if σ then hv j else -hv j) = -(τ * rI.getD j 0 / DR)) : False := by
  simp only [certOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hbi⟩, hR⟩, hineq⟩ := h
  set F : ℕ → List ℤ := fun i => rowsD.getD i []
  set R := b.map F
  have hR' : ∀ r ∈ R, r.length = 33 := fun r hr => by
    have := hR r hr; simpa using this
  set G : List ℤ → ℝ := fun r => ∑ k ∈ range 33, ((r.getD k 0 : ℤ) : ℝ) * hv k
  have hg : ∀ i ∈ b, spVal (rowsS.getD i []) hv * (1 / DA) = G (F i) * (1 / DA) := by
    intro i hi
    have hlt : i < rowsS.length := by
      have := hbi i hi; rw [hD, List.length_map] at this; exact this
    have e1 : F i = densify (rowsS.getD i []) := by
      simp only [F, hD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt,
        Option.map_some, Option.getD_some]
    have hmem : rowsS.getD i [] ∈ rowsS := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
    rw [e1, spVal_eq_dense _ (hS _ hmem) hv]
  -- the non-negative combination of the rows
  have h0 := sum_zip_map_nonneg lam b
    (fun i => spVal (rowsS.getD i []) hv * (1 / DA) + τ * (kts.getD i 0 : ℕ) / DK)
    (fun i hi => by have := hrows i hi; unfold RowOK at this; rw [mul_one_div]; exact this)
  rw [zip_map_split lam b (fun i => spVal (rowsS.getD i []) hv * (1 / DA))
    (fun i => τ * ((kts.getD i 0 : ℕ) : ℝ) / DK), zip_map_congr lam b _ _ hg,
    zip_map_mul_right lam b (fun i => G (F i)), ← zip_map_comp lam b F G, sum_combo lam R hR' hv] at h0
  have hkt : ((lam.zip b).map fun p => (p.1 : ℝ) * (τ * ((kts.getD p.2 0 : ℕ) : ℝ) / DK)).sum
      = τ * natDot lam (b.map fun i => kts.getD i 0) / DK := by
    rw [← natDot_cast]
    exact (zip_map_comp lam b (fun i => kts.getD i 0) (fun n : ℕ => τ * (n : ℝ) / DK)).symm
  rw [hkt] at h0
  -- split off the coordinate `j`
  set S := combo lam R
  set t : ℤ := (if σ then 1 else -1) * ((DA * DL : ℕ) : ℤ)
  have hsplit : ∑ k ∈ range 33, ((S.getD k 0 : ℤ) : ℝ) * hv k
      = ∑ k ∈ range 33, (((S.getD k 0 - if k = j then t else 0 : ℤ)) : ℝ) * hv k + (t : ℝ) * hv j := by
    have : ∑ k ∈ range 33, (((if k = j then t else 0 : ℤ)) : ℝ) * hv k = (t : ℝ) * hv j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk; simp [hk]
      · intro hn; exact absurd (Finset.mem_range.mpr hj) hn
    rw [← this, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  have hres : ∑ k ∈ range 33, (((S.getD k 0 - if k = j then t else 0 : ℤ)) : ℝ) * hv k
      ≤ τ * (absDot S j t rI : ℝ) / DR := by
    have eA : (absDot S j t rI : ℝ) = ∑ k ∈ range 33,
        ((|S.getD k 0 - (if k = j then t else 0)| : ℤ) : ℝ) * ((rI.getD k 0 : ℕ) : ℝ) := by
      unfold absDot; rw [list_sum_range]; push_cast; rfl
    rw [eA, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    set x : ℝ := (((S.getD k 0 - if k = j then t else 0 : ℤ)) : ℝ)
    have hx : ((|S.getD k 0 - (if k = j then t else 0)| : ℤ) : ℝ) = |x| := by
      simp only [x]; push_cast; rfl
    rw [hx]
    calc x * hv k ≤ |x| * |hv k| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ |x| * (τ * rI.getD k 0 / DR) := mul_le_mul_of_nonneg_left (hb k hk') (abs_nonneg _)
      _ = τ * (|x| * (rI.getD k 0 : ℕ)) / DR := by ring
  have htj : (t : ℝ) * hv j = -((DA * DL : ℕ) : ℝ) * (τ * rI.getD j 0 / DR) := by
    simp only [t]
    cases σ with
    | true => simp only [if_true] at hsat ⊢; push_cast; rw [hsat]; ring
    | false =>
      simp only [Bool.false_eq_true, if_false] at hsat ⊢
      push_cast
      have : hv j = τ * rI.getD j 0 / DR := by linarith
      rw [this]; ring
  rw [hsplit, htj] at h0
  have hineq' : ((absDot S j t rI : ℤ) : ℝ) * DK + (natDot lam (b.map fun i => kts.getD i 0) : ℝ) * DA * DR
      < (rI.getD j 0 : ℝ) * DA * DL * DK := by exact_mod_cast hineq
  have hDA : (0 : ℝ) < DA := by norm_num [DA]
  have hDK : (0 : ℝ) < DK := by norm_num [DK]
  have hDR : (0 : ℝ) < DR := by norm_num [DR]
  have key : 0 ≤ τ * ((absDot S j t rI : ℝ) * DK + (natDot lam (b.map fun i => kts.getD i 0) : ℝ) * DA * DR
      - (rI.getD j 0 : ℝ) * DA * DL * DK) := by
    have h1 : 0 ≤ (τ * (absDot S j t rI : ℝ) / DR + -((DA * DL : ℕ) : ℝ) * (τ * rI.getD j 0 / DR))
        * (1 / DA) + τ * (natDot lam (b.map fun i => kts.getD i 0) : ℝ) / DK := by
      have hm := mul_le_mul_of_nonneg_right
        (add_le_add_right hres (-((DA * DL : ℕ) : ℝ) * (τ * rI.getD j 0 / DR)))
        (by positivity : (0 : ℝ) ≤ 1 / DA)
      linarith
    have e : τ * ((absDot S j t rI : ℝ) * DK + (natDot lam (b.map fun i => kts.getD i 0) : ℝ) * DA * DR
        - (rI.getD j 0 : ℝ) * DA * DL * DK)
        = ((τ * (absDot S j t rI : ℝ) / DR + -((DA * DL : ℕ) : ℝ) * (τ * rI.getD j 0 / DR))
          * (1 / DA) + τ * (natDot lam (b.map fun i => kts.getD i 0) : ℝ) / DK) * (DA * DR * DK) := by
      push_cast; field_simp; ring
    rw [e]; positivity
  have : τ * ((absDot S j t rI : ℝ) * DK + (natDot lam (b.map fun i => kts.getD i 0) : ℝ) * DA * DR
      - (rI.getD j 0 : ℝ) * DA * DL * DK) < 0 := mul_neg_of_pos_of_neg hτ (by linarith)
  linarith

end SquarePacking.S11Opt.Split.U4
