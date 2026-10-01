import Sqpack.S11Opt.Split.U1Labels

/-!
# U3 — definitions: the four views, overlay regions, the finite search

* `vw g` (`g < 4`) — the author's views `g₀ … g₃` (PROOF.md §6) in unit coordinates of
  `[0, Ux]²`: the identity, `x ↦ Ux − x`, the quarter-turn `(x, y) ↦ (Ux − y, x)` and the diagonal
  reflection `(x, y) ↦ (y, x)`.  Each maps a packing in `cbox S` to a packing in `cbox S`
  (`PackIn.vw`), with the angle `va g θ`.
* `InT t p` — `p` lies in the closed overlay region of the label tuple `t = [l₀, l₁, l₂, l₃]`:
  `vw g p` lies in the closed cell `l_g` for every view.
* `BanT t t'` — two centres in the regions `t`, `t'` (and in `[1/2, Ux − 1/2]²`) are closer than 1.
* `ext` — the finite search of the D4 bridge, on bitmasks; `ext_true` is its soundness: a valid
  assignment of regions to owners makes it return `true`.
-/

namespace SquarePacking.S11Opt.Split

/-! ## Views -/

/-- The four views, in unit coordinates. -/
noncomputable def vw : ℕ → ℝ × ℝ → ℝ × ℝ
  | 0, p => p
  | 1, p => (Ux - p.1, p.2)
  | 2, p => (Ux - p.2, p.1)
  | _, p => (p.2, p.1)

/-- Their inverses. -/
noncomputable def vinv : ℕ → ℝ × ℝ → ℝ × ℝ
  | 0, p => p
  | 1, p => (Ux - p.1, p.2)
  | 2, p => (p.2, Ux - p.1)
  | _, p => (p.2, p.1)

/-- The angle of the image square. -/
noncomputable def va : ℕ → ℝ → ℝ
  | 0, θ => θ
  | 2, θ => θ + Real.pi / 2
  | _, θ => -θ

lemma vw_vinv (g : ℕ) (q : ℝ × ℝ) : vw g (vinv g q) = q := by
  rcases g with _ | _ | _ | g <;> simp [vw, vinv]

/-- In the image frame the local coordinates are those of the original point, up to sign and
order. -/
lemma coord_vw (g : ℕ) (c p : ℝ × ℝ) (θ : ℝ) :
    (|(coord (vw g c) (va g θ) (vw g p)).1| = |(coord c θ p).1| ∧
      |(coord (vw g c) (va g θ) (vw g p)).2| = |(coord c θ p).2|) ∨
    (|(coord (vw g c) (va g θ) (vw g p)).1| = |(coord c θ p).2| ∧
      |(coord (vw g c) (va g θ) (vw g p)).2| = |(coord c θ p).1|) := by
  rcases g with _ | _ | _ | g
  · left; simp [vw, va]
  · left
    simp only [vw, va, coord, Real.cos_neg, Real.sin_neg]
    constructor
    · rw [← abs_neg]; congr 1; ring
    · congr 1; ring
  · left
    simp only [vw, va, coord, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    constructor <;> congr 1 <;> ring
  · right
    simp only [vw, va, coord, Real.cos_neg, Real.sin_neg]
    constructor <;> congr 1 <;> ring

lemma mem_sq_vw (g : ℕ) {c p : ℝ × ℝ} {θ : ℝ} :
    vw g p ∈ sq (vw g c) (va g θ) 1 ↔ p ∈ sq c θ 1 := by
  simp only [sq, Set.mem_ofPred_eq]
  rcases coord_vw g c p θ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  exact and_comm

lemma mem_sqInt_vw (g : ℕ) {c p : ℝ × ℝ} {θ : ℝ} :
    vw g p ∈ sqInt (vw g c) (va g θ) 1 ↔ p ∈ sqInt c θ 1 := by
  simp only [sqInt, Set.mem_ofPred_eq]
  rcases coord_vw g c p θ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  exact and_comm

lemma mem_cbox_vw (g : ℕ) {S : ℝ} {p : ℝ × ℝ} : vw g p ∈ cbox S ↔ p ∈ cbox S := by
  rcases g with _ | _ | _ | g <;> simp only [vw, cbox, Set.mem_ofPred_eq] <;>
    constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- A view of a packing in `cbox S` is a packing in `cbox S`. -/
lemma PackIn.vw (g : ℕ) {S : ℝ} {n : ℕ} {ctr : Fin n → ℝ × ℝ} {ang : Fin n → ℝ}
    (h : PackIn (cbox S) ctr ang) :
    PackIn (cbox S) (fun i => Split.vw g (ctr i)) (fun i => va g (ang i)) := by
  refine ⟨fun i q hq => ?_, fun i j hij => ?_⟩
  · rw [← vw_vinv g q] at hq ⊢
    exact (mem_cbox_vw g).mpr (h.1 i ((mem_sq_vw g).mp hq))
  · rw [Set.disjoint_left]
    intro q h1 h2
    rw [← vw_vinv g q] at h1 h2
    exact Set.disjoint_left.mp (h.2 i j hij) ((mem_sqInt_vw g).mp h1) ((mem_sqInt_vw g).mp h2)

/-! ## Regions -/

/-- `p` lies in the closed overlay region of the label tuple `t`. -/
def InT (t : List ℕ) (p : ℝ × ℝ) : Prop := ∀ g < 4, InCellU (t.getD g 0) (vw g p)

/-- Centres in the regions `t` and `t'` are closer than `1`. -/
def BanT (t t' : List ℕ) : Prop :=
  ∀ p q : ℝ × ℝ, InB p → InB q → InT t p → InT t' q → (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 < 1

/-! ## The finite search -/

/-- An entry `(r, t, m)` of the owner table: region `r`, its labels `t`, its compatibility mask. -/
abbrev Entry := ℕ × List ℕ × ℕ

/-- The labels of the entry `e` in the views `1, 2, 3` lie in the target masks `T`. -/
def inTargets (T : List (List ℕ)) (e : Entry) : Bool :=
  (T.getD 0 []).contains (e.2.1.getD 1 0) && (T.getD 1 []).contains (e.2.1.getD 2 0) &&
    (T.getD 2 []).contains (e.2.1.getD 3 0)

/-- Depth-first search: can the owners `rest` be given regions from their tables `dom`, in the
targets `T`, pairwise compatible and compatible with the bitmask `avail`? -/
def ext (dom : List (List Entry)) (T : List (List ℕ)) : ℕ → List ℕ → Bool
  | _, [] => true
  | avail, o :: rest => (dom.getD o []).any fun e =>
      inTargets T e && avail.testBit e.1 && ext dom T (avail &&& e.2.2) rest

/-- **Soundness of the search.**  If every owner `o ∈ rest` has an entry `F o` in its table, in the
targets, allowed by `avail`, and the entries are pairwise compatible, the search succeeds. -/
theorem ext_true (dom : List (List Entry)) (T : List (List ℕ)) (F : ℕ → Entry) :
    ∀ (rest : List ℕ) (avail : ℕ), (∀ o ∈ rest, F o ∈ dom.getD o [] ∧ inTargets T (F o) = true) →
      (∀ o ∈ rest, avail.testBit (F o).1 = true) →
      rest.Pairwise (fun o o' => (F o).2.2.testBit (F o').1 = true) → ext dom T avail rest = true
  | [], _, _, _, _ => rfl
  | o :: rest, avail, hF, hav, hpw => by
    simp only [ext, List.any_eq_true, Bool.and_eq_true]
    refine ⟨F o, (hF o List.mem_cons_self).1, ⟨⟨(hF o List.mem_cons_self).2,
      hav o List.mem_cons_self⟩, ?_⟩⟩
    rw [List.pairwise_cons] at hpw
    refine ext_true dom T F rest _ (fun o' h => hF o' (List.mem_cons_of_mem _ h))
      (fun o' h => ?_) hpw.2
    rw [Nat.testBit_land, hav o' (List.mem_cons_of_mem _ h), hpw.1 o' h, Bool.and_self]

end SquarePacking.S11Opt.Split
