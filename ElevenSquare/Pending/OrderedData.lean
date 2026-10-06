import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card

/-! Small, kernel-checked certificates for ordered literal data. -/
namespace ElevenSquare.Pending.OrderedData

def adjacent {α : Type*} (key : α → ℕ) : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: xs => decide (key a < key b) && adjacent key (b :: xs)

theorem adjacent_sound {α : Type*} (key : α → ℕ) :
    ∀ xs, adjacent key xs = true → List.IsChain (fun a b => key a < key b) xs
  | [], _ => List.isChain_nil
  | [_], _ => List.isChain_singleton _
  | a :: b :: xs, h => by
    simp only [adjacent, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.isChain_cons_cons.mpr ⟨h.1, adjacent_sound key (b :: xs) h.2⟩

structure Block {α : Type*} (key : α → ℕ) (xs : List α)
    (n : ℕ) (first last : α) : Prop where
  ordered : List.IsChain (fun a b => key a < key b) xs
  length_eq : xs.length = n
  head_eq : xs.head? = some first
  last_eq : xs.getLast? = some last

theorem Block.append {α : Type*} {key : α → ℕ} {xs ys : List α}
    {n m : ℕ} {a b c d : α} (hx : Block key xs n a b) (hy : Block key ys m c d)
    (hbc : key b < key c) : Block key (xs ++ ys) (n + m) a d := by
  have hxne : xs ≠ [] := by intro h; simpa [h] using hx.head_eq
  have hyne : ys ≠ [] := by intro h; simpa [h] using hy.head_eq
  refine ⟨hx.ordered.append hy.ordered ?_, ?_, ?_, ?_⟩
  · rw [hx.last_eq, hy.head_eq]
    simp only [Option.mem_def, Option.some.injEq]
    rintro x rfl y rfl
    exact hbc
  · rw [List.length_append, hx.length_eq, hy.length_eq]
  · cases xs with
    | nil => exact False.elim (hxne rfl)
    | cons x xs => exact hx.head_eq
  · rw [List.getLast?_append_of_ne_nil xs hyne, hy.last_eq]

theorem ordered_nodup {α : Type*} {key : α → ℕ} {xs : List α}
    (h : List.IsChain (fun a b => key a < key b) xs) : xs.Nodup := by
  letI : IsTrans α (fun a b => key a < key b) := ⟨fun _ _ _ => lt_trans⟩
  have hp := List.isChain_iff_pairwise.mp h
  exact hp.imp (fun {a b} hab heq => (ne_of_lt hab) (congrArg key heq))

theorem Block.card {α : Type*} [DecidableEq α] {key : α → ℕ} {xs : List α}
    {n : ℕ} {a b : α} (h : Block key xs n a b) : xs.toFinset.card = n := by
  exact (List.toFinset_card_of_nodup (ordered_nodup h.ordered)).trans h.length_eq

theorem array_toList_append {α : Type*} (xs ys : Array α) :
    (xs ++ ys).toList = xs.toList ++ ys.toList := by
  exact Array.toList_append

end ElevenSquare.Pending.OrderedData
#print axioms ElevenSquare.Pending.OrderedData.adjacent_sound
#print axioms ElevenSquare.Pending.OrderedData.Block.append
#print axioms ElevenSquare.Pending.OrderedData.ordered_nodup

#print axioms ElevenSquare.Pending.OrderedData.Block.card
