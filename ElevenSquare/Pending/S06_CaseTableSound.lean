import ElevenSquare.Pending.S06_CaseCheckSupport
import ElevenSquare.Pending.ArrayKeyOrder
namespace ElevenSquare.Pending.CaseChecks
open OrderedData

def RowsGood (xs : Array (List ℕ)) : Prop :=
  ∀ row ∈ xs.toList, rowMask row ∈ canonicalMasks

theorem RowsGood.append {xs ys : Array (List ℕ)} (hx : RowsGood xs) (hy : RowsGood ys) :
    RowsGood (xs ++ ys) := by
  intro row hr
  rw [array_toList_append, List.mem_append] at hr
  exact hr.elim (hx row) (hy row)

theorem table_exact (xs : Array (List ℕ))
    (hs : xs.size = 2184) (ho : List.IsChain (fun a b => rowKey a < rowKey b) xs.toList)
    (hg : RowsGood xs) :
    Function.Injective (fun i : Fin 2184 => rowMask xs[i.val]!) ∧
    Finset.univ.image (fun i : Fin 2184 => rowMask xs[i.val]!) = canonicalMasks := by
  have hk := array_key_injective hs ho
  have hi : Function.Injective (fun i : Fin 2184 => rowMask xs[i.val]!) := by
    intro i j hij
    apply hk
    exact congrArg (fun m => 65536-maskWeight m) hij
  refine ⟨hi, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro m hm
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    apply hg
    have hidx : i.val < xs.size := by rw [hs]; exact i.isLt
    rw [getElem!_pos xs i.val hidx]
    exact Array.getElem_mem_toList hidx
  · rw [canonicalMasks_card, Finset.card_image_of_injective _ hi]
    rw [Finset.card_univ, Fintype.card_fin]

-- Convert list/array views before inserting the large concrete table.
theorem table_exact_block (xs : Array (List ℕ)) (a b : List ℕ)
    (hs : xs.size = 2184) (ho : Block rowKey xs.toList 2184 a b)
    (hg : RowsGood xs) :
    Function.Injective (fun i : Fin 2184 => rowMask xs[i.val]!) ∧
    Finset.univ.image (fun i : Fin 2184 => rowMask xs[i.val]!) = canonicalMasks :=
  table_exact xs hs ho.ordered hg

end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.table_exact
