import ElevenSquare.Pending.ArrayNodup
namespace ElevenSquare.Pending.OrderedData

theorem array_key_injective {α : Type*} [Inhabited α] {key : α → ℕ}
    {xs : Array α} {n : ℕ} (hs : xs.size = n)
    (ho : List.IsChain (fun a b => key a < key b) xs.toList) :
    Function.Injective (fun i : Fin n => key xs[i.val]!) := by
  letI : IsTrans α (fun a b => key a < key b) := ⟨fun _ _ _ => lt_trans⟩
  have hp := List.pairwise_iff_getElem.mp (List.isChain_iff_pairwise.mp ho)
  intro i j hij
  have hi : i.val < xs.size := by rw [hs]; exact i.isLt
  have hj : j.val < xs.size := by rw [hs]; exact j.isLt
  change key xs[i.val]! = key xs[j.val]! at hij
  rw [getElem!_pos xs i.val hi, getElem!_pos xs j.val hj,
    ← Array.getElem_toList, ← Array.getElem_toList] at hij
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact False.elim ((ne_of_lt (hp i.val j.val hi hj h)) hij)
  · exact h
  · exact False.elim ((ne_of_lt (hp j.val i.val hj hi h)) hij.symm)

end ElevenSquare.Pending.OrderedData
#print axioms ElevenSquare.Pending.OrderedData.array_key_injective
