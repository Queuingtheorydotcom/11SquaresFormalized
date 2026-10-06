import ElevenSquare.Pending.OrderedData
import Mathlib.Data.List.Nodup
namespace ElevenSquare.Pending.OrderedData

theorem array_get_injective {α : Type*} [Inhabited α] {xs : Array α} {n : ℕ}
    (hs : xs.size = n) (hn : xs.toList.Nodup) :
    Function.Injective (fun i : Fin n => xs[i.val]!) := by
  intro i j hij
  change xs[i.val]! = xs[j.val]! at hij
  have hi : i.val < xs.size := by rw [hs]; exact i.isLt
  have hj : j.val < xs.size := by rw [hs]; exact j.isLt
  rw [getElem!_pos xs i.val hi, getElem!_pos xs j.val hj,
    ← Array.getElem_toList, ← Array.getElem_toList] at hij
  exact Fin.ext (hn.getElem_inj_iff.mp hij)

theorem Block.array_get_injective {α : Type*} [Inhabited α] {key : α → ℕ}
    {xs : Array α} {n : ℕ} {a b : α} (h : Block key xs.toList n a b) :
    Function.Injective (fun i : Fin n => xs[i.val]!) := by
  have hs : xs.size = n := by
    simpa only [Array.length_toList] using h.length_eq
  have hn : xs.toList.Nodup := by
    exact ordered_nodup h.ordered
  exact OrderedData.array_get_injective hs hn

end ElevenSquare.Pending.OrderedData
#print axioms ElevenSquare.Pending.OrderedData.Block.array_get_injective
