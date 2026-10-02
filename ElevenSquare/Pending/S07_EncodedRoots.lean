import ElevenSquare.Pending.S07_EncodedRoot0
import ElevenSquare.Pending.S07_EncodedRoot1
import ElevenSquare.Pending.S07_EncodedRoot2
import ElevenSquare.Pending.S07_EncodedRoot3
import ElevenSquare.Pending.S07_EncodedRoot4
import ElevenSquare.Pending.S07_EncodedRoot5
import Mathlib.Tactic.FinCases
namespace ElevenSquare.Pending.EncodedSearch
open Propagation

theorem all_roots_rejected (k : Fin 6) :
    ¬ Sat compatible supports (initialDomains k.val) (List.range 216) := by
  revert k
  refine Fin.cases root_rejected0 ?_
  refine Fin.cases root_rejected1 ?_
  refine Fin.cases root_rejected2 ?_
  refine Fin.cases root_rejected3 ?_
  refine Fin.cases root_rejected4 ?_
  refine Fin.cases root_rejected5 ?_
  intro i
  exact Fin.elim0 i

end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.all_roots_rejected
