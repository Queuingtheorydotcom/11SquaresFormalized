import ElevenSquare.Tasks.T06.BranchInventory
import Mathlib.Data.Fintype.BigOperators

namespace ElevenSquare.Tasks.T06
open ElevenSquare ElevenSquare.Pending
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

abbrev FeatureSelection :=
  (p : Fin 14) → { id : Fin 112 // id ∈ allowedFeatureIds p }

def digitChoices (a b : Fin 2) (c : Fin 4) (d e f g h : Fin 2) : Fin 14 → Fin 112 :=
  ![7, 12, 22, 29, (![35, 39] : Fin 2 → Fin 112) a,
    (![41, 45] : Fin 2 → Fin 112) b, (![49, 50, 53, 54] : Fin 4 → Fin 112) c,
    61, 69, (![73, 77] : Fin 2 → Fin 112) d, (![83, 87] : Fin 2 → Fin 112) e,
    (![91, 95] : Fin 2 → Fin 112) f, (![97, 101] : Fin 2 → Fin 112) g,
    (![107, 111] : Fin 2 → Fin 112) h]

def digitIndex (a b : Fin 2) (c : Fin 4) (d e f g h : Fin 2) : Fin 512 :=
  Fin.ofNat 512 (256*a.val + 128*b.val + 32*c.val + 16*d.val + 8*e.val +
    4*f.val + 2*g.val + h.val)


end
end ElevenSquare.Tasks.T06
