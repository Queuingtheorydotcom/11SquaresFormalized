import ElevenSquare.Pending.S06_Inventory
import ElevenSquare.Tasks.T05.Transport
import ElevenSquare.Simplified.FourCollisionBridge

/-! UNFINISHED FORMALIZATION OBLIGATIONS. See handoffs/S07_Bridge.md.
Every `sorry` in this file is an explicit outstanding proof, not verified evidence. -/

namespace ElevenSquare.Pending
noncomputable section

def physicalSymmetry (g : Fin 4) (flip : Bool) (p : Point) : Point :=
  let z := (if flip then halfTurn else id) (view g (normalizeCenter p))
  ((coverCap-1)*z.1+1/2, (coverCap-1)*z.2+1/2)

def D4Image (P Q : Packing 11 coverCap) : Prop :=
  ∃ g : Fin 4, ∃ flip : Bool, ∃ perm : Equiv.Perm Owner,
    ∀ i p, ClosedSquare (Q.squares i) (physicalSymmetry g flip p) ↔
      ClosedSquare (P.squares (perm i)) p

-- The relation transports the complete squares, including their orientations.
theorem d4_forces_case438
    (hex : ∀ k : Fin 2184, k.val ∉ candidateIndices → Excluded k)
    (P : Packing 11 coverCap) :
    ∃ Q : Packing 11 coverCap, D4Image P Q ∧ Occupies Q (caseMask ⟨438, by omega⟩) := by
  obtain ⟨g, flip, hocc⟩ := ElevenSquare.Simplified.FourCollision.force_case438 hex P
    (T05Transport.transportedPacking P) (T05Transport.normalized_center P)
  refine ⟨T05Transport.transportedPacking P g flip, ?_, hocc⟩
  exact ⟨g, flip, Equiv.refl Owner,
    fun i p => T05Transport.closed_square_iff P g flip i p⟩


end
end ElevenSquare.Pending
