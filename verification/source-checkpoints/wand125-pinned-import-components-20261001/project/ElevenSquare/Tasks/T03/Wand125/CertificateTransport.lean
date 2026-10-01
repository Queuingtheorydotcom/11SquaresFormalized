import ElevenSquare.Tasks.T03.Wand125.Cells
import ElevenSquare.Pending.S06_Data
import ElevenSquare.Pending.S05_Trace

namespace ElevenSquare.Pending.T03.Wand125
noncomputable section

private def emptyState : PoseState where
  rows := fun _ => []
  owned := fun _ => []

/-- An independently proved exclusion supplies the original certificate contract. -/
theorem certificate_of_excluded (k : Fin 2184)
    (h : ∀ P : Packing 11 coverCap, ¬ Occupies P (caseMask k)) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  refine ⟨emptyState, emptyState, ?_, VerifiedTrace.refl _, Or.inl ⟨0, rfl⟩⟩
  intro P _ ho
  exact (h P ho).elim

/-- Bounds and case correspondence are explicit hypotheses, proved separately
for each literal imported case. No inherited inventory admission is used. -/
theorem certificate_of_case (k : Fin 2184) (J : List ℕ)
    (hJ : ∀ j ∈ J, j < 16) (hm : cellsOf J = caseMask k)
    (h : SquarePacking.S11Opt.CaseExcluded J) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  apply certificate_of_excluded k
  intro P ho
  exact excludes_occupancy J hJ h P (by simpa only [hm] using ho)

end
end ElevenSquare.Pending.T03.Wand125
