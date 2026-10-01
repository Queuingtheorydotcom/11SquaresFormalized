import Sqpack.S11Opt.FieldAll
import Sqpack.S11Opt.Split.Interface

/-!
# UField — the 59 baseline field certificates (1,904 cases)

`S11Opt.F00`, `S11Opt.F01` … `F58` and `S11Opt.FieldAll` (`excludedField_all`).  This unit also
does the index bookkeeping: every non-candidate case outside the generic, prior and returned
lists is excluded by some field certificate (directly or through the half-turn).
-/

namespace SquarePacking.S11Opt.Split
open SquarePacking.S11Opt.FieldAll

set_option maxRecDepth 100000

/-- The field cases: the non-candidate cases outside the generic, prior and returned lists. -/
def fieldIdx : List ℕ :=
  (List.range 2184).filter fun i =>
    !(decide (i ∈ candIdx) || decide (i ∈ genericIdx) || decide (i ∈ priorIdx) ||
      decide (i ∈ returnedIdx))

/-- Some field certificate applies to every field case, directly or through the half-turn. -/
lemma fieldIdx_app : ∀ i ∈ fieldIdx, (app (maskAt i) || app (hmask (maskAt i))) = true := by
  decide +kernel

/-- **UField.** -/
theorem field_excluded : ∀ i < 2184, i ∉ candIdx → i ∉ genericIdx → i ∉ priorIdx →
    i ∉ returnedIdx → CaseExcluded (maskAt i) := by
  intro i hi hc hg hp hr
  have hf : i ∈ fieldIdx := by
    simp [fieldIdx, hi, hc, hg, hp, hr]
  apply excludedField_all
  simp only [excludedField, List.mem_filter]
  exact ⟨mem_canonical_iff_maskAt.mpr ⟨i, hi, rfl⟩, fieldIdx_app i hf⟩

end SquarePacking.S11Opt.Split

#print axioms SquarePacking.S11Opt.Split.field_excluded
