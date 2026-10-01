import ElevenSquare.Interop.Wand125.Certificates
import ElevenSquare.Interop.Wand125.Families.CaseOrder
import ElevenSquare.Pending.S06_ExclusionPartition

/-!
# Family-level transport of wand125 exclusions

The `split` branch of wand125/n11-optimality-lean states its remaining units as
`CaseExcluded (maskAt i)` over its own index lists (`genericIdx`, `priorIdx`,
`returnedIdx`, `candIdx`). This file proves, in the kernel, that those lists and
`maskAt` agree with the recorded case tuples and families here, and turns any such
family statement into the initialized-terminal-trace contracts of `S06`.

Every theorem below is conditional: it takes the upstream family statement as a
hypothesis. No admission site and no public statement is changed.
-/

namespace ElevenSquare.Interop.Wand125
open ElevenSquare.Pending
open SquarePacking.S11Opt
open SquarePacking.S11Opt.Split
noncomputable section

set_option maxRecDepth 100000

/-! ## Case order -/

theorem tuple_eq_maskAt (k : Fin 2184) : recordedCaseTuples[k.val]! = maskAt k.val := by
  have hklt : k.val < recordedCaseTuples.size := by
    rw [recorded_case_tuple_bounds.1]
    exact k.isLt
  have hl : k.val < recordedCaseTuples.toList.length := by
    rw [Array.length_toList]
    exact hklt
  rw [maskAt, ← CaseOrder.tuples_eq_authorMasks, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hl, Option.getD_some, getElem!_pos recordedCaseTuples k.val hklt,
    Array.getElem_toList]

/-! ## Exclusion and certificates from `CaseExcluded (maskAt k)` -/

theorem excluded_of_maskAt (k : Fin 2184) (h : CaseExcluded (maskAt k.val)) :
    ∀ P : Packing 11 coverCap, ¬ Occupies P (caseMask k) := by
  intro P
  have hklt : k.val < recordedCaseTuples.size := by
    rw [recorded_case_tuple_bounds.1]
    exact k.isLt
  have hmem : recordedCaseTuples[k.val]! ∈ recordedCaseTuples.toList := by
    simp [getElem!_pos, hklt]
  have hJ := (recorded_case_tuple_bounds.2 _ hmem).2
  rw [← tuple_eq_maskAt] at h
  exact excludes_occupancy _ hJ h P

private def emptyState : PoseState where
  rows := fun _ => []
  owned := fun _ => []

/-- An exclusion yields the trace contract through the empty state, as in
`Certificates.lean`. The hypothesis is `Excluded k` unfolded, so that this file
does not import `S06_Baseline` (which imports the T01 dispatcher). -/
theorem certificate_of_excluded (k : Fin 2184)
    (h : ∀ P : Packing 11 coverCap, ¬ Occupies P (caseMask k)) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  refine ⟨emptyState, emptyState, ?_, VerifiedTrace.refl _, Or.inl ⟨0, rfl⟩⟩
  intro P _ ho
  exact (h P ho).elim

theorem certificate_of_maskAt (k : Fin 2184) (h : CaseExcluded (maskAt k.val)) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b :=
  certificate_of_excluded k (excluded_of_maskAt k h)

/-! ## Families -/

theorem priorArray_eq : priorArray.toList = priorIdx := by decide +kernel

theorem returnedArray_eq : returnedArray.toList = returnedIdx := by decide +kernel

theorem candidateArray_eq : candidateArray.toList = candIdx := by decide +kernel

theorem genericIdx_baseline : ∀ i ∈ genericIdx, i ∈ baselineIndices := by
  have hcand : ∀ i ∈ genericIdx, i < 2184 ∧ i ∉ candIdx := by decide +kernel
  have hpr : ∀ i ∈ genericIdx, i ∉ priorIdx ∧ i ∉ returnedIdx := by decide +kernel
  intro i hi
  have hu : i ∈ baselineIndices ∪ priorIndices ∪ returnedIndices := by
    rw [exclusion_inventory.2.2.2.2.2.2]
    simp [candidateIndices, candidateArray_eq, (hcand i hi).1, (hcand i hi).2]
  simp only [Finset.mem_union, priorIndices, returnedIndices, priorArray_eq, returnedArray_eq,
    List.mem_toFinset] at hu
  rcases hu with (h | h) | h
  · exact h
  · exact absurd h (hpr i hi).1
  · exact absurd h (hpr i hi).2

theorem prior_certificate_of (hfam : ∀ i ∈ priorIdx, CaseExcluded (maskAt i))
    (k : Fin 2184) (hk : k.val ∈ priorIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  have hk' : k.val ∈ priorIdx := by
    simpa [priorIndices, priorArray_eq] using hk
  exact certificate_of_maskAt k (hfam _ hk')

theorem returned_certificate_of (hfam : ∀ i ∈ returnedIdx, CaseExcluded (maskAt i))
    (k : Fin 2184) (hk : k.val ∈ returnedIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  have hk' : k.val ∈ returnedIdx := by
    simpa [returnedIndices, returnedArray_eq] using hk
  exact certificate_of_maskAt k (hfam _ hk')

theorem generic_certificate_of (hfam : ∀ i ∈ genericIdx, CaseExcluded (maskAt i))
    (k : Fin 2184) (hk : k.val ∈ genericIdx) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b :=
  certificate_of_maskAt k (hfam _ hk)

/-- The upstream statement for all non-candidate cases gives every
non-candidate certificate. -/
theorem noncandidate_certificate_of (h : NoncandidateExcluded)
    (k : Fin 2184) (hk : k.val ∉ candidateIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b := by
  have hk' : k.val ∉ candIdx := by
    simpa [candidateIndices, candidateArray_eq] using hk
  exact certificate_of_maskAt k (h k.val k.isLt hk')

end
end ElevenSquare.Interop.Wand125

#print axioms ElevenSquare.Interop.Wand125.tuple_eq_maskAt
#print axioms ElevenSquare.Interop.Wand125.certificate_of_maskAt
#print axioms ElevenSquare.Interop.Wand125.genericIdx_baseline
#print axioms ElevenSquare.Interop.Wand125.prior_certificate_of
#print axioms ElevenSquare.Interop.Wand125.returned_certificate_of
#print axioms ElevenSquare.Interop.Wand125.generic_certificate_of
#print axioms ElevenSquare.Interop.Wand125.noncandidate_certificate_of
