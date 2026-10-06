import ElevenSquare.Interop.Wand125.Families

/-!
# Conditional transport of the complete baseline family

The existing case-order and partition theorems identify each native baseline
index as either a generic case or a field case. The two upstream family
statements are explicit hypotheses, so this bridge can be checked independently
of their generated certificate data and the native baseline dispatcher.
-/

namespace ElevenSquare.Interop.Wand125
open ElevenSquare.Pending
open SquarePacking.S11Opt
open SquarePacking.S11Opt.Split
noncomputable section

/-- The field and generic family statements imply every native baseline exclusion. -/
theorem baseline_maskAt_excluded_of
    (hfield : ∀ i < 2184, i ∉ candIdx → i ∉ genericIdx → i ∉ priorIdx →
      i ∉ returnedIdx → CaseExcluded (maskAt i))
    (hgeneric : ∀ i ∈ genericIdx, CaseExcluded (maskAt i))
    (k : Fin 2184) (hk : k.val ∈ baselineIndices) :
    CaseExcluded (maskAt k.val) := by
  by_cases hg : k.val ∈ genericIdx
  · exact hgeneric k.val hg
  obtain ⟨_, _, _, hbp, hbr, _, hpartition⟩ := exclusion_inventory
  have hp : k.val ∉ priorIndices := by
    intro hp
    exact Finset.disjoint_left.mp hbp hk hp
  have hr : k.val ∉ returnedIndices := by
    intro hr
    exact Finset.disjoint_left.mp hbr hk hr
  have hc : k.val ∉ candidateIndices := by
    have hu : k.val ∈ baselineIndices ∪ priorIndices ∪ returnedIndices := by
      simp only [Finset.mem_union]
      exact Or.inl (Or.inl hk)
    rw [hpartition] at hu
    exact (Finset.mem_sdiff.mp hu).2
  exact hfield k.val k.isLt
    (by simpa [candidateIndices, candidateArray_eq] using hc) hg
    (by simpa [priorIndices, priorArray_eq] using hp)
    (by simpa [returnedIndices, returnedArray_eq] using hr)

/-- Preserve the native trace contract using the two explicit family hypotheses. -/
theorem baseline_certificate_of
    (hfield : ∀ i < 2184, i ∉ candIdx → i ∉ genericIdx → i ∉ priorIdx →
      i ∉ returnedIdx → CaseExcluded (maskAt i))
    (hgeneric : ∀ i ∈ genericIdx, CaseExcluded (maskAt i))
    (k : Fin 2184) (hk : k.val ∈ baselineIndices) :
    ∃ a b : PoseState,
      (∀ P : Packing 11 coverCap, IsCharted P → Occupies P (caseMask k) →
        ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) a) ∧
      VerifiedTrace a b ∧ Terminal b :=
  certificate_of_maskAt k (baseline_maskAt_excluded_of hfield hgeneric k hk)

end
end ElevenSquare.Interop.Wand125

#print axioms ElevenSquare.Interop.Wand125.baseline_maskAt_excluded_of
#print axioms ElevenSquare.Interop.Wand125.baseline_certificate_of
