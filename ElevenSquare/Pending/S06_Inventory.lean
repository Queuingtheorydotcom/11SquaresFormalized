import ElevenSquare.Pending.S06_CasesExact
import ElevenSquare.Pending.S06_ExclusionPartition
import ElevenSquare.Pending.S06_Baseline
import ElevenSquare.Pending.S06_PriorSupport
import ElevenSquare.Pending.S06_Returned
import ElevenSquare.Pending.S06_TupleBounds
import ElevenSquare.Pending.S06_CandidateMasks

/-! Assemble the complete exclusion families using the exact finite partition.
Full compiler and axiom acceptance of these dependencies remains to be checked. -/

namespace ElevenSquare.Pending
noncomputable section

-- Tuple length and index bounds are proved in S06_TupleBounds.

-- Exact source-order enumeration is proved in S06_CasesExact.

-- The four exact identities are proved in S06_CandidateMasks.

-- Exact counts, disjointness, and partition are proved in S06_ExclusionPartition.

theorem all_noncandidates_excluded (k : Fin 2184) (hk : k.val ∉ candidateIndices) :
    Excluded k := by
  have hm : k.val ∈ Finset.range 2184 \ candidateIndices :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr k.isLt, hk⟩
  rw [← exclusion_inventory.2.2.2.2.2.2] at hm
  rcases Finset.mem_union.mp hm with hm | hr
  · rcases Finset.mem_union.mp hm with hb | hp
    · exact baseline_excluded k hb
    · exact prior_excluded baseline_excluded k hp
  · exact returned_excluded k hr

theorem occupied_case_is_candidate (P : Packing 11 coverCap) (k : Fin 2184)
    (hk : Occupies P (caseMask k)) : k.val ∈ candidateIndices := by
  by_contra h
  exact all_noncandidates_excluded k h P hk


end
end ElevenSquare.Pending

#print axioms ElevenSquare.Pending.recorded_case_tuple_bounds
#print axioms ElevenSquare.Pending.recorded_candidate_masks

#print axioms ElevenSquare.Pending.exclusion_inventory

-- Audit the complete exclusion-family composition.
#print axioms ElevenSquare.Pending.all_noncandidates_excluded
#print axioms ElevenSquare.Pending.occupied_case_is_candidate

#print axioms ElevenSquare.Pending.recorded_cases_exact
