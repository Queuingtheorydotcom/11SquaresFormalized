import ElevenSquare.Simplified.LocalAliasWitness

/-! Exact finite alias coverage, with no handwritten witness for each of the
512 raw selections and 42 rows. Ordinary kernel reduction checks every case. -/
namespace ElevenSquare.Simplified.LocalAlias
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem alias_chunk_00 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 0 s) row = true := by decide

private theorem alias_chunk_01 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 1 s) row = true := by decide

private theorem alias_chunk_02 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 2 s) row = true := by decide

private theorem alias_chunk_03 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 3 s) row = true := by decide

private theorem alias_chunk_04 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 4 s) row = true := by decide

private theorem alias_chunk_05 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 5 s) row = true := by decide

private theorem alias_chunk_06 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 6 s) row = true := by decide

private theorem alias_chunk_07 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 7 s) row = true := by decide

private theorem alias_chunk_08 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 8 s) row = true := by decide

private theorem alias_chunk_09 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 9 s) row = true := by decide

private theorem alias_chunk_10 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 10 s) row = true := by decide

private theorem alias_chunk_11 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 11 s) row = true := by decide

private theorem alias_chunk_12 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 12 s) row = true := by decide

private theorem alias_chunk_13 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 13 s) row = true := by decide

private theorem alias_chunk_14 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 14 s) row = true := by decide

private theorem alias_chunk_15 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 15 s) row = true := by decide

private theorem alias_chunk_16 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 16 s) row = true := by decide

private theorem alias_chunk_17 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 17 s) row = true := by decide

private theorem alias_chunk_18 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 18 s) row = true := by decide

private theorem alias_chunk_19 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 19 s) row = true := by decide

private theorem alias_chunk_20 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 20 s) row = true := by decide

private theorem alias_chunk_21 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 21 s) row = true := by decide

private theorem alias_chunk_22 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 22 s) row = true := by decide

private theorem alias_chunk_23 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 23 s) row = true := by decide

private theorem alias_chunk_24 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 24 s) row = true := by decide

private theorem alias_chunk_25 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 25 s) row = true := by decide

private theorem alias_chunk_26 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 26 s) row = true := by decide

private theorem alias_chunk_27 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 27 s) row = true := by decide

private theorem alias_chunk_28 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 28 s) row = true := by decide

private theorem alias_chunk_29 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 29 s) row = true := by decide

private theorem alias_chunk_30 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 30 s) row = true := by decide

private theorem alias_chunk_31 : ∀ (s : Fin 16) (row : Fin 42),
    enabledWitnessCheck (rawGroupIndex 31 s) row = true := by decide

private theorem all_alias_checks (q : Fin 32) (s : Fin 16) (row : Fin 42) :
    enabledWitnessCheck (rawGroupIndex q s) row = true := by
  fin_cases q
  · exact alias_chunk_00 s row
  · exact alias_chunk_01 s row
  · exact alias_chunk_02 s row
  · exact alias_chunk_03 s row
  · exact alias_chunk_04 s row
  · exact alias_chunk_05 s row
  · exact alias_chunk_06 s row
  · exact alias_chunk_07 s row
  · exact alias_chunk_08 s row
  · exact alias_chunk_09 s row
  · exact alias_chunk_10 s row
  · exact alias_chunk_11 s row
  · exact alias_chunk_12 s row
  · exact alias_chunk_13 s row
  · exact alias_chunk_14 s row
  · exact alias_chunk_15 s row
  · exact alias_chunk_16 s row
  · exact alias_chunk_17 s row
  · exact alias_chunk_18 s row
  · exact alias_chunk_19 s row
  · exact alias_chunk_20 s row
  · exact alias_chunk_21 s row
  · exact alias_chunk_22 s row
  · exact alias_chunk_23 s row
  · exact alias_chunk_24 s row
  · exact alias_chunk_25 s row
  · exact alias_chunk_26 s row
  · exact alias_chunk_27 s row
  · exact alias_chunk_28 s row
  · exact alias_chunk_29 s row
  · exact alias_chunk_30 s row
  · exact alias_chunk_31 s row

theorem rawSelection_alias_cover (r : Fin 512) (row : Fin 42) :
    ∃ g ∈ rowAliases (branchRows (rawSelectionBranch r) row), RawEnabled r g := by
  apply enabled_alias_of_witness_check
  let q : Fin 32 := ⟨r.val / 16, by have hr := r.isLt; omega⟩
  let s : Fin 16 := ⟨r.val % 16, Nat.mod_lt _ (by decide)⟩
  have hr : rawGroupIndex q s = r := by
    apply Fin.ext
    dsimp [rawGroupIndex, q, s]
    omega
  rw [← hr]
  exact all_alias_checks q s row

end ElevenSquare.Simplified.LocalAlias

#print axioms ElevenSquare.Simplified.LocalAlias.rawSelection_alias_cover
