import ElevenSquare.Pending.S06_CaseCheckSupport
namespace ElevenSquare.Pending.CaseChecks
open OrderedData
-- Local depth allowance for checking 64 eleven-entry masks; worker memory is capped.
set_option maxRecDepth 4096 in
theorem case_block31 : Block rowKey recordedCaseTuplesChunk31.toList 64 [0, 3, 5, 6, 7, 8, 9, 10, 12, 13, 14] [1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13] := by
  exact ⟨adjacent_sound rowKey _ (by decide), rfl, rfl, rfl⟩
set_option maxRecDepth 4096 in
theorem case_good31 : ∀ row ∈ recordedCaseTuplesChunk31.toList, rowMask row ∈ canonicalMasks := by
  exact rowsCheck_sound _ (by decide)
end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.case_block31
#print axioms ElevenSquare.Pending.CaseChecks.case_good31
