import ElevenSquare.Pending.S06_CaseCheckSupport
namespace ElevenSquare.Pending.CaseChecks
open OrderedData
-- Local depth allowance for checking 64 eleven-entry masks; worker memory is capped.
set_option maxRecDepth 4096 in
theorem case_block30 : Block rowKey recordedCaseTuplesChunk30.toList 64 [0, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13] [0, 3, 5, 6, 7, 8, 9, 10, 11, 13, 14] := by
  exact ⟨adjacent_sound rowKey _ (by decide), rfl, rfl, rfl⟩
set_option maxRecDepth 4096 in
theorem case_good30 : ∀ row ∈ recordedCaseTuplesChunk30.toList, rowMask row ∈ canonicalMasks := by
  exact rowsCheck_sound _ (by decide)
end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.case_block30
#print axioms ElevenSquare.Pending.CaseChecks.case_good30
