import ElevenSquare.Pending.S06_CaseCheckSupport
namespace ElevenSquare.Pending.CaseChecks
open OrderedData
-- Local depth allowance for checking 64 eleven-entry masks; worker memory is capped.
set_option maxRecDepth 4096 in
theorem case_block17 : Block rowKey recordedCaseTuplesChunk17.toList 64 [0, 1, 2, 5, 6, 7, 9, 10, 12, 13, 14] [0, 1, 2, 6, 7, 8, 10, 11, 12, 14, 15] := by
  exact ⟨adjacent_sound rowKey _ (by decide), rfl, rfl, rfl⟩
set_option maxRecDepth 4096 in
theorem case_good17 : ∀ row ∈ recordedCaseTuplesChunk17.toList, rowMask row ∈ canonicalMasks := by
  exact rowsCheck_sound _ (by decide)
end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.case_block17
#print axioms ElevenSquare.Pending.CaseChecks.case_good17
