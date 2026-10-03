import ElevenSquare.Pending.S06_CaseCheckSupport
namespace ElevenSquare.Pending.CaseChecks
open OrderedData
-- Local depth allowance for checking 64 eleven-entry masks; worker memory is capped.
set_option maxRecDepth 4096 in
theorem case_block33 : Block rowKey recordedCaseTuplesChunk33.toList 64 [1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12] [1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13] := by
  exact ⟨adjacent_sound rowKey _ (by decide), rfl, rfl, rfl⟩
set_option maxRecDepth 4096 in
theorem case_good33 : ∀ row ∈ recordedCaseTuplesChunk33.toList, rowMask row ∈ canonicalMasks := by
  exact rowsCheck_sound _ (by decide)
end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.case_block33
#print axioms ElevenSquare.Pending.CaseChecks.case_good33
