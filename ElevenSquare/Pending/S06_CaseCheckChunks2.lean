import ElevenSquare.Pending.S06_CaseCheckSupport
namespace ElevenSquare.Pending.CaseChecks
open OrderedData
-- Local depth allowance for checking 64 eleven-entry masks; worker memory is capped.
set_option maxRecDepth 4096 in
theorem case_block2 : Block rowKey recordedCaseTuplesChunk2.toList 64 [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13] [0, 1, 2, 3, 4, 5, 7, 11, 12, 13, 14] := by
  exact ⟨adjacent_sound rowKey _ (by decide), rfl, rfl, rfl⟩
set_option maxRecDepth 4096 in
theorem case_good2 : ∀ row ∈ recordedCaseTuplesChunk2.toList, rowMask row ∈ canonicalMasks := by
  exact rowsCheck_sound _ (by decide)
end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.case_block2
#print axioms ElevenSquare.Pending.CaseChecks.case_good2
