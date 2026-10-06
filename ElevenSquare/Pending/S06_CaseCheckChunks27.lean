import ElevenSquare.Pending.S06_CaseCheckSupport
namespace ElevenSquare.Pending.CaseChecks
open OrderedData
-- Local depth allowance for checking 64 eleven-entry masks; worker memory is capped.
set_option maxRecDepth 4096 in
theorem case_block27 : Block rowKey recordedCaseTuplesChunk27.toList 64 [0, 2, 3, 4, 5, 7, 9, 10, 12, 13, 15] [0, 2, 3, 4, 7, 8, 9, 10, 11, 12, 15] := by
  exact ⟨adjacent_sound rowKey _ (by decide), rfl, rfl, rfl⟩
set_option maxRecDepth 4096 in
theorem case_good27 : ∀ row ∈ recordedCaseTuplesChunk27.toList, rowMask row ∈ canonicalMasks := by
  exact rowsCheck_sound _ (by decide)
end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.case_block27
#print axioms ElevenSquare.Pending.CaseChecks.case_good27
