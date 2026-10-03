import ElevenSquare.Pending.S06_CaseCheckSupport
namespace ElevenSquare.Pending.CaseChecks
open OrderedData
-- Local depth allowance for checking 64 eleven-entry masks; worker memory is capped.
set_option maxRecDepth 4096 in
theorem case_block6 : Block rowKey recordedCaseTuplesChunk6.toList 64 [0, 1, 2, 3, 4, 7, 8, 9, 10, 12, 15] [0, 1, 2, 3, 4, 8, 9, 11, 13, 14, 15] := by
  exact ⟨adjacent_sound rowKey _ (by decide), rfl, rfl, rfl⟩
set_option maxRecDepth 4096 in
theorem case_good6 : ∀ row ∈ recordedCaseTuplesChunk6.toList, rowMask row ∈ canonicalMasks := by
  exact rowsCheck_sound _ (by decide)
end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.case_block6
#print axioms ElevenSquare.Pending.CaseChecks.case_good6
