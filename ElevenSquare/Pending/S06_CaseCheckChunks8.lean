import ElevenSquare.Pending.S06_CaseCheckSupport
namespace ElevenSquare.Pending.CaseChecks
open OrderedData
-- Local depth allowance for checking 64 eleven-entry masks; worker memory is capped.
set_option maxRecDepth 4096 in
theorem case_block8 : Block rowKey recordedCaseTuplesChunk8.toList 64 [0, 1, 2, 3, 5, 6, 7, 9, 12, 14, 15] [0, 1, 2, 3, 5, 6, 9, 11, 12, 13, 15] := by
  exact ⟨adjacent_sound rowKey _ (by decide), rfl, rfl, rfl⟩
set_option maxRecDepth 4096 in
theorem case_good8 : ∀ row ∈ recordedCaseTuplesChunk8.toList, rowMask row ∈ canonicalMasks := by
  exact rowsCheck_sound _ (by decide)
end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.case_block8
#print axioms ElevenSquare.Pending.CaseChecks.case_good8
