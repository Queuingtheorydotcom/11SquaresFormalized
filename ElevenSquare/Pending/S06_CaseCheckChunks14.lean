import ElevenSquare.Pending.S06_CaseCheckSupport
namespace ElevenSquare.Pending.CaseChecks
open OrderedData
-- Local depth allowance for checking 64 eleven-entry masks; worker memory is capped.
set_option maxRecDepth 4096 in
theorem case_block14 : Block rowKey recordedCaseTuplesChunk14.toList 64 [0, 1, 2, 4, 5, 7, 8, 9, 11, 12, 14] [0, 1, 2, 4, 6, 7, 8, 9, 10, 11, 14] := by
  exact ⟨adjacent_sound rowKey _ (by decide), rfl, rfl, rfl⟩
set_option maxRecDepth 4096 in
theorem case_good14 : ∀ row ∈ recordedCaseTuplesChunk14.toList, rowMask row ∈ canonicalMasks := by
  exact rowsCheck_sound _ (by decide)
end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.case_block14
#print axioms ElevenSquare.Pending.CaseChecks.case_good14
