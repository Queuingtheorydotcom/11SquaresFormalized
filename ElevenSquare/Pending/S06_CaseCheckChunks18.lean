import ElevenSquare.Pending.S06_CaseCheckSupport
namespace ElevenSquare.Pending.CaseChecks
open OrderedData
-- Local depth allowance for checking 64 eleven-entry masks; worker memory is capped.
set_option maxRecDepth 4096 in
theorem case_block18 : Block rowKey recordedCaseTuplesChunk18.toList 64 [0, 1, 2, 6, 7, 9, 10, 11, 12, 13, 14] [0, 1, 3, 4, 5, 6, 7, 10, 11, 12, 14] := by
  exact ⟨adjacent_sound rowKey _ (by decide), rfl, rfl, rfl⟩
set_option maxRecDepth 4096 in
theorem case_good18 : ∀ row ∈ recordedCaseTuplesChunk18.toList, rowMask row ∈ canonicalMasks := by
  exact rowsCheck_sound _ (by decide)
end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.case_block18
#print axioms ElevenSquare.Pending.CaseChecks.case_good18
