import ElevenSquare.Pending.S06_CaseCheckSupport
namespace ElevenSquare.Pending.CaseChecks
open OrderedData
-- Local depth allowance for checking 64 eleven-entry masks; worker memory is capped.
set_option maxRecDepth 4096 in
theorem case_block20 : Block rowKey recordedCaseTuplesChunk20.toList 64 [0, 1, 3, 4, 5, 7, 8, 9, 10, 13, 15] [0, 1, 3, 4, 6, 7, 8, 9, 10, 14, 15] := by
  exact ⟨adjacent_sound rowKey _ (by decide), rfl, rfl, rfl⟩
set_option maxRecDepth 4096 in
theorem case_good20 : ∀ row ∈ recordedCaseTuplesChunk20.toList, rowMask row ∈ canonicalMasks := by
  exact rowsCheck_sound _ (by decide)
end ElevenSquare.Pending.CaseChecks
#print axioms ElevenSquare.Pending.CaseChecks.case_block20
#print axioms ElevenSquare.Pending.CaseChecks.case_good20
