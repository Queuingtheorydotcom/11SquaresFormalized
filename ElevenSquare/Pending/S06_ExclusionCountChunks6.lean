import ElevenSquare.Pending.S06_Data
import ElevenSquare.Pending.OrderedData
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData
theorem baseline_block30 : Block id baselineArrayChunk30.toList 11 2167 2181 := by
  exact ⟨adjacent_sound id _ (by decide), rfl, rfl, rfl⟩
#print axioms baseline_block30
theorem prior_block0 : Block id priorArrayChunk0.toList 64 221 1115 := by
  exact ⟨adjacent_sound id _ (by decide), rfl, rfl, rfl⟩
#print axioms prior_block0
theorem prior_block1 : Block id priorArrayChunk1.toList 12 1124 2183 := by
  exact ⟨adjacent_sound id _ (by decide), rfl, rfl, rfl⟩
#print axioms prior_block1
theorem returned_block0 : Block id returnedArrayChunk0.toList 64 1145 1492 := by
  exact ⟨adjacent_sound id _ (by decide), rfl, rfl, rfl⟩
#print axioms returned_block0
theorem returned_block1 : Block id returnedArrayChunk1.toList 64 1499 1887 := by
  exact ⟨adjacent_sound id _ (by decide), rfl, rfl, rfl⟩
#print axioms returned_block1
end ElevenSquare.Pending.ExclusionCounts
