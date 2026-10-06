import ElevenSquare.Pending.S06_Data
import ElevenSquare.Pending.OrderedData
namespace ElevenSquare.Pending.ExclusionCounts
open OrderedData
theorem baseline_block0 : Block id baselineArrayChunk0.toList 64 0 63 := by
  exact ⟨adjacent_sound id _ (by decide), rfl, rfl, rfl⟩
#print axioms baseline_block0
theorem baseline_block1 : Block id baselineArrayChunk1.toList 64 64 127 := by
  exact ⟨adjacent_sound id _ (by decide), rfl, rfl, rfl⟩
#print axioms baseline_block1
theorem baseline_block2 : Block id baselineArrayChunk2.toList 64 128 191 := by
  exact ⟨adjacent_sound id _ (by decide), rfl, rfl, rfl⟩
#print axioms baseline_block2
theorem baseline_block3 : Block id baselineArrayChunk3.toList 64 192 260 := by
  exact ⟨adjacent_sound id _ (by decide), rfl, rfl, rfl⟩
#print axioms baseline_block3
theorem baseline_block4 : Block id baselineArrayChunk4.toList 64 261 324 := by
  exact ⟨adjacent_sound id _ (by decide), rfl, rfl, rfl⟩
#print axioms baseline_block4
end ElevenSquare.Pending.ExclusionCounts
