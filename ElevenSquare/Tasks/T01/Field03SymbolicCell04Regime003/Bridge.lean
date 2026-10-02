import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime003.Cover
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime000.SourceBridge

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime003
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem source_eq : source = symbolicWallScaledSlab (4 : Fin 16) := by
  exact ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime000.source_eq_scaled_slab

theorem wall_cover_checked : node000.Check
    (symbolicWallScaledSlab (4 : Fin 16)) targets (677/4096) (1195/4096) := by
  rw [← source_eq]
  exact cover_checked

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime003

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime003.wall_cover_checked
