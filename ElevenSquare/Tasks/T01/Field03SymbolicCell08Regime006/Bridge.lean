import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime006.Cover
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.SourceBridge

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime006
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem source_eq : source = symbolicWallScaledSlab (8 : Fin 16) := by
  exact ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.source_eq_scaled_slab

theorem wall_cover_checked : node000.Check
    (symbolicWallScaledSlab (8 : Fin 16)) targets (1387/4096) (1605/4096) := by
  rw [← source_eq]
  exact cover_checked

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime006

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime006.wall_cover_checked
