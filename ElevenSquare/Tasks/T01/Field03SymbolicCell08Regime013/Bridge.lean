import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime013.Cover
import ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.SourceBridge

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime013
open ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem source_eq : source = symbolicWallScaledSlab (8 : Fin 16) := by
  exact ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime000.source_eq_scaled_slab

theorem wall_cover_checked : node000.Check
    (symbolicWallScaledSlab (8 : Fin 16)) targets (3301/4096) (1837/2048) := by
  rw [← source_eq]
  exact cover_checked

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime013

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell08Regime013.wall_cover_checked
