import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.Data
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCoverSlab

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Normalize the fixed rational facets once for all regimes of this cell. -/
theorem source_eq_scaled_slab : source = symbolicWallScaledSlab (1 : Fin 16) := by
  have hrange : (List.finRange 16 : List (Fin 16)) =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
  have hs0 : baselineRationalSite (0 : Fin 16) = ((104991/1000000 : ℚ), (265837/2000000 : ℚ)) := by rfl
  have hs1 : baselineRationalSite (1 : Fin 16) = ((186601/500000 : ℚ), (45503/1000000 : ℚ)) := by rfl
  have hs2 : baselineRationalSite (2 : Fin 16) = ((1267243/2000000 : ℚ), (34689/250000 : ℚ)) := by rfl
  have hs3 : baselineRationalSite (3 : Fin 16) = ((1731123/2000000 : ℚ), (25701/250000 : ℚ)) := by rfl
  have hs4 : baselineRationalSite (4 : Fin 16) = ((206181/2000000 : ℚ), (400379/1000000 : ℚ)) := by rfl
  have hs5 : baselineRationalSite (5 : Fin 16) = ((742311/2000000 : ℚ), (312933/1000000 : ℚ)) := by rfl
  have hs6 : baselineRationalSite (6 : Fin 16) = ((635257/1000000 : ℚ), (166409/400000 : ℚ)) := by rfl
  have hs7 : baselineRationalSite (7 : Fin 16) = ((445439/500000 : ℚ), (167763/500000 : ℚ)) := by rfl
  have hs8 : baselineRationalSite (8 : Fin 16) = ((54561/500000 : ℚ), (332237/500000 : ℚ)) := by rfl
  have hs9 : baselineRationalSite (9 : Fin 16) = ((364743/1000000 : ℚ), (233591/400000 : ℚ)) := by rfl
  have hs10 : baselineRationalSite (10 : Fin 16) = ((1257689/2000000 : ℚ), (687067/1000000 : ℚ)) := by rfl
  have hs11 : baselineRationalSite (11 : Fin 16) = ((1793819/2000000 : ℚ), (599621/1000000 : ℚ)) := by rfl
  have hs12 : baselineRationalSite (12 : Fin 16) = ((268877/2000000 : ℚ), (224299/250000 : ℚ)) := by rfl
  have hs13 : baselineRationalSite (13 : Fin 16) = ((732757/2000000 : ℚ), (215311/250000 : ℚ)) := by rfl
  have hs14 : baselineRationalSite (14 : Fin 16) = ((313399/500000 : ℚ), (954497/1000000 : ℚ)) := by rfl
  have hs15 : baselineRationalSite (15 : Fin 16) = ((895009/1000000 : ℚ), (1734163/2000000 : ℚ)) := by rfl
  simp only [symbolicWallScaledSlab, symbolicWallSlab, baselineCellPolygon,
    hrange, List.map_cons, List.map_nil, List.append_nil]
  simp only [baselineBisector, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
  norm_num [scaledWallFacet, SymbolicQuadratic.scaleByChart,
    SymbolicWallFacet.ofHalfplane, baselineRationalCap, baselineCenterBox,
    source]

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.source_eq_scaled_slab
