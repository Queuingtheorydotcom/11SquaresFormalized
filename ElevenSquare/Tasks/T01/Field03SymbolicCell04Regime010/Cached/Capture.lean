import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime000.SourceBridge
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.Cached.Cover
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.TargetCheck
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicCachedFieldRow
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.MedianLink
import ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime008.MedianBroad

namespace ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.Cached
open ElevenSquare.Pending ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

theorem capture_from_packing (P : Packing 11 coverCap)
    (i j : Owner) (hij : i ≠ j)
    (hcell : ClosedCell 4 (normalizeCenter (P.squares i).center))
    (hother : ClosedCell 0 (normalizeCenter (P.squares j).center))
    (hotherChart : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ (P.squares j).axis = chartAxis s)
    (t : ℝ) (ha : (P.squares i).axis = chartAxis t)
    (hlt : ((2973/4096:ℚ):ℝ) ≤ t) (htu : t ≤ ((1697/2048:ℚ):ℝ)) :
    BaselineMajorityCapture baselineField03Sites 2 (P.squares i) := by
  have hcover : SymbolicCoverSignRefs.Check cache rowCertificate.source
      (rowCertificate.targets.map SymbolicFieldTarget.polygon)
      (2973/4096) (1697/2048) rowCertificate.cover signNode000 := by
    change SymbolicCoverSignRefs.Check cache source
      (rowCertificate.targets.map SymbolicFieldTarget.polygon)
      (2973/4096) (1697/2048) node000 signNode000
    rw [row_targetPolygons_eq]
    exact cover_checked
  apply symbolic_cached_field_row_majority P i 4 baselineField03Sites t
    (2973/4096) (1697/2048) rowCertificate cache signNode000 cache_checked
    ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime000.source_eq_scaled_slab hcover
    row_targets_checked hlt htu ha hcell
  · intro polygon hmem hcontains
    have heq : polygon = target00 := by
      simpa [rowCertificate] using hmem
    subst polygon
    obtain ⟨hbLo, hbHi⟩ := interval_in_representative t hlt htu
    apply Field03SymbolicCell04Regime008.target00_majority_broad (P.squares i)
      t ha hbLo hbHi
    simpa only [target00_eq_representative] using hcontains
  · intro p hp
    rw [row_blockerPoints_eq] at hp
    exact blockerPoints_owned P i j hij hother hotherChart p hp

end
end ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.Cached

#print axioms ElevenSquare.Tasks.T01.Field03SymbolicCell04Regime010.Cached.capture_from_packing
