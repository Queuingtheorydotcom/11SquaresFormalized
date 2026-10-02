import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.SourceBridge
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.Data
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class00.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.FeatureB
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedAssembly
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicFeatureRowCached

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def featureFamily : Fin 2 → Finset QPoint := ![G005.featureA, G005.featureB]
def featureThreshold : Fin 2 → ℕ := ![3, 2]

def rowCertificate : SymbolicFeatureRowCertificate 2 where
  source := source
  targets := [.majority 0 target00, .majority 1 target01]
  cover := node000

theorem source_eq : source = symbolicWallScaledSlab (1 : Fin 16) := by
  exact source_eq_scaled_slab

theorem targetPolygons_eq :
    rowCertificate.targets.map SymbolicFeatureTarget.polygon = targets := by rfl

theorem targetChecks : ∀ target ∈ rowCertificate.targets, target.Check := by
  intro target ht
  simp only [rowCertificate, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> trivial

theorem majority_target (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlt : (left : ℝ) ≤ t) (htu : t ≤ (right : ℝ)) :
    ∀ feature polygon,
      SymbolicFeatureTarget.majority feature polygon ∈ rowCertificate.targets →
      SymbolicPolygonContains polygon t q.center →
      BaselineMajorityCapture (featureFamily feature)
        (featureThreshold feature) q := by
  intro feature polygon ht hcontains
  simp only [rowCertificate, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at ht
  rcases ht with h | h
  · injection h with hf hp
    subst feature
    subst polygon
    change BaselineMajorityCapture G005.featureA 3 q
    have hcl : (SymbolicCell01Semantics.Class00.left : ℝ) ≤ t := by
      simpa [SymbolicCell01Semantics.Class00.left, left] using hlt
    have hcu : t ≤ (SymbolicCell01Semantics.Class00.right : ℝ) := by
      have hu : (right : ℝ) ≤
          (SymbolicCell01Semantics.Class00.right : ℝ) := by
        norm_num [right, SymbolicCell01Semantics.Class00.right]
      exact le_trans htu hu
    apply SymbolicCell01Semantics.Class00.majority_of_target q t ha hcl hcu
    simpa only [show target00 = SymbolicCell01Semantics.Class00.target from rfl]
      using hcontains
  · injection h with hf hp
    subst feature
    subst polygon
    change BaselineMajorityCapture G005.featureB 2 q
    apply SymbolicCell01Semantics.featureB_early q t ha
    · simpa [left] using hlt
    · have hu : (right : ℝ) ≤ (31/64 : ℝ) := by norm_num [right]
      exact le_trans htu hu
    · simpa only [show target01 = SymbolicCell00.Regime000.target from rfl]
        using hcontains

theorem window_capture_of_cover
    (hcover : ∀ s : ℝ, (left : ℝ) ≤ s → s ≤ (right : ℝ) →
      ∀ x : Point, SymbolicPolygonContains source s x →
        ∃ polygon ∈ targets, SymbolicPolygonContains polygon s x) :
    G005.WindowCapture 1 (left, right) := by
  intro P _ owners hs t _ _ ha hlt htu
  have hcell : ClosedCell (1 : Fin 16)
      (normalizeCenter (P.squares (owners 1)).center) :=
    hs.1 1 (by decide)
  obtain ⟨feature, hfeat⟩ := symbolic_feature_row_choice_of_cover
    P (owners 1) 1 featureFamily featureThreshold t left right
    rowCertificate (by simpa [rowCertificate] using source_eq)
    (by simpa only [targetPolygons_eq] using hcover)
    targetChecks hlt htu ha hcell (majority_target _ t ha hlt htu)
    (by intro p hp; simp [rowCertificate,
      SymbolicFeatureRowCertificate.blockerPoints,
      SymbolicFeatureTarget.blockerPoint] at hp)
  fin_cases feature
  · exact Or.inl (by simpa [featureFamily, featureThreshold] using hfeat)
  · exact Or.inr (by simpa [featureFamily, featureThreshold] using hfeat)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.window_capture_of_cover
