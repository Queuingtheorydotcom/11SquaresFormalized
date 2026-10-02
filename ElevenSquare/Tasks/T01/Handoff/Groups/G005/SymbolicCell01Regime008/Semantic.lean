import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime000.SourceBridge
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime008.Data
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.Class02.MedianAggregate
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.FeatureB
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Semantics.BlockerTarget
import ElevenSquare.Tasks.T01.Handoff.Groups.G005.FixedAssembly
import ElevenSquare.Tasks.T01.Handoff.PlanAPI.SymbolicFeatureRowCached

namespace ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime008
open ElevenSquare.Pending ElevenSquare.Tasks.T01
  ElevenSquare.Tasks.T01.Handoff.PlanAPI
noncomputable section

def featureFamily : Fin 2 → Finset QPoint := ![G005.featureA, G005.featureB]
def featureThreshold : Fin 2 → ℕ := ![3, 2]

def rowCertificate : SymbolicFeatureRowCertificate 2 where
  source := source
  targets := [.majority 0 target00, .majority 1 target01,
    .blocker target02 SymbolicCell01Semantics.blockPoint half]
  cover := node000

theorem source_eq : source = symbolicWallScaledSlab (1 : Fin 16) := by
  simpa only [source, SymbolicCell01Regime000.source] using
    SymbolicCell01Regime000.source_eq_scaled_slab

theorem targetPolygons_eq :
    rowCertificate.targets.map SymbolicFeatureTarget.polygon = targets := by rfl

theorem targetChecks : ∀ target ∈ rowCertificate.targets, target.Check := by
  intro target ht
  simp only [rowCertificate, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · trivial
  · trivial
  · refine ⟨by norm_num [half], by norm_num [half], ?_⟩
    intro f hf
    have hfacet := SymbolicCell01Semantics.block_target_facets f (by simpa [half] using hf)
    simpa only [show target02 = SymbolicCell01Regime008.target02 from rfl] using hfacet

theorem featureA_target (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlt : (left : ℝ) ≤ t) (htu : t ≤ (right : ℝ))
    (hcontains : SymbolicPolygonContains target00 t q.center) :
    BaselineMajorityCapture G005.featureA 3 q := by
  have hcl : (SymbolicCell01Semantics.Class02.left : ℝ) ≤ t := by
    have hle : (SymbolicCell01Semantics.Class02.left : ℝ) ≤ (left : ℝ) := by
      norm_num [SymbolicCell01Semantics.Class02.left, left]
    exact le_trans hle hlt
  have hcu : t ≤ (SymbolicCell01Semantics.Class02.right : ℝ) := by
    have hle : (right : ℝ) ≤ (SymbolicCell01Semantics.Class02.right : ℝ) := by
      norm_num [SymbolicCell01Semantics.Class02.right, right]
    exact le_trans htu hle
  apply SymbolicCell01Semantics.Class02.majority_of_target q t ha hcl hcu
  simpa only [show target00 = SymbolicCell01Semantics.Class02.target from rfl]
    using hcontains

theorem featureB_target (q : UnitSquare) (t : ℝ)
    (ha : q.axis = chartAxis t)
    (hlt : (left : ℝ) ≤ t) (htu : t ≤ (right : ℝ))
    (hcontains : SymbolicPolygonContains target01 t q.center) :
    BaselineMajorityCapture G005.featureB 2 q := by
  apply SymbolicCell01Semantics.featureB_early q t ha
  · have hle : (0 : ℝ) ≤ (left : ℝ) := by norm_num [left]
    exact le_trans hle hlt
  · have hle : (right : ℝ) ≤ (31/64 : ℝ) := by norm_num [right]
    exact le_trans htu hle
  · simpa only [show target01 = SymbolicCell00.Regime000.target from rfl]
      using hcontains

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
    exact featureA_target q t ha hlt htu hcontains
  · injection h with hf hp
    subst feature
    subst polygon
    change BaselineMajorityCapture G005.featureB 2 q
    exact featureB_target q t ha hlt htu hcontains

theorem window_capture_of_cover
    (hcover : ∀ s : ℝ, (left : ℝ) ≤ s → s ≤ (right : ℝ) →
      ∀ x : Point, SymbolicPolygonContains source s x →
        ∃ polygon ∈ targets, SymbolicPolygonContains polygon s x) :
    G005.WindowCapture 1 (left, right) := by
  intro P hc owners hs t _ _ ha hlt htu
  have hcell : ClosedCell (1 : Fin 16)
      (normalizeCenter (P.squares (owners 1)).center) :=
    hs.1 1 (by decide)
  obtain ⟨feature, hfeat⟩ := symbolic_feature_row_choice_of_cover
    P (owners 1) 1 featureFamily featureThreshold t left right
    rowCertificate (by simpa [rowCertificate] using source_eq)
    (by simpa only [targetPolygons_eq] using hcover)
    targetChecks hlt htu ha hcell (majority_target _ t ha hlt htu)
    (by
      intro p hp
      have heq : SymbolicCell01Semantics.blockPoint = p := by
        simpa [rowCertificate, SymbolicFeatureRowCertificate.blockerPoints,
          SymbolicFeatureTarget.blockerPoint] using hp
      subst p
      exact SymbolicCell01Semantics.block_point_owned P hc owners hs)
  fin_cases feature
  · exact Or.inl (by simpa [featureFamily, featureThreshold] using hfeat)
  · exact Or.inr (by simpa [featureFamily, featureThreshold] using hfeat)

end
end ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime008

#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G005.SymbolicCell01Regime008.window_capture_of_cover
