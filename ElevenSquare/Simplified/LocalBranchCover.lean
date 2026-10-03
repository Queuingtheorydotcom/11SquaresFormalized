import ElevenSquare.Simplified.LocalAliasCover
import ElevenSquare.Tasks.T06.BranchSelection

/-! The original nonlinear branch-cover argument, reusing the finite boolean
alias theorem instead of 21,504 separately written alias witnesses. -/
namespace ElevenSquare.Simplified.LocalAlias
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T06
noncomputable section

theorem rawEnabled_nonneg (S : ℝ) (q₀ : Owner → UnitSquare)
    (r : Fin 512) (h : Displacement)
    (hpairs : ∀ p v, 0 ≤ featureGap q₀ (allFeatures (rawSelections r p)) v h)
    (hwalls : ∀ i v w, 0 ≤ gapValue S q₀ (.wall i v w) h)
    (g : Gap) (hg : RawEnabled r g) : 0 ≤ gapValue S q₀ g h := by
  cases g with
  | wall i v w => exact hwalls i v w
  | pair f v =>
      obtain ⟨p, hp⟩ := hg
      change 0 ≤ featureGap q₀ f v h
      rw [← hp]
      exact hpairs p v

theorem rawSelection_rows_nonneg (S : ℝ) (q₀ : Owner → UnitSquare)
    (r : Fin 512) (h : Displacement)
    (hpairs : ∀ p v, 0 ≤ featureGap q₀ (allFeatures (rawSelections r p)) v h)
    (hwalls : ∀ i v w, 0 ≤ gapValue S q₀ (.wall i v w) h) :
    ∀ row, ∃ g ∈ rowAliases (branchRows (rawSelectionBranch r) row),
      0 ≤ gapValue S q₀ g h := by
  intro row
  obtain ⟨g, hg, henabled⟩ := rawSelection_alias_cover r row
  exact ⟨g, hg, rawEnabled_nonneg S q₀ r h hpairs hwalls g henabled⟩

theorem branch_from_allowed_choices (S : ℝ) (q₀ : Owner → UnitSquare)
    (p : LocalPacket)
    (haliases : ∀ b row, p.aliases b row = rowAliases (branchRows b row))
    (choose : Fin 14 → SeparationFeature)
    (hchoose : ∀ pair, choose pair ∈ allowedFeatures pair) :
    ∃ b : Fin 128, ∀ h,
      (∀ pair v, 0 ≤ featureGap q₀ (choose pair) v h) →
      (∀ i v w, 0 ≤ gapValue S q₀ (.wall i v w) h) →
      ∀ row, ∃ g ∈ p.aliases b row, 0 ≤ gapValue S q₀ g h := by
  classical
  have hids : ∀ pair, ∃ id ∈ allowedFeatureIds pair, allFeatures id = choose pair := by
    intro pair
    exact List.mem_map.mp (hchoose pair)
  choose ids hmem hid using hids
  let selection : FeatureSelection := fun pair => ⟨ids pair, hmem pair⟩
  obtain ⟨r, hr⟩ := rawSelections_complete selection
  refine ⟨rawSelectionBranch r, ?_⟩
  intro h hpairs hwalls row
  rw [haliases]
  apply rawSelection_rows_nonneg S q₀ r h ?_ hwalls row
  intro pair v
  rw [hr pair]
  change 0 ≤ featureGap q₀ (allFeatures (ids pair)) v h
  rw [hid pair]
  exact hpairs pair v

theorem allowed_choices_of_unavailable (S : ℝ) (q₀ : Owner → UnitSquare)
    (radii : Fin 33 → ℝ)
    (hunavailable : ∀ h, InRectangle radii h → ∀ u : Fin 88,
      featureGap q₀ (allFeatures (unavailableFeatureIds u))
        (unavailableCorners u) h < 0)
    (h : Displacement) (hrect : InRectangle radii h)
    (hf : LocalFeasible S q₀ h) :
    ∀ pair, ∃ f ∈ allowedFeatures pair, ∀ v, 0 ≤ featureGap q₀ f v h := by
  intro pair
  obtain ⟨f, hpair, hnonneg⟩ := feasible_pair_feature S q₀ h hf
    (contactPairs pair).1 (contactPairs pair).2 (contactPairs_distinct pair)
  obtain ⟨id, hid, heq⟩ := feature_inventory_complete pair f hpair
  rcases allowed_or_unavailable pair id hid with hallowed | ⟨u, hu⟩
  · refine ⟨f, ?_, hnonneg⟩
    exact List.mem_map.mpr ⟨id, hallowed, heq⟩
  · have hneg := hunavailable h hrect u
    rw [hu, heq] at hneg
    exact False.elim ((not_lt_of_ge (hnonneg (unavailableCorners u))) hneg)

/-- Assembly of the concrete 512-to-128 branch cover. -/
theorem branch_cover_of_unavailable (S : ℝ) (q₀ : Owner → UnitSquare)
    (p : LocalPacket)
    (haliases : ∀ b row, p.aliases b row = rowAliases (branchRows b row))
    (hunavailable : ∀ h, InRectangle p.radii h → ∀ u : Fin 88,
      featureGap q₀ (allFeatures (unavailableFeatureIds u))
        (unavailableCorners u) h < 0) : BranchCover S q₀ p := by
  apply branch_cover_from_feature_choices S q₀ p allowedFeatures
  · exact allowed_choices_of_unavailable S q₀ p.radii hunavailable
  · exact branch_from_allowed_choices S q₀ p haliases

end
end ElevenSquare.Simplified.LocalAlias

#print axioms ElevenSquare.Simplified.LocalAlias.branch_cover_of_unavailable
