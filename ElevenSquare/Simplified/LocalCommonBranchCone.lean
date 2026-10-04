import ElevenSquare.Simplified.LocalCommonCone

/-! The finite branch inventory supplies each common row. The corner contact
(4,5), occupying source positions28and29, is not needed. Every owner option at
the five parallel contacts is retained through the convexity theorem. -/
namespace ElevenSquare.Simplified.LocalCommon
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T06
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def fixedPosition : Fin 30 → Fin 42 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 30, 31]
private def fixedIndex (j : Fin 30) : Fin 40 := ⟨j.val,by omega⟩

private theorem branch_fixed : ∀ (b : Fin 128) (j : Fin 30),
    branchRows b (fixedPosition j)=rowIndex (fixedIndex j) := by decide

private theorem fixed_curvature : ∀ j : Fin 30,
    rowCurvatures (rowIndex (fixedIndex j))=curvatureQ (fixedIndex j) := by decide +kernel

private def firstPosition : Fin 5 → Fin 42 := ![32,34,36,38,40]
private def secondPosition : Fin 5 → Fin 42 := ![33,35,37,39,41]
private def firstA : Fin 5 → Fin 56 := ![32,34,36,38,40]
private def secondA : Fin 5 → Fin 56 := ![33,35,37,39,41]
private def firstB : Fin 5 → Fin 56 := ![52,54,50,48,46]
private def secondB : Fin 5 → Fin 56 := ![53,55,51,49,47]

private theorem branch_options : ∀ (b : Fin 128) (g : Fin 5),
    (branchRows b (firstPosition g)=firstA g ∧
      branchRows b (secondPosition g)=secondA g) ∨
    (branchRows b (firstPosition g)=firstB g ∧
      branchRows b (secondPosition g)=secondB g) := by decide

/-- The thirty rows independent of the parallel-contact owner choice. -/
private theorem common_fixed_lower (j : Fin 30) (b : Fin 128) (τ : ℝ)
    (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ (fixedIndex j) : ℝ)/2) ≤
      dot (polynomialGradient (rowIndex (fixedIndex j))) h := by
  have hj := hrows (fixedPosition j)
  rw [branch_fixed b j, fixed_curvature j] at hj
  exact hj

private def parallelIndex (j : Fin 10) : Fin 40 := ⟨30 + j.val, by omega⟩
private def parallelGroup (j : Fin 10) : Fin 5 := ⟨j.val / 2, by omega⟩
private def parallelCombo (j : Fin 10) (s : Fin 2) : Fin 20 :=
  ⟨2 * j.val + s.val, by omega⟩

/-- Each parallel contact contributes two common rows. Each of those rows
has one convex certificate for each of the two possible owners. -/
private theorem parallel_wiring : ∀ (j : Fin 10) (s : Fin 2),
    comboFirst (parallelCombo j s) =
      (if s = 0 then firstA (parallelGroup j) else firstB (parallelGroup j)) ∧
    comboSecond (parallelCombo j s) =
      (if s = 0 then secondA (parallelGroup j) else secondB (parallelGroup j)) ∧
    comboTarget (parallelCombo j s) = rowIndex (parallelIndex j) ∧
    comboCurvature (parallelCombo j s) = curvatureQ (parallelIndex j) := by
  decide +kernel

private theorem common_parallel_lower (j : Fin 10) (b : Fin 128) (τ : ℝ)
    (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ (parallelIndex j) : ℝ)/2) ≤
      dot (polynomialGradient (rowIndex (parallelIndex j))) h := by
  rcases branch_options b (parallelGroup j) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hc := combo_lower (parallelCombo j 0) τ h
    rcases parallel_wiring j 0 with ⟨hf, hs, ht, hk⟩
    rw [hf, hs, ht, hk] at hc
    simp only [if_true] at hc
    exact hc
      (by simpa only [ha] using hrows (firstPosition (parallelGroup j)))
      (by simpa only [hb] using hrows (secondPosition (parallelGroup j)))
  · have hc := combo_lower (parallelCombo j 1) τ h
    rcases parallel_wiring j 1 with ⟨hf, hs, ht, hk⟩
    rw [hf, hs, ht, hk] at hc
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false] at hc
    exact hc
      (by simpa only [ha] using hrows (firstPosition (parallelGroup j)))
      (by simpa only [hb] using hrows (secondPosition (parallelGroup j)))

/-- Every original branch implies the same forty necessary rows. -/
theorem common_rows (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    ∀ j : Fin 40, -(τ^2*(curvatureQ j : ℝ)/2) ≤
      dot (polynomialGradient (rowIndex j)) h := by
  intro j
  by_cases hj : j.val < 30
  · exact common_fixed_lower ⟨j.val, hj⟩ b τ h hrows
  · let k : Fin 10 := ⟨j.val - 30, by omega⟩
    have hk : parallelIndex k = j := by
      apply Fin.ext
      dsimp [parallelIndex, k]
      omega
    simpa only [hk] using common_parallel_lower k b τ h hrows

end
end ElevenSquare.Simplified.LocalCommon

#print axioms ElevenSquare.Simplified.LocalCommon.common_rows
