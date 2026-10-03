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

private theorem common_lower_00 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 0 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 0)) h := by
  have hj := hrows (fixedPosition 0)
  rw [branch_fixed b 0,fixed_curvature 0] at hj
  exact hj

private theorem common_lower_01 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 1 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 1)) h := by
  have hj := hrows (fixedPosition 1)
  rw [branch_fixed b 1,fixed_curvature 1] at hj
  exact hj

private theorem common_lower_02 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 2 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 2)) h := by
  have hj := hrows (fixedPosition 2)
  rw [branch_fixed b 2,fixed_curvature 2] at hj
  exact hj

private theorem common_lower_03 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 3 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 3)) h := by
  have hj := hrows (fixedPosition 3)
  rw [branch_fixed b 3,fixed_curvature 3] at hj
  exact hj

private theorem common_lower_04 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 4 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 4)) h := by
  have hj := hrows (fixedPosition 4)
  rw [branch_fixed b 4,fixed_curvature 4] at hj
  exact hj

private theorem common_lower_05 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 5 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 5)) h := by
  have hj := hrows (fixedPosition 5)
  rw [branch_fixed b 5,fixed_curvature 5] at hj
  exact hj

private theorem common_lower_06 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 6 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 6)) h := by
  have hj := hrows (fixedPosition 6)
  rw [branch_fixed b 6,fixed_curvature 6] at hj
  exact hj

private theorem common_lower_07 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 7 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 7)) h := by
  have hj := hrows (fixedPosition 7)
  rw [branch_fixed b 7,fixed_curvature 7] at hj
  exact hj

private theorem common_lower_08 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 8 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 8)) h := by
  have hj := hrows (fixedPosition 8)
  rw [branch_fixed b 8,fixed_curvature 8] at hj
  exact hj

private theorem common_lower_09 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 9 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 9)) h := by
  have hj := hrows (fixedPosition 9)
  rw [branch_fixed b 9,fixed_curvature 9] at hj
  exact hj

private theorem common_lower_10 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 10 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 10)) h := by
  have hj := hrows (fixedPosition 10)
  rw [branch_fixed b 10,fixed_curvature 10] at hj
  exact hj

private theorem common_lower_11 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 11 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 11)) h := by
  have hj := hrows (fixedPosition 11)
  rw [branch_fixed b 11,fixed_curvature 11] at hj
  exact hj

private theorem common_lower_12 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 12 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 12)) h := by
  have hj := hrows (fixedPosition 12)
  rw [branch_fixed b 12,fixed_curvature 12] at hj
  exact hj

private theorem common_lower_13 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 13 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 13)) h := by
  have hj := hrows (fixedPosition 13)
  rw [branch_fixed b 13,fixed_curvature 13] at hj
  exact hj

private theorem common_lower_14 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 14 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 14)) h := by
  have hj := hrows (fixedPosition 14)
  rw [branch_fixed b 14,fixed_curvature 14] at hj
  exact hj

private theorem common_lower_15 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 15 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 15)) h := by
  have hj := hrows (fixedPosition 15)
  rw [branch_fixed b 15,fixed_curvature 15] at hj
  exact hj

private theorem common_lower_16 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 16 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 16)) h := by
  have hj := hrows (fixedPosition 16)
  rw [branch_fixed b 16,fixed_curvature 16] at hj
  exact hj

private theorem common_lower_17 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 17 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 17)) h := by
  have hj := hrows (fixedPosition 17)
  rw [branch_fixed b 17,fixed_curvature 17] at hj
  exact hj

private theorem common_lower_18 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 18 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 18)) h := by
  have hj := hrows (fixedPosition 18)
  rw [branch_fixed b 18,fixed_curvature 18] at hj
  exact hj

private theorem common_lower_19 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 19 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 19)) h := by
  have hj := hrows (fixedPosition 19)
  rw [branch_fixed b 19,fixed_curvature 19] at hj
  exact hj

private theorem common_lower_20 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 20 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 20)) h := by
  have hj := hrows (fixedPosition 20)
  rw [branch_fixed b 20,fixed_curvature 20] at hj
  exact hj

private theorem common_lower_21 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 21 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 21)) h := by
  have hj := hrows (fixedPosition 21)
  rw [branch_fixed b 21,fixed_curvature 21] at hj
  exact hj

private theorem common_lower_22 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 22 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 22)) h := by
  have hj := hrows (fixedPosition 22)
  rw [branch_fixed b 22,fixed_curvature 22] at hj
  exact hj

private theorem common_lower_23 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 23 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 23)) h := by
  have hj := hrows (fixedPosition 23)
  rw [branch_fixed b 23,fixed_curvature 23] at hj
  exact hj

private theorem common_lower_24 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 24 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 24)) h := by
  have hj := hrows (fixedPosition 24)
  rw [branch_fixed b 24,fixed_curvature 24] at hj
  exact hj

private theorem common_lower_25 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 25 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 25)) h := by
  have hj := hrows (fixedPosition 25)
  rw [branch_fixed b 25,fixed_curvature 25] at hj
  exact hj

private theorem common_lower_26 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 26 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 26)) h := by
  have hj := hrows (fixedPosition 26)
  rw [branch_fixed b 26,fixed_curvature 26] at hj
  exact hj

private theorem common_lower_27 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 27 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 27)) h := by
  have hj := hrows (fixedPosition 27)
  rw [branch_fixed b 27,fixed_curvature 27] at hj
  exact hj

private theorem common_lower_28 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 28 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 28)) h := by
  have hj := hrows (fixedPosition 28)
  rw [branch_fixed b 28,fixed_curvature 28] at hj
  exact hj

private theorem common_lower_29 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 29 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 29)) h := by
  have hj := hrows (fixedPosition 29)
  rw [branch_fixed b 29,fixed_curvature 29] at hj
  exact hj

private theorem common_lower_30 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 30 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 30)) h := by
  rcases branch_options b 0 with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have h0 := hrows (firstPosition 0)
    have h1 := hrows (secondPosition 0)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 0 τ h h0 h1
  · have h0 := hrows (firstPosition 0)
    have h1 := hrows (secondPosition 0)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 1 τ h h0 h1

private theorem common_lower_31 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 31 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 31)) h := by
  rcases branch_options b 0 with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have h0 := hrows (firstPosition 0)
    have h1 := hrows (secondPosition 0)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 2 τ h h0 h1
  · have h0 := hrows (firstPosition 0)
    have h1 := hrows (secondPosition 0)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 3 τ h h0 h1

private theorem common_lower_32 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 32 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 32)) h := by
  rcases branch_options b 1 with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have h0 := hrows (firstPosition 1)
    have h1 := hrows (secondPosition 1)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 4 τ h h0 h1
  · have h0 := hrows (firstPosition 1)
    have h1 := hrows (secondPosition 1)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 5 τ h h0 h1

private theorem common_lower_33 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 33 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 33)) h := by
  rcases branch_options b 1 with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have h0 := hrows (firstPosition 1)
    have h1 := hrows (secondPosition 1)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 6 τ h h0 h1
  · have h0 := hrows (firstPosition 1)
    have h1 := hrows (secondPosition 1)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 7 τ h h0 h1

private theorem common_lower_34 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 34 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 34)) h := by
  rcases branch_options b 2 with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have h0 := hrows (firstPosition 2)
    have h1 := hrows (secondPosition 2)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 8 τ h h0 h1
  · have h0 := hrows (firstPosition 2)
    have h1 := hrows (secondPosition 2)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 9 τ h h0 h1

private theorem common_lower_35 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 35 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 35)) h := by
  rcases branch_options b 2 with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have h0 := hrows (firstPosition 2)
    have h1 := hrows (secondPosition 2)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 10 τ h h0 h1
  · have h0 := hrows (firstPosition 2)
    have h1 := hrows (secondPosition 2)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 11 τ h h0 h1

private theorem common_lower_36 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 36 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 36)) h := by
  rcases branch_options b 3 with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have h0 := hrows (firstPosition 3)
    have h1 := hrows (secondPosition 3)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 12 τ h h0 h1
  · have h0 := hrows (firstPosition 3)
    have h1 := hrows (secondPosition 3)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 13 τ h h0 h1

private theorem common_lower_37 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 37 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 37)) h := by
  rcases branch_options b 3 with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have h0 := hrows (firstPosition 3)
    have h1 := hrows (secondPosition 3)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 14 τ h h0 h1
  · have h0 := hrows (firstPosition 3)
    have h1 := hrows (secondPosition 3)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 15 τ h h0 h1

private theorem common_lower_38 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 38 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 38)) h := by
  rcases branch_options b 4 with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have h0 := hrows (firstPosition 4)
    have h1 := hrows (secondPosition 4)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 16 τ h h0 h1
  · have h0 := hrows (firstPosition 4)
    have h1 := hrows (secondPosition 4)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 17 τ h h0 h1

private theorem common_lower_39 (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    -(τ^2*(curvatureQ 39 : ℝ)/2) ≤ dot (polynomialGradient (rowIndex 39)) h := by
  rcases branch_options b 4 with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have h0 := hrows (firstPosition 4)
    have h1 := hrows (secondPosition 4)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 18 τ h h0 h1
  · have h0 := hrows (firstPosition 4)
    have h1 := hrows (secondPosition 4)
    rw [ha] at h0
    rw [hb] at h1
    exact combo_lower 19 τ h h0 h1

/-- Every original branch implies the same forty necessary rows. -/
theorem common_rows (b : Fin 128) (τ : ℝ) (h : Fin 33 → ℝ)
    (hrows : ∀ i : Fin 42, -(τ^2*(rowCurvatures (branchRows b i) : ℝ)/2) ≤
      dot (polynomialGradient (branchRows b i)) h) :
    ∀ j : Fin 40, -(τ^2*(curvatureQ j : ℝ)/2) ≤
      dot (polynomialGradient (rowIndex j)) h := by
  intro j
  fin_cases j
  · exact common_lower_00 b τ h hrows
  · exact common_lower_01 b τ h hrows
  · exact common_lower_02 b τ h hrows
  · exact common_lower_03 b τ h hrows
  · exact common_lower_04 b τ h hrows
  · exact common_lower_05 b τ h hrows
  · exact common_lower_06 b τ h hrows
  · exact common_lower_07 b τ h hrows
  · exact common_lower_08 b τ h hrows
  · exact common_lower_09 b τ h hrows
  · exact common_lower_10 b τ h hrows
  · exact common_lower_11 b τ h hrows
  · exact common_lower_12 b τ h hrows
  · exact common_lower_13 b τ h hrows
  · exact common_lower_14 b τ h hrows
  · exact common_lower_15 b τ h hrows
  · exact common_lower_16 b τ h hrows
  · exact common_lower_17 b τ h hrows
  · exact common_lower_18 b τ h hrows
  · exact common_lower_19 b τ h hrows
  · exact common_lower_20 b τ h hrows
  · exact common_lower_21 b τ h hrows
  · exact common_lower_22 b τ h hrows
  · exact common_lower_23 b τ h hrows
  · exact common_lower_24 b τ h hrows
  · exact common_lower_25 b τ h hrows
  · exact common_lower_26 b τ h hrows
  · exact common_lower_27 b τ h hrows
  · exact common_lower_28 b τ h hrows
  · exact common_lower_29 b τ h hrows
  · exact common_lower_30 b τ h hrows
  · exact common_lower_31 b τ h hrows
  · exact common_lower_32 b τ h hrows
  · exact common_lower_33 b τ h hrows
  · exact common_lower_34 b τ h hrows
  · exact common_lower_35 b τ h hrows
  · exact common_lower_36 b τ h hrows
  · exact common_lower_37 b τ h hrows
  · exact common_lower_38 b τ h hrows
  · exact common_lower_39 b τ h hrows


end
end ElevenSquare.Simplified.LocalCommon

#print axioms ElevenSquare.Simplified.LocalCommon.common_rows
