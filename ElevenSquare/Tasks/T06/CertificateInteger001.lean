import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.DataDual001
import ElevenSquare.Tasks.T06.RoundedGradientLiterals
import ElevenSquare.Tasks.T06.RecursiveCertificate
import ElevenSquare.Tasks.T06.SparseColumn00
import ElevenSquare.Tasks.T06.SparseColumn01
import ElevenSquare.Tasks.T06.SparseColumn02
import ElevenSquare.Tasks.T06.SparseColumn03
import ElevenSquare.Tasks.T06.SparseColumn04
import ElevenSquare.Tasks.T06.SparseColumn05
import ElevenSquare.Tasks.T06.SparseColumn06
import ElevenSquare.Tasks.T06.SparseColumn07
import ElevenSquare.Tasks.T06.SparseColumn08
import ElevenSquare.Tasks.T06.SparseColumn09
import ElevenSquare.Tasks.T06.SparseColumn10
import ElevenSquare.Tasks.T06.SparseColumn11
import ElevenSquare.Tasks.T06.SparseColumn12
import ElevenSquare.Tasks.T06.SparseColumn13
import ElevenSquare.Tasks.T06.SparseColumn15
import ElevenSquare.Tasks.T06.SparseColumn16
import ElevenSquare.Tasks.T06.SparseColumn18
import ElevenSquare.Tasks.T06.SparseColumn19
import ElevenSquare.Tasks.T06.SparseColumn20
import ElevenSquare.Tasks.T06.SparseColumn21
import ElevenSquare.Tasks.T06.SparseColumn22
import ElevenSquare.Tasks.T06.SparseColumn23
import ElevenSquare.Tasks.T06.SparseColumn24
import ElevenSquare.Tasks.T06.SparseColumn25
import ElevenSquare.Tasks.T06.SparseColumn26
import ElevenSquare.Tasks.T06.SparseColumn27
import ElevenSquare.Tasks.T06.SparseColumn28
import ElevenSquare.Tasks.T06.SparseColumn29
import ElevenSquare.Tasks.T06.SparseColumn30
import ElevenSquare.Tasks.T06.SparseColumn31
import ElevenSquare.Tasks.T06.SparseColumn32
import ElevenSquare.Tasks.T06.SparseColumn33
import ElevenSquare.Tasks.T06.SparseColumn34

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix001 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral28, roundedGradientLiteral42, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix001_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = branchIntegerMatrix001 := by
  change roundedGradients ∘ branchRows 1 = branchIntegerMatrix001
  rw [show branchRows 1 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral28_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral42_eq, branchIntegerMatrix001]

theorem branchColumn001_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 0) i) = _
  rw [branchColumn001_0]
  exact sparseColumn00_sum n

theorem branchColumn001_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 1) i) = _
  rw [branchColumn001_1]
  exact sparseColumn01_sum n

theorem branchColumn001_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 2) i) = _
  rw [branchColumn001_2]
  exact sparseColumn02_sum n

theorem branchColumn001_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 3) i) = _
  rw [branchColumn001_3]
  exact sparseColumn03_sum n

theorem branchColumn001_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 4) i) = _
  rw [branchColumn001_4]
  exact sparseColumn04_sum n

theorem branchColumn001_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 5) i) = _
  rw [branchColumn001_5]
  exact sparseColumn05_sum n

theorem branchColumn001_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 6) i) = _
  rw [branchColumn001_6]
  exact sparseColumn06_sum n

theorem branchColumn001_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 7) i) = _
  rw [branchColumn001_7]
  exact sparseColumn07_sum n

theorem branchColumn001_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 8) i) = _
  rw [branchColumn001_8]
  exact sparseColumn08_sum n

theorem branchColumn001_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 9) i) = _
  rw [branchColumn001_9]
  exact sparseColumn09_sum n

theorem branchColumn001_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 10) i) = _
  rw [branchColumn001_10]
  exact sparseColumn10_sum n

theorem branchColumn001_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 11) i) = _
  rw [branchColumn001_11]
  exact sparseColumn11_sum n

theorem branchColumn001_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 12) = sparseColumn12 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 12) = sparseDot12 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 12) i) = _
  rw [branchColumn001_12]
  exact sparseColumn12_sum n

theorem branchColumn001_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 13) = sparseColumn13 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 13) = sparseDot13 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 13) i) = _
  rw [branchColumn001_13]
  exact sparseColumn13_sum n

theorem branchColumn001_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 14) = sparseColumn33 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 14) = sparseDot33 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 14) i) = _
  rw [branchColumn001_14]
  exact sparseColumn33_sum n

theorem branchColumn001_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 15) = sparseColumn15 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 15) = sparseDot15 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 15) i) = _
  rw [branchColumn001_15]
  exact sparseColumn15_sum n

theorem branchColumn001_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 16) = sparseColumn16 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 16) = sparseDot16 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 16) i) = _
  rw [branchColumn001_16]
  exact sparseColumn16_sum n

theorem branchColumn001_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 17) = sparseColumn34 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 17) = sparseDot34 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 17) i) = _
  rw [branchColumn001_17]
  exact sparseColumn34_sum n

theorem branchColumn001_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 18) i) = _
  rw [branchColumn001_18]
  exact sparseColumn18_sum n

theorem branchColumn001_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 19) i) = _
  rw [branchColumn001_19]
  exact sparseColumn19_sum n

theorem branchColumn001_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 20) = sparseColumn20 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 20) = sparseDot20 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 20) i) = _
  rw [branchColumn001_20]
  exact sparseColumn20_sum n

theorem branchColumn001_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 21) i) = _
  rw [branchColumn001_21]
  exact sparseColumn21_sum n

theorem branchColumn001_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 22) i) = _
  rw [branchColumn001_22]
  exact sparseColumn22_sum n

theorem branchColumn001_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 23) = sparseColumn23 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 23) = sparseDot23 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 23) i) = _
  rw [branchColumn001_23]
  exact sparseColumn23_sum n

theorem branchColumn001_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 24) i) = _
  rw [branchColumn001_24]
  exact sparseColumn24_sum n

theorem branchColumn001_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 25) i) = _
  rw [branchColumn001_25]
  exact sparseColumn25_sum n

theorem branchColumn001_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 26) = sparseColumn26 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 26) = sparseDot26 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 26) i) = _
  rw [branchColumn001_26]
  exact sparseColumn26_sum n

theorem branchColumn001_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 27) i) = _
  rw [branchColumn001_27]
  exact sparseColumn27_sum n

theorem branchColumn001_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 28) i) = _
  rw [branchColumn001_28]
  exact sparseColumn28_sum n

theorem branchColumn001_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 29) = sparseColumn29 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 29) = sparseDot29 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 29) i) = _
  rw [branchColumn001_29]
  exact sparseColumn29_sum n

theorem branchColumn001_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 30) i) = _
  rw [branchColumn001_30]
  exact sparseColumn30_sum n

theorem branchColumn001_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 31) i) = _
  rw [branchColumn001_31]
  exact sparseColumn31_sum n

theorem branchColumn001_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 1 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 1 i)) = _
  rw [branchIntegerMatrix001_eq]
  simp only [branchIntegerMatrix001, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot001_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 1 i) 32) i) = _
  rw [branchColumn001_32]
  exact sparseColumn32_sum n

def branchSparseDots001 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot12, sparseDot13, sparseDot33, sparseDot15, sparseDot16, sparseDot34, sparseDot18, sparseDot19, sparseDot20, sparseDot21, sparseDot22, sparseDot23, sparseDot24, sparseDot25, sparseDot26, sparseDot27, sparseDot28, sparseDot29, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot001_0 :
    branchSparseDots001 0 = sparseDot00 := rfl

private theorem branchSparseDot001_1 :
    branchSparseDots001 1 = sparseDot01 := rfl

private theorem branchSparseDot001_2 :
    branchSparseDots001 2 = sparseDot02 := rfl

private theorem branchSparseDot001_3 :
    branchSparseDots001 3 = sparseDot03 := rfl

private theorem branchSparseDot001_4 :
    branchSparseDots001 4 = sparseDot04 := rfl

private theorem branchSparseDot001_5 :
    branchSparseDots001 5 = sparseDot05 := rfl

private theorem branchSparseDot001_6 :
    branchSparseDots001 6 = sparseDot06 := rfl

private theorem branchSparseDot001_7 :
    branchSparseDots001 7 = sparseDot07 := rfl

private theorem branchSparseDot001_8 :
    branchSparseDots001 8 = sparseDot08 := rfl

private theorem branchSparseDot001_9 :
    branchSparseDots001 9 = sparseDot09 := rfl

private theorem branchSparseDot001_10 :
    branchSparseDots001 10 = sparseDot10 := rfl

private theorem branchSparseDot001_11 :
    branchSparseDots001 11 = sparseDot11 := rfl

private theorem branchSparseDot001_12 :
    branchSparseDots001 12 = sparseDot12 := rfl

private theorem branchSparseDot001_13 :
    branchSparseDots001 13 = sparseDot13 := rfl

private theorem branchSparseDot001_14 :
    branchSparseDots001 14 = sparseDot33 := rfl

private theorem branchSparseDot001_15 :
    branchSparseDots001 15 = sparseDot15 := rfl

private theorem branchSparseDot001_16 :
    branchSparseDots001 16 = sparseDot16 := rfl

private theorem branchSparseDot001_17 :
    branchSparseDots001 17 = sparseDot34 := rfl

private theorem branchSparseDot001_18 :
    branchSparseDots001 18 = sparseDot18 := rfl

private theorem branchSparseDot001_19 :
    branchSparseDots001 19 = sparseDot19 := rfl

private theorem branchSparseDot001_20 :
    branchSparseDots001 20 = sparseDot20 := rfl

private theorem branchSparseDot001_21 :
    branchSparseDots001 21 = sparseDot21 := rfl

private theorem branchSparseDot001_22 :
    branchSparseDots001 22 = sparseDot22 := rfl

private theorem branchSparseDot001_23 :
    branchSparseDots001 23 = sparseDot23 := rfl

private theorem branchSparseDot001_24 :
    branchSparseDots001 24 = sparseDot24 := rfl

private theorem branchSparseDot001_25 :
    branchSparseDots001 25 = sparseDot25 := rfl

private theorem branchSparseDot001_26 :
    branchSparseDots001 26 = sparseDot26 := rfl

private theorem branchSparseDot001_27 :
    branchSparseDots001 27 = sparseDot27 := rfl

private theorem branchSparseDot001_28 :
    branchSparseDots001 28 = sparseDot28 := rfl

private theorem branchSparseDot001_29 :
    branchSparseDots001 29 = sparseDot29 := rfl

private theorem branchSparseDot001_30 :
    branchSparseDots001 30 = sparseDot30 := rfl

private theorem branchSparseDot001_31 :
    branchSparseDots001 31 = sparseDot31 := rfl

private theorem branchSparseDot001_32 :
    branchSparseDots001 32 = sparseDot32 := rfl

theorem branchDots001 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 1 i) k) = branchSparseDots001 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot001_0 n
      _ = _ := congrFun branchSparseDot001_0.symm n
  · calc
      _ = sparseDot01 n := branchDot001_1 n
      _ = _ := congrFun branchSparseDot001_1.symm n
  · calc
      _ = sparseDot02 n := branchDot001_2 n
      _ = _ := congrFun branchSparseDot001_2.symm n
  · calc
      _ = sparseDot03 n := branchDot001_3 n
      _ = _ := congrFun branchSparseDot001_3.symm n
  · calc
      _ = sparseDot04 n := branchDot001_4 n
      _ = _ := congrFun branchSparseDot001_4.symm n
  · calc
      _ = sparseDot05 n := branchDot001_5 n
      _ = _ := congrFun branchSparseDot001_5.symm n
  · calc
      _ = sparseDot06 n := branchDot001_6 n
      _ = _ := congrFun branchSparseDot001_6.symm n
  · calc
      _ = sparseDot07 n := branchDot001_7 n
      _ = _ := congrFun branchSparseDot001_7.symm n
  · calc
      _ = sparseDot08 n := branchDot001_8 n
      _ = _ := congrFun branchSparseDot001_8.symm n
  · calc
      _ = sparseDot09 n := branchDot001_9 n
      _ = _ := congrFun branchSparseDot001_9.symm n
  · calc
      _ = sparseDot10 n := branchDot001_10 n
      _ = _ := congrFun branchSparseDot001_10.symm n
  · calc
      _ = sparseDot11 n := branchDot001_11 n
      _ = _ := congrFun branchSparseDot001_11.symm n
  · calc
      _ = sparseDot12 n := branchDot001_12 n
      _ = _ := congrFun branchSparseDot001_12.symm n
  · calc
      _ = sparseDot13 n := branchDot001_13 n
      _ = _ := congrFun branchSparseDot001_13.symm n
  · calc
      _ = sparseDot33 n := branchDot001_14 n
      _ = _ := congrFun branchSparseDot001_14.symm n
  · calc
      _ = sparseDot15 n := branchDot001_15 n
      _ = _ := congrFun branchSparseDot001_15.symm n
  · calc
      _ = sparseDot16 n := branchDot001_16 n
      _ = _ := congrFun branchSparseDot001_16.symm n
  · calc
      _ = sparseDot34 n := branchDot001_17 n
      _ = _ := congrFun branchSparseDot001_17.symm n
  · calc
      _ = sparseDot18 n := branchDot001_18 n
      _ = _ := congrFun branchSparseDot001_18.symm n
  · calc
      _ = sparseDot19 n := branchDot001_19 n
      _ = _ := congrFun branchSparseDot001_19.symm n
  · calc
      _ = sparseDot20 n := branchDot001_20 n
      _ = _ := congrFun branchSparseDot001_20.symm n
  · calc
      _ = sparseDot21 n := branchDot001_21 n
      _ = _ := congrFun branchSparseDot001_21.symm n
  · calc
      _ = sparseDot22 n := branchDot001_22 n
      _ = _ := congrFun branchSparseDot001_22.symm n
  · calc
      _ = sparseDot23 n := branchDot001_23 n
      _ = _ := congrFun branchSparseDot001_23.symm n
  · calc
      _ = sparseDot24 n := branchDot001_24 n
      _ = _ := congrFun branchSparseDot001_24.symm n
  · calc
      _ = sparseDot25 n := branchDot001_25 n
      _ = _ := congrFun branchSparseDot001_25.symm n
  · calc
      _ = sparseDot26 n := branchDot001_26 n
      _ = _ := congrFun branchSparseDot001_26.symm n
  · calc
      _ = sparseDot27 n := branchDot001_27 n
      _ = _ := congrFun branchSparseDot001_27.symm n
  · calc
      _ = sparseDot28 n := branchDot001_28 n
      _ = _ := congrFun branchSparseDot001_28.symm n
  · calc
      _ = sparseDot29 n := branchDot001_29 n
      _ = _ := congrFun branchSparseDot001_29.symm n
  · calc
      _ = sparseDot30 n := branchDot001_30 n
      _ = _ := congrFun branchSparseDot001_30.symm n
  · calc
      _ = sparseDot31 n := branchDot001_31 n
      _ = _ := congrFun branchSparseDot001_31.symm n
  · calc
      _ = sparseDot32 n := branchDot001_32 n
      _ = _ := congrFun branchSparseDot001_32.symm n

def branchIntegerCurvature001 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101981296, 101981296, 44932602, 44932602, 115699695, 115699695, 48290998, 48290998, 204734428, 204734428]

theorem branchIntegerCurvature001_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 1 i)) = branchIntegerCurvature001 := by
  change curvatureNumerators ∘ branchRows 1 = branchIntegerCurvature001
  rw [show branchRows 1 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature001_entry (i : Fin 42) :
    curvatureNumerators (branchRows 1 i) = branchIntegerCurvature001 i :=
  congrFun branchIntegerCurvature001_eq i

theorem integerCheck001_0_0 :
    integerResidualCheck 1 0 0 (dualNumerators001 0 0) ∧
    integerMassCheck 1 0 0 (dualNumerators001 0 0) := by
  have hn : dualNumerators001 0 0 = ![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1011030237961, 258120108700, 0, 1660206247774, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 298609637458, 1874436686609, 0, 1308901425339, 1536582908426, 298609637459, 1741178091979, 225835502005, 1430871029972, 404321515913] := rfl
  have he : residualNumerators 1 0 0 = 1299282634834126 := rfl
  have hr : radiusNumerators 0 = 18767167 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_0_1 :
    integerResidualCheck 1 0 1 (dualNumerators001 0 1) ∧
    integerMassCheck 1 0 1 (dualNumerators001 0 1) := by
  have hn : dualNumerators001 0 1 = ![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 1 0 1 = 33000000000000 := rfl
  have hr : radiusNumerators 0 = 18767167 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_1_0 :
    integerResidualCheck 1 1 0 (dualNumerators001 1 0) ∧
    integerMassCheck 1 1 0 (dualNumerators001 1 0) := by
  have hn : dualNumerators001 1 0 = ![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1197158056821, 305639293618, 0, 1965845541389, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 353582830567, 2219515200554, 0, 1549866490727, 1819463493499, 353582830568, 2061724074025, 267411181773, 1694290356000, 478755968067] := rfl
  have he : residualNumerators 1 1 0 = 1546888545653667 := rfl
  have hr : radiusNumerators 1 = 22176635 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_1_1 :
    integerResidualCheck 1 1 1 (dualNumerators001 1 1) ∧
    integerMassCheck 1 1 1 (dualNumerators001 1 1) := by
  have hn : dualNumerators001 1 1 = ![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 1 1 1 = 33000000000000 := rfl
  have hr : radiusNumerators 1 = 22176635 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_2_0 :
    integerResidualCheck 1 2 0 (dualNumerators001 2 0) ∧
    integerMassCheck 1 2 0 (dualNumerators001 2 0) := by
  have hn : dualNumerators001 2 0 = ![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1197158056822, 305639293619, 0, 1965845541391, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 353582830567, 2219515200555, 0, 1549866490728, 1819463493501, 353582830568, 2061724074027, 267411181773, 1694290356001, 478755968068] := rfl
  have he : residualNumerators 1 2 0 = 1582932792409380 := rfl
  have hr : radiusNumerators 2 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_2_1 :
    integerResidualCheck 1 2 1 (dualNumerators001 2 1) ∧
    integerMassCheck 1 2 1 (dualNumerators001 2 1) := by
  have hn : dualNumerators001 2 1 = ![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1011030237961, 258120108700, 0, 1660206247773, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 298609637458, 1874436686608, 0, 1308901425338, 1536582908425, 298609637459, 1741178091978, 225835502005, 1430871029971, 404321515912] := rfl
  have he : residualNumerators 1 2 1 = 1338657849243373 := rfl
  have hr : radiusNumerators 2 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_3_0 :
    integerResidualCheck 1 3 0 (dualNumerators001 3 0) ∧
    integerMassCheck 1 3 0 (dualNumerators001 3 0) := by
  have hn : dualNumerators001 3 0 = ![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 1 3 0 = 33000000000000 := rfl
  have hr : radiusNumerators 3 = 16360330 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_3_1 :
    integerResidualCheck 1 3 1 (dualNumerators001 3 1) ∧
    integerMassCheck 1 3 1 (dualNumerators001 3 1) := by
  have hn : dualNumerators001 3 1 = ![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 796619754801, 203380245200, 0, 1308124173107, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 235283107509, 1476922487191, 0, 1031321016287, 1210717794365, 235283107510, 1371924214149, 177942276579, 1127424369963, 318576531911] := rfl
  have he : residualNumerators 1 3 1 = 1025708242445655 := rfl
  have hr : radiusNumerators 3 = 16360330 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_4_0 :
    integerResidualCheck 1 4 0 (dualNumerators001 4 0) ∧
    integerMassCheck 1 4 0 (dualNumerators001 4 0) := by
  have hn : dualNumerators001 4 0 = ![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 672765518030, 171759757645, 0, 1104743927909, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 198702531230, 1247298370644, 0, 870976665588, 1022481779049, 198702531231, 1158624675158, 150276750182, 952138376845, 269045933435] := rfl
  have he : residualNumerators 1 4 0 = 858561353766622 := rfl
  have hr : radiusNumerators 4 = 13760362 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_4_1 :
    integerResidualCheck 1 4 1 (dualNumerators001 4 1) ∧
    integerMassCheck 1 4 1 (dualNumerators001 4 1) := by
  have hn : dualNumerators001 4 1 = ![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 1 4 1 = 33000000000000 := rfl
  have hr : radiusNumerators 4 = 13760362 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_5_0 :
    integerResidualCheck 1 5 0 (dualNumerators001 5 0) ∧
    integerMassCheck 1 5 0 (dualNumerators001 5 0) := by
  have hn : dualNumerators001 5 0 = ![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 796619754801, 203380245201, 0, 1308124173108, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 235283107509, 1476922487193, 0, 1031321016288, 1210717794366, 235283107510, 1371924214150, 177942276579, 1127424369964, 318576531911] := rfl
  have he : residualNumerators 1 5 0 = 1057574095074272 := rfl
  have hr : radiusNumerators 5 = 17641130 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_5_1 :
    integerResidualCheck 1 5 1 (dualNumerators001 5 1) ∧
    integerMassCheck 1 5 1 (dualNumerators001 5 1) := by
  have hn : dualNumerators001 5 1 = ![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 198702531230, 1247298370643, 0, 870976665588, 1022481779048, 198702531231, 1158624675157, 150276750182, 952138376844, 269045933435] := rfl
  have he : residualNumerators 1 5 1 = 894483746056194 := rfl
  have hr : radiusNumerators 5 = 17641130 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_6_0 :
    integerResidualCheck 1 6 0 (dualNumerators001 6 0) ∧
    integerMassCheck 1 6 0 (dualNumerators001 6 0) := by
  have hn : dualNumerators001 6 0 = ![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 0, 70552396879, 187567711821, 1472638535954, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 1, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 659499318402, 1175693227483, 103906894360, 5439901403, 1430871029972, 404321515913] := rfl
  have he : residualNumerators 1 6 0 = 722596183434246 := rfl
  have hr : radiusNumerators 6 = 8962451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_6_1 :
    integerResidualCheck 1 6 1 (dualNumerators001 6 1) ∧
    integerMassCheck 1 6 1 (dualNumerators001 6 1) := by
  have hn : dualNumerators001 6 1 = ![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949782, 1, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 760187607595, 1097479190627, 0, 0] := rfl
  have he : residualNumerators 1 6 1 = 622101700319854 := rfl
  have hr : radiusNumerators 6 = 8962451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_7_0 :
    integerResidualCheck 1 7 0 (dualNumerators001 7 0) ∧
    integerMassCheck 1 7 0 (dualNumerators001 7 0) := by
  have hn : dualNumerators001 7 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 1 7 0 = 33000000000000 := rfl
  have hr : radiusNumerators 7 = 10424794 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_7_1 :
    integerResidualCheck 1 7 1 (dualNumerators001 7 1) ∧
    integerMassCheck 1 7 1 (dualNumerators001 7 1) := by
  have hn : dualNumerators001 7 1 = ![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 598579028412, 152819646810, 0, 982922770697, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675220, 1, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 176791415284, 1109757600279, 0, 774933245365, 909731746751, 176791415285, 1030862037014, 133705590887, 847145178002, 239377984034] := rfl
  have he : residualNumerators 1 7 1 = 761034410772082 := rfl
  have hr : radiusNumerators 7 = 10424794 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_8_0 :
    integerResidualCheck 1 8 0 (dualNumerators001 8 0) ∧
    integerMassCheck 1 8 0 (dualNumerators001 8 0) := by
  have hn : dualNumerators001 8 0 = ![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1197158056823, 305639293619, 0, 1965845541393, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350440, 2, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 353582830567, 2219515200557, 0, 1549866490730, 1819463493502, 353582830569, 2061724074028, 267411181773, 1694290356003, 478755968068] := rfl
  have he : residualNumerators 1 8 0 = 1574681711323471 := rfl
  have hr : radiusNumerators 8 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_8_1 :
    integerResidualCheck 1 8 1 (dualNumerators001 8 1) ∧
    integerMassCheck 1 8 1 (dualNumerators001 8 1) := by
  have hn : dualNumerators001 8 1 = ![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 252183386393, 1583009159490, 0, 1105400337063, 1297683104332, 252183386394, 1470468908124, 190723789588, 1208406751039, 341459739686] := rfl
  have he : residualNumerators 1 8 1 = 1128234752178627 := rfl
  have hr : radiusNumerators 8 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_9_0 :
    integerResidualCheck 1 9 0 (dualNumerators001 9 0) ∧
    integerMassCheck 1 9 0 (dualNumerators001 9 0) := by
  have hn : dualNumerators001 9 0 = ![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 887477428322, 296619754801, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 703380245200, 296619754801, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 235283107509, 1476922487191, 0, 1031321016287, 1210717794365, 235283107510, 1371924214149, 177942276579, 1127424369963, 318576531911] := rfl
  have he : residualNumerators 1 9 0 = 1027366425084007 := rfl
  have hr : radiusNumerators 9 = 16350530 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_9_1 :
    integerResidualCheck 1 9 1 (dualNumerators001 9 1) ∧
    integerMassCheck 1 9 1 (dualNumerators001 9 1) := by
  have hn : dualNumerators001 9 1 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 1 9 1 = 33000000000000 := rfl
  have hr : radiusNumerators 9 = 16350530 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_10_0 :
    integerResidualCheck 1 10 0 (dualNumerators001 10 0) ∧
    integerMassCheck 1 10 0 (dualNumerators001 10 0) := by
  have hn : dualNumerators001 10 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 1 10 0 = 33000000000000 := rfl
  have hr : radiusNumerators 10 = 10683139 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_10_1 :
    integerResidualCheck 1 10 1 (dualNumerators001 10 1) ∧
    integerMassCheck 1 10 1 (dualNumerators001 10 1) := by
  have hn : dualNumerators001 10 1 = ![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 560661867464, 344525275673, 0, 844525275674, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 419928145920, 344525275674, 155474724327, 844525275674, 0, 0, 1184800741849, 1308901425339, 179862976578, 1129038448761, 0, 788396879662, 925537360486, 179862976579, 1048772159673, 136028582177, 861863417206, 243536919859] := rfl
  have he : residualNumerators 1 10 1 = 778095390264368 := rfl
  have hr : radiusNumerators 10 = 10683139 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_11_0 :
    integerResidualCheck 1 11 0 (dualNumerators001 11 0) ∧
    integerMassCheck 1 11 0 (dualNumerators001 11 0) := by
  have hn : dualNumerators001 11 0 = ![301584229951, 55520807208, 301584229951, 0, 1, 453219981703, 536656503669, 0, 422847068578, 301584229950, 0, 453219981704, 546780018297, 0, 582744499174, 0, 0, 500692022794, 1015715082378, 857797059952, 467415292132, 702430462570, 467415292132, 553465130761, 453219981704, 0, 0, 546780018297, 0, 46087995504, 702430462570, 776005788302, 106635005680, 669370782622, 0, 467415292132, 548721496610, 106635005681, 621783467235, 80646995335, 510971252327, 144385249964] := rfl
  have he : residualNumerators 1 11 0 = 481460482234886 := rfl
  have hr : radiusNumerators 11 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_11_1 :
    integerResidualCheck 1 11 1 (dualNumerators001 11 1) ∧
    integerMassCheck 1 11 1 (dualNumerators001 11 1) := by
  have hn : dualNumerators001 11 1 = ![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 101936936604, 639879996233, 0, 446822154676, 524546213099, 101936936605, 594389257794, 77093892371, 488459149252, 138024000452] := rfl
  have he : residualNumerators 1 11 1 = 467045895818018 := rfl
  have hr : radiusNumerators 11 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_12_0 :
    integerResidualCheck 1 12 0 (dualNumerators001 12 0) ∧
    integerMassCheck 1 12 0 (dualNumerators001 12 0) := by
  have hn : dualNumerators001 12 0 = ![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 235283107509, 1476922487191, 0, 1031321016287, 1210717794365, 235283107510, 1371924214149, 177942276579, 1127424369963, 318576531911] := rfl
  have he : residualNumerators 1 12 0 = 991208242445655 := rfl
  have hr : radiusNumerators 12 = 16348076 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_12_1 :
    integerResidualCheck 1 12 1 (dualNumerators001 12 1) ∧
    integerMassCheck 1 12 1 (dualNumerators001 12 1) := by
  have hn : dualNumerators001 12 1 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 1 12 1 = 66000000000000 := rfl
  have hr : radiusNumerators 12 = 16348076 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_13_0 :
    integerResidualCheck 1 13 0 (dualNumerators001 13 0) ∧
    integerMassCheck 1 13 0 (dualNumerators001 13 0) := by
  have hn : dualNumerators001 13 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 1 13 0 = 33000000000000 := rfl
  have hr : radiusNumerators 13 = 13962901 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_13_1 :
    integerResidualCheck 1 13 1 (dualNumerators001 13 1) ∧
    integerMassCheck 1 13 1 (dualNumerators001 13 1) := by
  have hn : dualNumerators001 13 1 = ![271504920046, 49983290985, 271504920046, 0, 1, 408016874475, 483131631732, 0, 380673285087, 271504920045, 408016874475, 0, 0, 16868368268, 0, 0, 450754164561, 0, 914410021623, 772242375590, 420796377646, 632371681400, 420796377646, 498263805438, 408016874475, 0, 0, 16868368268, 500000000001, 16868368269, 632371681400, 698608775208, 95999478143, 602609297066, 0, 420796377646, 493993290328, 95999478143, 559768229874, 72603451527, 460008167640, 129984600832] := rfl
  have he : residualNumerators 1 13 1 = 410049781031792 := rfl
  have hr : radiusNumerators 13 = 13962901 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_14_0 :
    integerResidualCheck 1 14 0 (dualNumerators001 14 0) ∧
    integerMassCheck 1 14 0 (dualNumerators001 14 0) := by
  have hn : dualNumerators001 14 0 = ![288297190339, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 0, 433252253780, 0, 0, 1079760519503, 0, 478632796615, 1, 970965240730, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253780, 0, 0, 566747746222, 0, 671483150164, 741816932837, 101936936605, 639879996233, 0, 446822154676, 524546213099, 101936936605, 594389257794, 77093892371, 488459149252, 138024000452] := rfl
  have he : residualNumerators 1 14 0 = 468403908326087 := rfl
  have hr : radiusNumerators 14 = 20161291 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_14_1 :
    integerResidualCheck 1 14 1 (dualNumerators001 14 1) ∧
    integerMassCheck 1 14 1 (dualNumerators001 14 1) := by
  have hn : dualNumerators001 14 1 = ![362006560060, 66644387979, 362006560061, 0, 1, 544022499300, 644175508976, 0, 507564380116, 362006560060, 544022499300, 0, 0, 355824491024, 0, 1000000000000, 601005552747, 0, 1219213362163, 1029656500786, 561061836861, 843162241867, 561061836861, 664351740584, 544022499300, 0, 0, 355824491024, 0, 355824491025, 843162241867, 931478366944, 127999304190, 803479062754, 0, 561061836861, 658657720437, 127999304191, 746357639831, 96804602036, 613344223519, 173312801109] := rfl
  have he : residualNumerators 1 14 1 = 578515681399151 := rfl
  have hr : radiusNumerators 14 = 20161291 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_15_0 :
    integerResidualCheck 1 15 0 (dualNumerators001 15 0) ∧
    integerMassCheck 1 15 0 (dualNumerators001 15 0) := by
  have hn : dualNumerators001 15 0 = ![602334801077, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546385, 0, 844525275675, 602334801077, 221089960014, 684097183123, 0, 1184097183122, 1071829546385, 0, 0, 0, 2028622458796, 1713222941252, 933538524389, 1402919220983, 933538524389, 1105400337064, 905187143136, 0, 684097183123, 500000000000, 0, 0, 1402919220983, 1549866490727, 212975243914, 1336891246814, 0, 933538524389, 1095926181425, 212975243915, 1241848160005, 161071060979, 1020530044549, 288371380791] := rfl
  have he : residualNumerators 1 15 0 = 926154509129459 := rfl
  have hr : radiusNumerators 15 = 12900283 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_15_1 :
    integerResidualCheck 1 15 1 (dualNumerators001 15 1) ∧
    integerMassCheck 1 15 1 (dualNumerators001 15 1) := by
  have hn : dualNumerators001 15 1 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 1 15 1 = 33000000000000 := rfl
  have hr : radiusNumerators 15 = 12900283 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_16_0 :
    integerResidualCheck 1 16 0 (dualNumerators001 16 0) ∧
    integerMassCheck 1 16 0 (dualNumerators001 16 0) := by
  have hn : dualNumerators001 16 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 1 16 0 = 66000000000000 := rfl
  have hr : radiusNumerators 16 = 10683060 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_16_1 :
    integerResidualCheck 1 16 1 (dualNumerators001 16 1) ∧
    integerMassCheck 1 16 1 (dualNumerators001 16 1) := by
  have hn : dualNumerators001 16 1 = ![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 0, 0, 0, 0, 1184800741849, 1308901425339, 179862976578, 1129038448761, 0, 788396879662, 925537360486, 179862976579, 1048772159673, 136028582177, 861863417206, 243536919859] := rfl
  have he : residualNumerators 1 16 1 = 744190347618485 := rfl
  have hr : radiusNumerators 16 = 10683060 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_17_0 :
    integerResidualCheck 1 17 0 (dualNumerators001 17 0) ∧
    integerMassCheck 1 17 0 (dualNumerators001 17 0) := by
  have hn : dualNumerators001 17 0 = ![275782051153, 50770698773, 275782051153, 0, 1, 414444535771, 490742607366, 0, 386670191328, 275782051153, 414444535771, 0, 0, 0, 1032887523019, 0, 0, 457855084348, 928815106981, 784407834273, 427425359826, 642333698256, 427425359826, 506113164564, 414444535771, 0, 0, 0, 0, 542144915654, 642333698256, 709614252839, 97511798266, 612102454573, 0, 427425359826, 501775374235, 97511798267, 568586494045, 73747204211, 467254869626, 132032302875] := rfl
  have he : residualNumerators 1 17 0 = 444310779722329 := rfl
  have hr : radiusNumerators 17 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_17_1 :
    integerResidualCheck 1 17 1 (dualNumerators001 17 1) ∧
    integerMassCheck 1 17 1 (dualNumerators001 17 1) := by
  have hn : dualNumerators001 17 1 = ![508686963928, 93647837150, 508686963928, 0, 1, 764453421592, 905187143136, 0, 713222941253, 508686963927, 764453421593, 0, 0, 1000000000000, 905187143136, 0, 844525275674, 0, 1713222941251, 1446860076751, 788396879661, 1184800741848, 788396879661, 933538524388, 764453421592, 1, 0, 1000000000000, 0, 0, 1184800741848, 1308901425338, 179862976578, 1129038448761, 0, 788396879661, 925537360485, 179862976579, 1048772159672, 136028582177, 861863417205, 243536919859] := rfl
  have he : residualNumerators 1 17 1 = 812784255225138 := rfl
  have hr : radiusNumerators 17 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_18_0 :
    integerResidualCheck 1 18 0 (dualNumerators001 18 0) ∧
    integerMassCheck 1 18 0 (dualNumerators001 18 0) := by
  have hn : dualNumerators001 18 0 = ![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 562515489548, 74022925577, 0, 476109064652, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 261721072458, 1006675626970, 0, 763999473637, 809471999789, 261721072459, 862769256399, 123780303264, 835192545885, 236000526363] := rfl
  have he : residualNumerators 1 18 0 = 621507176557322 := rfl
  have hr : radiusNumerators 18 = 13565580 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_18_1 :
    integerResidualCheck 1 18 1 (dualNumerators001 18 1) ∧
    integerMassCheck 1 18 1 (dualNumerators001 18 1) := by
  have hn : dualNumerators001 18 1 = ![538874628613, 99205301184, 538874628613, 0, 1, 173280948973, 205181483568, 0, 64396810428, 45929282541, 82602613712, 90678335261, 0, 583235221374, 205181483568, 0, 0, 492556886114, 154686685730, 130636815909, 835183729590, 268562336295, 71184255953, 84289076957, 173280948973, 1, 90678335261, 492556886113, 0, 0, 268562336295, 763397412564, 0, 118180546476, 71184255953, 0, 99806458592, 1, 177057282341, 91505053955, 77817540467, 21988918126] := rfl
  have he : residualNumerators 1 18 1 = 248549256815663 := rfl
  have hr : radiusNumerators 18 = 13565580 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_19_0 :
    integerResidualCheck 1 19 0 (dualNumerators001 19 0) ∧
    integerMassCheck 1 19 0 (dualNumerators001 19 0) := by
  have hn : dualNumerators001 19 0 = ![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 216703300504, 217988955956, 0, 1402086139076, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 307298608851, 763894463397, 0, 645216866088, 597351015788, 307298608852, 577111910116, 96603051948, 705341215054, 199308409586] := rfl
  have he : residualNumerators 1 19 0 = 627988796584033 := rfl
  have hr : radiusNumerators 19 = 8248658 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_19_1 :
    integerResidualCheck 1 19 1 (dualNumerators001 19 1) ∧
    integerMassCheck 1 19 1 (dualNumerators001 19 1) := by
  have hn : dualNumerators001 19 1 = ![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 1, 0, 0, 0, 0, 987477735649, 0, 0, 763999473637, 55115222459, 405068248518, 645216866088, 1, 838241775551, 149235960098, 503065535987, 142151330101] := rfl
  have he : residualNumerators 1 19 1 = 510429784189875 := rfl
  have hr : radiusNumerators 19 = 8248658 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_20_0 :
    integerResidualCheck 1 20 0 (dualNumerators001 20 0) ∧
    integerMassCheck 1 20 0 (dualNumerators001 20 0) := by
  have hn : dualNumerators001 20 0 = ![525362030296, 96717669897, 525362030297, 0, 2, 1982073878105, 2346968095805, 0, 736602820676, 525362030296, 1821502598273, 160571279835, 0, 1032780604873, 2346968095805, 0, 0, 872209325041, 1769383425548, 1494289025233, 814241006257, 3071949885822, 814241006257, 964140481890, 1982073878105, 2, 160571279833, 872209325040, 0, 0, 3071949885822, 1351808005780, 0, 1351808005780, 814241006257, 0, 1141636028738, 1, 2025269461734, 1046680424089, 890115821339, 251520207400] := rfl
  have he : residualNumerators 1 20 0 = 1230195150963381 := rfl
  have hr : radiusNumerators 20 = 35312013 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_20_1 :
    integerResidualCheck 1 20 1 (dualNumerators001 20 1) ∧
    integerMassCheck 1 20 1 (dualNumerators001 20 1) := by
  have hn : dualNumerators001 20 1 = ![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 0, 87654492241, 172716091384, 1501965016760, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 1, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 1301213128929, 890779360508, 0, 1320313360088, 549979932486, 1301213128931, 0, 135852760286, 1443346382594, 407846678822] := rfl
  have he : residualNumerators 1 20 1 = 954586689513097 := rfl
  have hr : radiusNumerators 20 = 35312013 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_21_0 :
    integerResidualCheck 1 21 0 (dualNumerators001 21 0) ∧
    integerMassCheck 1 21 0 (dualNumerators001 21 0) := by
  have hn : dualNumerators001 21 0 = ![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 604293255477, 704608169863, 851509250277, 798941670661, 1020530044549, 288371380791] := rfl
  have he : residualNumerators 1 21 0 = 755404998366421 := rfl
  have hr : radiusNumerators 21 = 11182451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_21_1 :
    integerResidualCheck 1 21 1 (dualNumerators001 21 1) ∧
    integerMassCheck 1 21 1 (dualNumerators001 21 1) := by
  have hn : dualNumerators001 21 1 = ![114087637157, 21003212630, 114087637157, 0, 1, 11738971135, 13900082653, 0, 159960694697, 114087637156, 0, 11738971135, 207227876819, 1201147979134, 13900082653, 0, 0, 1189409008001, 1568336550649, 324499857786, 176820605835, 18193837997, 176820605835, 209372781287, 11738971135, 0, 218966847953, 1189409008000, 0, 0, 18193837997, 1843425165269, 878870811393, 964554353877, 0, 176820605835, 73655079013, 174262641531, 0, 18193837997, 193297583373, 54620137172] := rfl
  have he : residualNumerators 1 21 1 = 393600022291398 := rfl
  have hr : radiusNumerators 21 = 11182451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_22_0 :
    integerResidualCheck 1 22 0 (dualNumerators001 22 0) ∧
    integerMassCheck 1 22 0 (dualNumerators001 22 0) := by
  have hn : dualNumerators001 22 0 = ![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 583695195717, 0, 612220343875, 0, 492945346072, 0, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 583695195717, 0, 0, 0, 801336080718, 763999473637, 565168626292, 198830847345, 460183470977, 0, 139439543571, 505777322518, 256292246333, 545043834385, 503065535987, 142151330101] := rfl
  have he : residualNumerators 1 22 0 = 467009268151641 := rfl
  have hr : radiusNumerators 22 = 6465674 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_22_1 :
    integerResidualCheck 1 22 1 (dualNumerators001 22 1) ∧
    integerMassCheck 1 22 1 (dualNumerators001 22 1) := by
  have hn : dualNumerators001 22 1 = ![50594765625, 9314353833, 50594765625, 0, 0, 5205914576, 6164308785, 0, 70938219592, 50594765625, 0, 5205914576, 10257833851, 89203660570, 6164308785, 0, 0, 83997745994, 1170399714012, 143906865451, 78415131848, 8068472555, 78415131848, 92851136735, 5205914576, 0, 15463748427, 83997745994, 0, 0, 8068472555, 130185291813, 17889440442, 112295851372, 0, 78415131848, 32664025241, 77280744217, 0, 8068472555, 85722223462, 24222545996] := rfl
  have he : residualNumerators 1 22 1 = 97887699060409 := rfl
  have hr : radiusNumerators 22 = 6465674 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_23_0 :
    integerResidualCheck 1 23 0 (dualNumerators001 23 0) ∧
    integerMassCheck 1 23 0 (dualNumerators001 23 0) := by
  have hn : dualNumerators001 23 0 = ![525362030296, 96717669897, 525362030296, 0, 2, 1982073878105, 2346968095804, 0, 736602820676, 525362030295, 1821502598274, 160571279833, 0, 1032780604872, 2346968095804, 0, 0, 872209325040, 1769383425546, 1494289025232, 814241006256, 3071949885821, 814241006256, 964140481889, 1982073878106, 0, 160571279833, 872209325039, 0, 0, 3071949885821, 1351808005779, 1000000000000, 351808005780, 814241006256, 0, 1141636028738, 0, 2025269461734, 1046680424088, 890115821339, 251520207400] := rfl
  have he : residualNumerators 1 23 0 = 1233606156643998 := rfl
  have hr : radiusNumerators 23 = 35297932 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_23_1 :
    integerResidualCheck 1 23 1 (dualNumerators001 23 1) ∧
    integerMassCheck 1 23 1 (dualNumerators001 23 1) := by
  have hn : dualNumerators001 23 1 = ![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 0, 87654492241, 172716091384, 1501965016760, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 1, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 301213128929, 1890779360508, 0, 1320313360088, 549979932486, 1301213128931, 0, 135852760286, 1443346382594, 407846678822] := rfl
  have he : residualNumerators 1 23 1 = 954586689513097 := rfl
  have hr : radiusNumerators 23 = 35297932 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_24_0 :
    integerResidualCheck 1 24 0 (dualNumerators001 24 0) ∧
    integerMassCheck 1 24 0 (dualNumerators001 24 0) := by
  have hn : dualNumerators001 24 0 = ![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 276221246109, 150663467366, 0, 969054410724, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 384946583730, 686246488518, 569308312247, 737522866658, 835192545885, 236000526363] := rfl
  have he : residualNumerators 1 24 0 = 668384906521344 := rfl
  have hr : radiusNumerators 24 = 9356857 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_24_1 :
    integerResidualCheck 1 24 1 (dualNumerators001 24 1) ∧
    integerMassCheck 1 24 1 (dualNumerators001 24 1) := by
  have hn : dualNumerators001 24 1 = ![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 395480180778, 20824623507, 0, 133942179966, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 587483804282, 282115266095, 48434165160, 99625565721, 0, 0, 115439864933, 32619865948] := rfl
  have he : residualNumerators 1 24 1 = 230534867381230 := rfl
  have hr : radiusNumerators 24 = 9356857 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_25_0 :
    integerResidualCheck 1 25 0 (dualNumerators001 25 0) ∧
    integerMassCheck 1 25 0 (dualNumerators001 25 0) := by
  have hn : dualNumerators001 25 0 = ![30936264063, 5695279071, 30936264063, 0, 1, 16941043971, 20059842445, 0, 627070502755, 447241068346, 373191945837, 136694444207, 0, 879206860134, 603755038162, 0, 0, 742512415929, 1506277362888, 1272089305134, 47947079019, 26256356369, 693163945107, 820773474842, 509886390043, 1, 136694444206, 742512415929, 0, 0, 790255830005, 1150795112397, 638438115729, 512356996669, 47947079019, 0, 333437443812, 638438115729, 26256356369, 0, 757756228906, 214119330636] := rfl
  have he : residualNumerators 1 25 0 = 504349421940160 := rfl
  have hr : radiusNumerators 25 = 8671199 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_25_1 :
    integerResidualCheck 1 25 1 (dualNumerators001 25 1) ∧
    integerMassCheck 1 25 1 (dualNumerators001 25 1) := by
  have hn : dualNumerators001 25 1 = ![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 0, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 415529968297, 599898615461, 0, 0] := rfl
  have he : residualNumerators 1 25 1 = 223581994926723 := rfl
  have hr : radiusNumerators 25 = 8671199 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_26_0 :
    integerResidualCheck 1 26 0 (dualNumerators001 26 0) ∧
    integerMassCheck 1 26 0 (dualNumerators001 26 0) := by
  have hn : dualNumerators001 26 0 = ![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0] := rfl
  have he : residualNumerators 1 26 0 = 396300992921948 := rfl
  have hr : radiusNumerators 26 = 15099566 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_26_1 :
    integerResidualCheck 1 26 1 (dualNumerators001 26 1) ∧
    integerMassCheck 1 26 1 (dualNumerators001 26 1) := by
  have hn : dualNumerators001 26 1 = ![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 879744679617, 350168760452, 564110399358, 1160334187225, 0, 0, 1344522571906, 379922014678] := rfl
  have he : residualNumerators 1 26 1 = 855600806020798 := rfl
  have hr : radiusNumerators 26 = 15099566 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_27_0 :
    integerResidualCheck 1 27 0 (dualNumerators001 27 0) ∧
    integerMassCheck 1 27 0 (dualNumerators001 27 0) := by
  have hn : dualNumerators001 27 0 = ![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312724, 1, 0, 0, 0, 0, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 286173900105, 455299762271, 595678484088, 168320989550] := rfl
  have he : residualNumerators 1 27 0 = 409706678433734 := rfl
  have hr : radiusNumerators 27 = 7338775 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_27_1 :
    integerResidualCheck 1 27 1 (dualNumerators001 27 1) ∧
    integerMassCheck 1 27 1 (dualNumerators001 27 1) := by
  have hn : dualNumerators001 27 1 = ![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 234337221023, 181967583262, 0, 1170399780726, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 575645700633, 956292240576, 0, 377837583379, 718114611481, 575645700634, 576174693322, 69042172766, 413046270426, 116714568052] := rfl
  have he : residualNumerators 1 27 1 = 548500316720415 := rfl
  have hr : radiusNumerators 27 = 7338775 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_28_0 :
    integerResidualCheck 1 28 0 (dualNumerators001 28 0) ∧
    integerMassCheck 1 28 0 (dualNumerators001 28 0) := by
  have hn : dualNumerators001 28 0 = ![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 1, 0, 0, 0, 0, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 450383711774, 395438493575, 503065535987, 142151330101] := rfl
  have he : residualNumerators 1 28 0 = 285363467233393 := rfl
  have hr : radiusNumerators 28 = 10335557 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_28_1 :
    integerResidualCheck 1 28 1 (dualNumerators001 28 1) ∧
    integerMassCheck 1 28 1 (dualNumerators001 28 1) := by
  have hn : dualNumerators001 28 1 = ![71098470185, 13089028086, 71098470186, 0, 1, 500260975618, 592357612055, 0, 99686179557, 71098470185, 0, 7315629546, 105164706304, 618299100026, 8662416338, 0, 0, 610983470481, 1239454790169, 202225622679, 110193136482, 775337722729, 110193136482, 130479382508, 7315629546, 0, 112480335850, 610983470480, 0, 0, 11338249092, 946942807286, 438489340489, 508453466798, 0, 110193136482, 361227794882, 438489340489, 0, 11338249092, 120461452361, 34038816922] := rfl
  have he : residualNumerators 1 28 1 = 310908116290873 := rfl
  have hr : radiusNumerators 28 = 10335557 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_29_0 :
    integerResidualCheck 1 29 0 (dualNumerators001 29 0) ∧
    integerMassCheck 1 29 0 (dualNumerators001 29 0) := by
  have hn : dualNumerators001 29 0 = ![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0] := rfl
  have he : residualNumerators 1 29 0 = 396300992921948 := rfl
  have hr : radiusNumerators 29 = 40352153 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_29_1 :
    integerResidualCheck 1 29 1 (dualNumerators001 29 1) ∧
    integerMassCheck 1 29 1 (dualNumerators001 29 1) := by
  have hn : dualNumerators001 29 1 = ![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 0, 87654492241, 172716091384, 1501965016760, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 1, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 301213128929, 1890779360508, 0, 1320313360088, 1549979932486, 301213128931, 0, 135852760286, 1443346382594, 407846678822] := rfl
  have he : residualNumerators 1 29 1 = 954586689513097 := rfl
  have hr : radiusNumerators 29 = 40352153 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_30_0 :
    integerResidualCheck 1 30 0 (dualNumerators001 30 0) ∧
    integerMassCheck 1 30 0 (dualNumerators001 30 0) := by
  have hn : dualNumerators001 30 0 = ![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 77683757550, 37915592377, 0, 243869815754, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 1, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 43863150959, 275338398478, 0, 192266201784, 225710625575, 43863150960, 151451427040, 27712131761, 269573776534, 0] := rfl
  have he : residualNumerators 1 30 0 = 215817496664297 := rfl
  have hr : radiusNumerators 30 = 7680628 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_30_1 :
    integerResidualCheck 1 30 1 (dualNumerators001 30 1) ∧
    integerMassCheck 1 30 1 (dualNumerators001 30 1) := by
  have hn : dualNumerators001 30 1 = ![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 491724510490, 107456641334, 0, 691151837050, 709488714054, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 124312626679, 780336997961, 0, 544901951702, 639686846958, 124312626680, 829173251111, 99477537975, 536287180313, 227712293325] := rfl
  have he : residualNumerators 1 30 1 = 552336465097545 := rfl
  have hr : radiusNumerators 30 = 7680628 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_31_0 :
    integerResidualCheck 1 31 0 (dualNumerators001 31 0) ∧
    integerMassCheck 1 31 0 (dualNumerators001 31 0) := by
  have hn : dualNumerators001 31 0 = ![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1487243996141, 231835083176, 0, 1491143233587, 2035556695381, 0, 0, 1259308150414, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079315, 2, 231835083174, 1259308150413, 0, 0, 2664343059941, 1951759503826, 0, 1951759503826, 472517800158, 1808495209395, 1648310233016, 2, 1836249633286, 828093426656, 1648310233018, 0] := rfl
  have he : residualNumerators 1 31 0 = 1678982460545983 := rfl
  have hr : radiusNumerators 31 = 32891612 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_31_1 :
    integerResidualCheck 1 31 1 (dualNumerators001 31 1) ∧
    integerMassCheck 1 31 1 (dualNumerators001 31 1) := by
  have hn : dualNumerators001 31 1 = ![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 274671058114, 217988955956, 0, 1402086139076, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 556963843680, 992902647048, 725570984152, 37986262977, 845258320866, 704608169862] := rfl
  have he : residualNumerators 1 31 1 = 651385257669341 := rfl
  have hr : radiusNumerators 31 = 32891612 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_32_0 :
    integerResidualCheck 1 32 0 (dualNumerators001 32 0) ∧
    integerMassCheck 1 32 0 (dualNumerators001 32 0) := by
  have hn : dualNumerators001 32 0 = ![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 979882959195, 1099655708204, 1160276651773, 0, 382837210862, 2079538667397, 0, 979882959196, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 180393692578, 979882959195, 0, 0, 3223007296772, 1518687763292, 208690812242, 1309996951051, 0, 914758491801, 1073879389714, 208690812243, 2973224772447, 249782524326, 0, 1282570201956] := rfl
  have he : residualNumerators 1 32 0 = 1331602979220572 := rfl
  have hr : radiusNumerators 32 = 67647473 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck001_32_1 :
    integerResidualCheck 1 32 1 (dualNumerators001 32 1) ∧
    integerMassCheck 1 32 1 (dualNumerators001 32 1) := by
  have hn : dualNumerators001 32 1 = ![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1307998858623, 638403098873, 0, 4106153599144, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957494, 2, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 738545008627, 4636005289951, 0, 3237278684975, 3800398563899, 738545008631, 2550060655570, 466602515837, 4538943572529, 0] := rfl
  have he : residualNumerators 1 32 1 = 2884011955971833 := rfl
  have hr : radiusNumerators 32 = 67647473 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots001]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature001_entry]
    rw [hn, he, hr]
    decide

theorem integerChecks001 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 1 j s (dualNumerators001 j s) ∧
    integerMassCheck 1 j s (dualNumerators001 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck001_0_0
    · exact integerCheck001_0_1
  · fin_cases s
    · exact integerCheck001_1_0
    · exact integerCheck001_1_1
  · fin_cases s
    · exact integerCheck001_2_0
    · exact integerCheck001_2_1
  · fin_cases s
    · exact integerCheck001_3_0
    · exact integerCheck001_3_1
  · fin_cases s
    · exact integerCheck001_4_0
    · exact integerCheck001_4_1
  · fin_cases s
    · exact integerCheck001_5_0
    · exact integerCheck001_5_1
  · fin_cases s
    · exact integerCheck001_6_0
    · exact integerCheck001_6_1
  · fin_cases s
    · exact integerCheck001_7_0
    · exact integerCheck001_7_1
  · fin_cases s
    · exact integerCheck001_8_0
    · exact integerCheck001_8_1
  · fin_cases s
    · exact integerCheck001_9_0
    · exact integerCheck001_9_1
  · fin_cases s
    · exact integerCheck001_10_0
    · exact integerCheck001_10_1
  · fin_cases s
    · exact integerCheck001_11_0
    · exact integerCheck001_11_1
  · fin_cases s
    · exact integerCheck001_12_0
    · exact integerCheck001_12_1
  · fin_cases s
    · exact integerCheck001_13_0
    · exact integerCheck001_13_1
  · fin_cases s
    · exact integerCheck001_14_0
    · exact integerCheck001_14_1
  · fin_cases s
    · exact integerCheck001_15_0
    · exact integerCheck001_15_1
  · fin_cases s
    · exact integerCheck001_16_0
    · exact integerCheck001_16_1
  · fin_cases s
    · exact integerCheck001_17_0
    · exact integerCheck001_17_1
  · fin_cases s
    · exact integerCheck001_18_0
    · exact integerCheck001_18_1
  · fin_cases s
    · exact integerCheck001_19_0
    · exact integerCheck001_19_1
  · fin_cases s
    · exact integerCheck001_20_0
    · exact integerCheck001_20_1
  · fin_cases s
    · exact integerCheck001_21_0
    · exact integerCheck001_21_1
  · fin_cases s
    · exact integerCheck001_22_0
    · exact integerCheck001_22_1
  · fin_cases s
    · exact integerCheck001_23_0
    · exact integerCheck001_23_1
  · fin_cases s
    · exact integerCheck001_24_0
    · exact integerCheck001_24_1
  · fin_cases s
    · exact integerCheck001_25_0
    · exact integerCheck001_25_1
  · fin_cases s
    · exact integerCheck001_26_0
    · exact integerCheck001_26_1
  · fin_cases s
    · exact integerCheck001_27_0
    · exact integerCheck001_27_1
  · fin_cases s
    · exact integerCheck001_28_0
    · exact integerCheck001_28_1
  · fin_cases s
    · exact integerCheck001_29_0
    · exact integerCheck001_29_1
  · fin_cases s
    · exact integerCheck001_30_0
    · exact integerCheck001_30_1
  · fin_cases s
    · exact integerCheck001_31_0
    · exact integerCheck001_31_1
  · fin_cases s
    · exact integerCheck001_32_0
    · exact integerCheck001_32_1

end ElevenSquare.Tasks.T06
