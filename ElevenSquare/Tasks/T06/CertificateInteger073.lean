import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual073
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
import ElevenSquare.Tasks.T06.SparseColumn21
import ElevenSquare.Tasks.T06.SparseColumn22
import ElevenSquare.Tasks.T06.SparseColumn23
import ElevenSquare.Tasks.T06.SparseColumn24
import ElevenSquare.Tasks.T06.SparseColumn25
import ElevenSquare.Tasks.T06.SparseColumn27
import ElevenSquare.Tasks.T06.SparseColumn28
import ElevenSquare.Tasks.T06.SparseColumn30
import ElevenSquare.Tasks.T06.SparseColumn31
import ElevenSquare.Tasks.T06.SparseColumn32
import ElevenSquare.Tasks.T06.SparseColumn33
import ElevenSquare.Tasks.T06.SparseColumn34
import ElevenSquare.Tasks.T06.SparseColumn45
import ElevenSquare.Tasks.T06.SparseColumn55
import ElevenSquare.Tasks.T06.SparseColumn57

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix073 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral28, roundedGradientLiteral42, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix073_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = branchIntegerMatrix073 := by
  change roundedGradients ∘ branchRows 73 = branchIntegerMatrix073
  rw [show branchRows 73 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 32, 33, 54, 55, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral28_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral42_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix073]

theorem branchColumn073_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 0) i) = _
  rw [branchColumn073_0]
  exact sparseColumn00_sum n

theorem branchColumn073_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 1) i) = _
  rw [branchColumn073_1]
  exact sparseColumn01_sum n

theorem branchColumn073_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 2) i) = _
  rw [branchColumn073_2]
  exact sparseColumn02_sum n

theorem branchColumn073_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 3) i) = _
  rw [branchColumn073_3]
  exact sparseColumn03_sum n

theorem branchColumn073_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 4) i) = _
  rw [branchColumn073_4]
  exact sparseColumn04_sum n

theorem branchColumn073_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 5) i) = _
  rw [branchColumn073_5]
  exact sparseColumn05_sum n

theorem branchColumn073_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 6) i) = _
  rw [branchColumn073_6]
  exact sparseColumn06_sum n

theorem branchColumn073_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 7) i) = _
  rw [branchColumn073_7]
  exact sparseColumn07_sum n

theorem branchColumn073_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 8) i) = _
  rw [branchColumn073_8]
  exact sparseColumn08_sum n

theorem branchColumn073_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 9) i) = _
  rw [branchColumn073_9]
  exact sparseColumn09_sum n

theorem branchColumn073_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 10) i) = _
  rw [branchColumn073_10]
  exact sparseColumn10_sum n

theorem branchColumn073_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 11) i) = _
  rw [branchColumn073_11]
  exact sparseColumn11_sum n

theorem branchColumn073_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 12) = sparseColumn12 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 12) = sparseDot12 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 12) i) = _
  rw [branchColumn073_12]
  exact sparseColumn12_sum n

theorem branchColumn073_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 13) = sparseColumn13 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 13) = sparseDot13 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 13) i) = _
  rw [branchColumn073_13]
  exact sparseColumn13_sum n

theorem branchColumn073_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 14) = sparseColumn33 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 14) = sparseDot33 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 14) i) = _
  rw [branchColumn073_14]
  exact sparseColumn33_sum n

theorem branchColumn073_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 15) = sparseColumn15 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 15) = sparseDot15 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 15) i) = _
  rw [branchColumn073_15]
  exact sparseColumn15_sum n

theorem branchColumn073_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 16) = sparseColumn16 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 16) = sparseDot16 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 16) i) = _
  rw [branchColumn073_16]
  exact sparseColumn16_sum n

theorem branchColumn073_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 17) = sparseColumn34 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 17) = sparseDot34 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 17) i) = _
  rw [branchColumn073_17]
  exact sparseColumn34_sum n

theorem branchColumn073_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 18) i) = _
  rw [branchColumn073_18]
  exact sparseColumn18_sum n

theorem branchColumn073_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 19) i) = _
  rw [branchColumn073_19]
  exact sparseColumn19_sum n

theorem branchColumn073_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 20) = sparseColumn55 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 20) = sparseDot55 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 20) i) = _
  rw [branchColumn073_20]
  exact sparseColumn55_sum n

theorem branchColumn073_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 21) i) = _
  rw [branchColumn073_21]
  exact sparseColumn21_sum n

theorem branchColumn073_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 22) i) = _
  rw [branchColumn073_22]
  exact sparseColumn22_sum n

theorem branchColumn073_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 23) = sparseColumn23 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 23) = sparseDot23 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 23) i) = _
  rw [branchColumn073_23]
  exact sparseColumn23_sum n

theorem branchColumn073_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 24) i) = _
  rw [branchColumn073_24]
  exact sparseColumn24_sum n

theorem branchColumn073_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 25) i) = _
  rw [branchColumn073_25]
  exact sparseColumn25_sum n

theorem branchColumn073_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 26) = sparseColumn57 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 26) = sparseDot57 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 26) i) = _
  rw [branchColumn073_26]
  exact sparseColumn57_sum n

theorem branchColumn073_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 27) i) = _
  rw [branchColumn073_27]
  exact sparseColumn27_sum n

theorem branchColumn073_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 28) i) = _
  rw [branchColumn073_28]
  exact sparseColumn28_sum n

theorem branchColumn073_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 29) = sparseColumn45 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 29) = sparseDot45 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 29) i) = _
  rw [branchColumn073_29]
  exact sparseColumn45_sum n

theorem branchColumn073_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 30) i) = _
  rw [branchColumn073_30]
  exact sparseColumn30_sum n

theorem branchColumn073_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 31) i) = _
  rw [branchColumn073_31]
  exact sparseColumn31_sum n

theorem branchColumn073_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 73 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 73 i)) = _
  rw [branchIntegerMatrix073_eq]
  simp only [branchIntegerMatrix073, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot073_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 73 i) 32) i) = _
  rw [branchColumn073_32]
  exact sparseColumn32_sum n

def branchSparseDots073 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot12, sparseDot13, sparseDot33, sparseDot15, sparseDot16, sparseDot34, sparseDot18, sparseDot19, sparseDot55, sparseDot21, sparseDot22, sparseDot23, sparseDot24, sparseDot25, sparseDot57, sparseDot27, sparseDot28, sparseDot45, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot073_0 :
    branchSparseDots073 0 = sparseDot00 := rfl

private theorem branchSparseDot073_1 :
    branchSparseDots073 1 = sparseDot01 := rfl

private theorem branchSparseDot073_2 :
    branchSparseDots073 2 = sparseDot02 := rfl

private theorem branchSparseDot073_3 :
    branchSparseDots073 3 = sparseDot03 := rfl

private theorem branchSparseDot073_4 :
    branchSparseDots073 4 = sparseDot04 := rfl

private theorem branchSparseDot073_5 :
    branchSparseDots073 5 = sparseDot05 := rfl

private theorem branchSparseDot073_6 :
    branchSparseDots073 6 = sparseDot06 := rfl

private theorem branchSparseDot073_7 :
    branchSparseDots073 7 = sparseDot07 := rfl

private theorem branchSparseDot073_8 :
    branchSparseDots073 8 = sparseDot08 := rfl

private theorem branchSparseDot073_9 :
    branchSparseDots073 9 = sparseDot09 := rfl

private theorem branchSparseDot073_10 :
    branchSparseDots073 10 = sparseDot10 := rfl

private theorem branchSparseDot073_11 :
    branchSparseDots073 11 = sparseDot11 := rfl

private theorem branchSparseDot073_12 :
    branchSparseDots073 12 = sparseDot12 := rfl

private theorem branchSparseDot073_13 :
    branchSparseDots073 13 = sparseDot13 := rfl

private theorem branchSparseDot073_14 :
    branchSparseDots073 14 = sparseDot33 := rfl

private theorem branchSparseDot073_15 :
    branchSparseDots073 15 = sparseDot15 := rfl

private theorem branchSparseDot073_16 :
    branchSparseDots073 16 = sparseDot16 := rfl

private theorem branchSparseDot073_17 :
    branchSparseDots073 17 = sparseDot34 := rfl

private theorem branchSparseDot073_18 :
    branchSparseDots073 18 = sparseDot18 := rfl

private theorem branchSparseDot073_19 :
    branchSparseDots073 19 = sparseDot19 := rfl

private theorem branchSparseDot073_20 :
    branchSparseDots073 20 = sparseDot55 := rfl

private theorem branchSparseDot073_21 :
    branchSparseDots073 21 = sparseDot21 := rfl

private theorem branchSparseDot073_22 :
    branchSparseDots073 22 = sparseDot22 := rfl

private theorem branchSparseDot073_23 :
    branchSparseDots073 23 = sparseDot23 := rfl

private theorem branchSparseDot073_24 :
    branchSparseDots073 24 = sparseDot24 := rfl

private theorem branchSparseDot073_25 :
    branchSparseDots073 25 = sparseDot25 := rfl

private theorem branchSparseDot073_26 :
    branchSparseDots073 26 = sparseDot57 := rfl

private theorem branchSparseDot073_27 :
    branchSparseDots073 27 = sparseDot27 := rfl

private theorem branchSparseDot073_28 :
    branchSparseDots073 28 = sparseDot28 := rfl

private theorem branchSparseDot073_29 :
    branchSparseDots073 29 = sparseDot45 := rfl

private theorem branchSparseDot073_30 :
    branchSparseDots073 30 = sparseDot30 := rfl

private theorem branchSparseDot073_31 :
    branchSparseDots073 31 = sparseDot31 := rfl

private theorem branchSparseDot073_32 :
    branchSparseDots073 32 = sparseDot32 := rfl

theorem branchDots073 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 73 i) k) = branchSparseDots073 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot073_0 n
      _ = _ := congrFun branchSparseDot073_0.symm n
  · calc
      _ = sparseDot01 n := branchDot073_1 n
      _ = _ := congrFun branchSparseDot073_1.symm n
  · calc
      _ = sparseDot02 n := branchDot073_2 n
      _ = _ := congrFun branchSparseDot073_2.symm n
  · calc
      _ = sparseDot03 n := branchDot073_3 n
      _ = _ := congrFun branchSparseDot073_3.symm n
  · calc
      _ = sparseDot04 n := branchDot073_4 n
      _ = _ := congrFun branchSparseDot073_4.symm n
  · calc
      _ = sparseDot05 n := branchDot073_5 n
      _ = _ := congrFun branchSparseDot073_5.symm n
  · calc
      _ = sparseDot06 n := branchDot073_6 n
      _ = _ := congrFun branchSparseDot073_6.symm n
  · calc
      _ = sparseDot07 n := branchDot073_7 n
      _ = _ := congrFun branchSparseDot073_7.symm n
  · calc
      _ = sparseDot08 n := branchDot073_8 n
      _ = _ := congrFun branchSparseDot073_8.symm n
  · calc
      _ = sparseDot09 n := branchDot073_9 n
      _ = _ := congrFun branchSparseDot073_9.symm n
  · calc
      _ = sparseDot10 n := branchDot073_10 n
      _ = _ := congrFun branchSparseDot073_10.symm n
  · calc
      _ = sparseDot11 n := branchDot073_11 n
      _ = _ := congrFun branchSparseDot073_11.symm n
  · calc
      _ = sparseDot12 n := branchDot073_12 n
      _ = _ := congrFun branchSparseDot073_12.symm n
  · calc
      _ = sparseDot13 n := branchDot073_13 n
      _ = _ := congrFun branchSparseDot073_13.symm n
  · calc
      _ = sparseDot33 n := branchDot073_14 n
      _ = _ := congrFun branchSparseDot073_14.symm n
  · calc
      _ = sparseDot15 n := branchDot073_15 n
      _ = _ := congrFun branchSparseDot073_15.symm n
  · calc
      _ = sparseDot16 n := branchDot073_16 n
      _ = _ := congrFun branchSparseDot073_16.symm n
  · calc
      _ = sparseDot34 n := branchDot073_17 n
      _ = _ := congrFun branchSparseDot073_17.symm n
  · calc
      _ = sparseDot18 n := branchDot073_18 n
      _ = _ := congrFun branchSparseDot073_18.symm n
  · calc
      _ = sparseDot19 n := branchDot073_19 n
      _ = _ := congrFun branchSparseDot073_19.symm n
  · calc
      _ = sparseDot55 n := branchDot073_20 n
      _ = _ := congrFun branchSparseDot073_20.symm n
  · calc
      _ = sparseDot21 n := branchDot073_21 n
      _ = _ := congrFun branchSparseDot073_21.symm n
  · calc
      _ = sparseDot22 n := branchDot073_22 n
      _ = _ := congrFun branchSparseDot073_22.symm n
  · calc
      _ = sparseDot23 n := branchDot073_23 n
      _ = _ := congrFun branchSparseDot073_23.symm n
  · calc
      _ = sparseDot24 n := branchDot073_24 n
      _ = _ := congrFun branchSparseDot073_24.symm n
  · calc
      _ = sparseDot25 n := branchDot073_25 n
      _ = _ := congrFun branchSparseDot073_25.symm n
  · calc
      _ = sparseDot57 n := branchDot073_26 n
      _ = _ := congrFun branchSparseDot073_26.symm n
  · calc
      _ = sparseDot27 n := branchDot073_27 n
      _ = _ := congrFun branchSparseDot073_27.symm n
  · calc
      _ = sparseDot28 n := branchDot073_28 n
      _ = _ := congrFun branchSparseDot073_28.symm n
  · calc
      _ = sparseDot45 n := branchDot073_29 n
      _ = _ := congrFun branchSparseDot073_29.symm n
  · calc
      _ = sparseDot30 n := branchDot073_30 n
      _ = _ := congrFun branchSparseDot073_30.symm n
  · calc
      _ = sparseDot31 n := branchDot073_31 n
      _ = _ := congrFun branchSparseDot073_31.symm n
  · calc
      _ = sparseDot32 n := branchDot073_32 n
      _ = _ := congrFun branchSparseDot073_32.symm n

def branchIntegerCurvature073 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101981296, 101981296, 79086693, 79086693, 115699695, 115699695, 88123140, 88123140, 204734428, 204734428]

theorem branchIntegerCurvature073_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 73 i)) = branchIntegerCurvature073 := by
  change curvatureNumerators ∘ branchRows 73 = branchIntegerCurvature073
  rw [show branchRows 73 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 32, 33, 54, 55, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature073_entry (i : Fin 42) :
    curvatureNumerators (branchRows 73 i) = branchIntegerCurvature073 i :=
  congrFun branchIntegerCurvature073_eq i

def branchResiduals073 : Fin 33 → Fin 2 → ℕ := ![![1298836079769784, 33000000000000], ![1545701694583812, 33000000000000], ![1582373852669008, 1337425552976719], ![33000000000000, 1025492039224637], ![855512920319029, 33000000000000], ![1057264082615963, 894618693070560], ![724814714438427, 624798065222648], ![33000000000000, 763478220318838], ![1581425738454540, 1128872691561402], ![1027150221862989, 33000000000000], ![33000000000000, 778038292551398], ![484523869650523, 466061235425526], ![990992039224637, 66000000000000], ![33000000000000, 407868728535213], ![465416843945314, 577915043058449], ![925720176939429, 33000000000000], ![66000000000000, 744133249905515], ![446441505729995, 812878550080944], ![621743891109522, 259939289498161], ![633721619895239, 512654122287363], ![1317874975590388, 855005206964392], ![751811341995265, 375152244602780], ![469276107797727, 91397125170083], ![1322512764972210, 855005206964392], ![671228213735849, 230845440638654], ![509953380569920, 220935526651417], ![398970616796057, 855005206964392], ![410390631273191, 548448895033009], ![286891125236809, 299207140313493], ![398970616796057, 855005206964392], ![216045807619381, 552641063223376], ![1679952190907465, 651518154550049], ![1327862946018076, 2881544653428319]]

theorem branchResiduals073_eq : residualNumerators 73 = branchResiduals073 := rfl

theorem integerCheck073_0_0 :
    integerResidualCheck 73 0 0 (dualNumerators073 0 0) ∧
    integerMassCheck 73 0 0 (dualNumerators073 0 0) := by
  apply integerChecks_of_simple 73 0 0 (dualNumerators073 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1011030237961, 258120108700, 0, 1660206247774, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1452036338470, 721009985597, 1308901425339, 0, 383156207414, 1452036338471, 1330333654477, 636679939507, 1430871029972, 404321515913]) (branchResiduals073 0 0) 18767167
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck073_0_1 :
    integerResidualCheck 73 0 1 (dualNumerators073 0 1) ∧
    integerMassCheck 73 0 1 (dualNumerators073 0 1) := by
  apply integerChecks_of_simple 73 0 1 (dualNumerators073 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals073 0 1) 18767167
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck073_1_0 :
    integerResidualCheck 73 1 0 (dualNumerators073 1 0) ∧
    integerMassCheck 73 1 0 (dualNumerators073 1 0) := by
  apply integerChecks_of_simple 73 1 0 (dualNumerators073 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1197158056821, 305639293618, 0, 1965845541389, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 1719352138172, 853745892948, 1549866490727, 0, 453694185894, 1719352138174, 1575244332878, 753890922920, 1694290356000, 478755968067]) (branchResiduals073 1 0) 22176635
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck073_1_1 :
    integerResidualCheck 73 1 1 (dualNumerators073 1 1) ∧
    integerMassCheck 73 1 1 (dualNumerators073 1 1) := by
  apply integerChecks_of_simple 73 1 1 (dualNumerators073 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals073 1 1) 22176635
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck073_2_0 :
    integerResidualCheck 73 2 0 (dualNumerators073 2 0) ∧
    integerMassCheck 73 2 0 (dualNumerators073 2 0) := by
  apply integerChecks_of_simple 73 2 0 (dualNumerators073 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1197158056822, 305639293619, 0, 1965845541391, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 1719352138173, 853745892949, 1549866490728, 0, 453694185894, 1719352138175, 1575244332879, 753890922921, 1694290356001, 478755968068]) (branchResiduals073 2 0) 22681452
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck073_2_1 :
    integerResidualCheck 73 2 1 (dualNumerators073 2 1) ∧
    integerMassCheck 73 2 1 (dualNumerators073 2 1) := by
  apply integerChecks_of_simple 73 2 1 (dualNumerators073 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1011030237961, 258120108700, 0, 1660206247773, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1452036338469, 721009985597, 1308901425338, 0, 383156207413, 1452036338470, 1330333654476, 636679939507, 1430871029971, 404321515912]) (branchResiduals073 2 1) 22681452
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck073_3_0 :
    integerResidualCheck 73 3 0 (dualNumerators073 3 0) ∧
    integerMassCheck 73 3 0 (dualNumerators073 3 0) := by
  apply integerChecks_of_simple 73 3 0 (dualNumerators073 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals073 3 0) 16360330
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck073_3_1 :
    integerResidualCheck 73 3 1 (dualNumerators073 3 1) ∧
    integerMassCheck 73 3 1 (dualNumerators073 3 1) := by
  apply integerChecks_of_simple 73 3 1 (dualNumerators073 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 796619754801, 203380245200, 0, 1308124173107, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1144101124261, 568104470439, 1031321016287, 0, 301899777613, 1144101124262, 1048208085022, 501658405706, 1127424369963, 318576531911]) (branchResiduals073 3 1) 16360330
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck073_4_0 :
    integerResidualCheck 73 4 0 (dualNumerators073 4 0) ∧
    integerMassCheck 73 4 0 (dualNumerators073 4 0) := by
  apply integerChecks_of_simple 73 4 0 (dualNumerators073 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 672765518030, 171759757645, 0, 1104743927909, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 966222317365, 479778584509, 870976665588, 0, 254961992914, 966222317366, 885238221966, 423663203373, 952138376845, 269045933435]) (branchResiduals073 4 0) 13760362
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck073_4_1 :
    integerResidualCheck 73 4 1 (dualNumerators073 4 1) ∧
    integerMassCheck 73 4 1 (dualNumerators073 4 1) := by
  apply integerChecks_of_simple 73 4 1 (dualNumerators073 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals073 4 1) 13760362
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck073_5_0 :
    integerResidualCheck 73 5 0 (dualNumerators073 5 0) ∧
    integerMassCheck 73 5 0 (dualNumerators073 5 0) := by
  apply integerChecks_of_simple 73 5 0 (dualNumerators073 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 796619754801, 203380245201, 0, 1308124173108, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000000, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1144101124262, 568104470440, 1031321016288, 0, 301899777613, 1144101124263, 1048208085022, 501658405707, 1127424369964, 318576531911]) (branchResiduals073 5 0) 17641130
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck073_5_1 :
    integerResidualCheck 73 5 1 (dualNumerators073 5 1) ∧
    integerMassCheck 73 5 1 (dualNumerators073 5 1) := by
  apply integerChecks_of_simple 73 5 1 (dualNumerators073 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 966222317364, 479778584509, 870976665588, 0, 254961992914, 966222317365, 885238221966, 423663203373, 952138376844, 269045933435]) (branchResiduals073 5 1) 17641130
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck073_6_0 :
    integerResidualCheck 73 6 0 (dualNumerators073 6 0) ∧
    integerMassCheck 73 6 0 (dualNumerators073 6 0) := by
  apply integerChecks_of_simple 73 6 0 (dualNumerators073 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 0, 70552396879, 187567711821, 1472638535954, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 1, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 659499318402, 1175693227483, 2719950702, 106626845062, 1430871029972, 404321515913]) (branchResiduals073 6 0) 8962451
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck073_6_1 :
    integerResidualCheck 73 6 1 (dualNumerators073 6 1) ∧
    integerMassCheck 73 6 1 (dualNumerators073 6 1) := by
  apply integerChecks_of_simple 73 6 1 (dualNumerators073 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949782, 1, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals073 6 1) 8962451
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck073_7_0 :
    integerResidualCheck 73 7 0 (dualNumerators073 7 0) ∧
    integerMassCheck 73 7 0 (dualNumerators073 7 0) := by
  apply integerChecks_of_simple 73 7 0 (dualNumerators073 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals073 7 0) 10424794
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck073_7_1 :
    integerResidualCheck 73 7 1 (dualNumerators073 7 1) ∧
    integerMassCheck 73 7 1 (dualNumerators073 7 1) := by
  apply integerChecks_of_simple 73 7 1 (dualNumerators073 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 598579028412, 152819646809, 0, 982922770697, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 859676069088, 426872946475, 774933245365, 0, 226847092948, 859676069088, 787622166441, 376945461461, 847145178002, 239377984034]) (branchResiduals073 7 1) 10424794
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck073_8_0 :
    integerResidualCheck 73 8 0 (dualNumerators073 8 0) ∧
    integerMassCheck 73 8 0 (dualNumerators073 8 0) := by
  apply integerChecks_of_simple 73 8 0 (dualNumerators073 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1197158056824, 305639293618, 0, 1965845541393, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 1719352138175, 853745892950, 1549866490730, 0, 453694185895, 1719352138176, 1575244332881, 753890922921, 1694290356003, 478755968068]) (branchResiduals073 8 0) 22681452
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck073_8_1 :
    integerResidualCheck 73 8 1 (dualNumerators073 8 1) ∧
    integerMassCheck 73 8 1 (dualNumerators073 8 1) := by
  apply integerChecks_of_simple 73 8 1 (dualNumerators073 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590429, 217988955956, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139073, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546384, 0, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1226281389033, 608911156849, 1105400337063, 0, 323585101692, 1226281389034, 1123500396284, 537692301428, 1208406751039, 341459739686]) (branchResiduals073 8 1) 22681452
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck073_9_0 :
    integerResidualCheck 73 9 0 (dualNumerators073 9 0) ∧
    integerMassCheck 73 9 0 (dualNumerators073 9 0) := by
  apply integerChecks_of_simple 73 9 0 (dualNumerators073 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 887477428322, 296619754801, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 703380245200, 296619754801, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1144101124261, 568104470439, 1031321016287, 0, 301899777613, 1144101124262, 1048208085022, 501658405706, 1127424369963, 318576531911]) (branchResiduals073 9 0) 16350530
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck073_9_1 :
    integerResidualCheck 73 9 1 (dualNumerators073 9 1) ∧
    integerMassCheck 73 9 1 (dualNumerators073 9 1) := by
  apply integerChecks_of_simple 73 9 1 (dualNumerators073 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals073 9 1) 16350530
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck073_10_0 :
    integerResidualCheck 73 10 0 (dualNumerators073 10 0) ∧
    integerMassCheck 73 10 0 (dualNumerators073 10 0) := by
  apply integerChecks_of_simple 73 10 0 (dualNumerators073 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals073 10 0) 10683139
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck073_10_1 :
    integerResidualCheck 73 10 1 (dualNumerators073 10 1) ∧
    integerMassCheck 73 10 1 (dualNumerators073 10 1) := by
  apply integerChecks_of_simple 73 10 1 (dualNumerators073 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 560661867464, 344525275673, 0, 844525275674, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 419928145920, 344525275674, 155474724327, 844525275674, 0, 0, 1184800741849, 1308901425339, 874612019090, 434289406250, 788396879662, 0, 230788317974, 874612019090, 801306257136, 383494484713, 861863417206, 243536919859]) (branchResiduals073 10 1) 10683139
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck073_11_0 :
    integerResidualCheck 73 11 0 (dualNumerators073 11 0) ∧
    integerMassCheck 73 11 0 (dualNumerators073 11 0) := by
  apply integerChecks_of_simple 73 11 0 (dualNumerators073 11 0)
    (![301584229951, 55520807208, 301584229951, 0, 1, 453219981703, 536656503669, 0, 422847068578, 301584229950, 0, 453219981704, 546780018297, 0, 582744499174, 0, 0, 500692022794, 1015715082378, 857797059952, 467415292132, 702430462570, 467415292132, 553465130761, 453219981704, 0, 0, 546780018297, 0, 46087995504, 702430462570, 776005788302, 518529490604, 257476297698, 467415292132, 0, 136827011686, 518529490605, 475068849115, 227361613456, 510971252327, 144385249964]) (branchResiduals073 11 0) 15120968
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck073_11_1 :
    integerResidualCheck 73 11 1 (dualNumerators073 11 1) ∧
    integerMassCheck 73 11 1 (dualNumerators073 11 1) := by
  apply integerChecks_of_simple 73 11 1 (dualNumerators073 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 495684390637, 246132542200, 446822154676, 0, 130798759066, 495684390638, 454138515265, 217344634900, 488459149252, 138024000452]) (branchResiduals073 11 1) 15120968
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck073_12_0 :
    integerResidualCheck 73 12 0 (dualNumerators073 12 0) ∧
    integerMassCheck 73 12 0 (dualNumerators073 12 0) := by
  apply integerChecks_of_simple 73 12 0 (dualNumerators073 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1144101124261, 568104470439, 1031321016287, 0, 301899777613, 1144101124262, 1048208085022, 501658405706, 1127424369963, 318576531911]) (branchResiduals073 12 0) 16348076
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck073_12_1 :
    integerResidualCheck 73 12 1 (dualNumerators073 12 1) ∧
    integerMassCheck 73 12 1 (dualNumerators073 12 1) := by
  apply integerChecks_of_simple 73 12 1 (dualNumerators073 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals073 12 1) 16348076
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck073_13_0 :
    integerResidualCheck 73 13 0 (dualNumerators073 13 0) ∧
    integerMassCheck 73 13 0 (dualNumerators073 13 0) := by
  apply integerChecks_of_simple 73 13 0 (dualNumerators073 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals073 13 0) 13962901
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck073_13_1 :
    integerResidualCheck 73 13 1 (dualNumerators073 13 1) ∧
    integerMassCheck 73 13 1 (dualNumerators073 13 1) := by
  apply integerChecks_of_simple 73 13 1 (dualNumerators073 13 1)
    (![271504920046, 49983290985, 271504920046, 0, 1, 408016874475, 483131631732, 0, 380673285087, 271504920045, 408016874475, 0, 0, 16868368268, 0, 0, 450754164561, 0, 914410021623, 772242375590, 420796377646, 632371681400, 420796377646, 498263805438, 408016874475, 0, 0, 16868368268, 500000000001, 16868368269, 632371681400, 698608775208, 466812564804, 231796210404, 420796377646, 0, 123180203666, 466812564805, 427686586650, 204685094751, 460008167640, 129984600832]) (branchResiduals073 13 1) 13962901
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck073_14_0 :
    integerResidualCheck 73 14 0 (dualNumerators073 14 0) ∧
    integerMassCheck 73 14 0 (dualNumerators073 14 0) := by
  apply integerChecks_of_simple 73 14 0 (dualNumerators073 14 0)
    (![288297190339, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 0, 433252253780, 0, 0, 1079760519503, 0, 478632796615, 1, 970965240730, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253780, 0, 0, 566747746222, 0, 671483150164, 741816932837, 495684390637, 246132542200, 446822154676, 0, 130798759066, 495684390638, 454138515265, 217344634900, 488459149252, 138024000452]) (branchResiduals073 14 0) 20161291
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck073_14_1 :
    integerResidualCheck 73 14 1 (dualNumerators073 14 1) ∧
    integerMassCheck 73 14 1 (dualNumerators073 14 1) := by
  apply integerChecks_of_simple 73 14 1 (dualNumerators073 14 1)
    (![362006560060, 66644387979, 362006560061, 0, 1, 544022499300, 644175508976, 0, 507564380116, 362006560060, 544022499300, 0, 0, 355824491024, 0, 1000000000000, 601005552747, 0, 1219213362163, 1029656500786, 561061836861, 843162241867, 561061836861, 664351740584, 544022499300, 0, 0, 355824491024, 0, 355824491025, 843162241867, 931478366944, 622416753072, 309061613872, 561061836861, 0, 164240271555, 622416753073, 570248782200, 272913459667, 613344223519, 173312801109]) (branchResiduals073 14 1) 20161291
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck073_15_0 :
    integerResidualCheck 73 15 0 (dualNumerators073 15 0) ∧
    integerMassCheck 73 15 0 (dualNumerators073 15 0) := by
  apply integerChecks_of_simple 73 15 0 (dualNumerators073 15 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546385, 0, 844525275675, 602334801077, 221089960014, 684097183123, 0, 1184097183122, 1071829546385, 0, 0, 0, 2028622458796, 1713222941252, 933538524389, 1402919220983, 933538524389, 1105400337064, 905187143136, 0, 684097183123, 500000000000, 0, 0, 1402919220983, 1549866490727, 1035625628128, 514240862600, 933538524389, 0, 273275797210, 1035625628129, 948824481893, 454094739091, 1020530044549, 288371380791]) (branchResiduals073 15 0) 12900283
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck073_15_1 :
    integerResidualCheck 73 15 1 (dualNumerators073 15 1) ∧
    integerMassCheck 73 15 1 (dualNumerators073 15 1) := by
  apply integerChecks_of_simple 73 15 1 (dualNumerators073 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals073 15 1) 12900283
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck073_16_0 :
    integerResidualCheck 73 16 0 (dualNumerators073 16 0) ∧
    integerMassCheck 73 16 0 (dualNumerators073 16 0) := by
  apply integerChecks_of_simple 73 16 0 (dualNumerators073 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals073 16 0) 10683060
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck073_16_1 :
    integerResidualCheck 73 16 1 (dualNumerators073 16 1) ∧
    integerMassCheck 73 16 1 (dualNumerators073 16 1) := by
  apply integerChecks_of_simple 73 16 1 (dualNumerators073 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 0, 0, 0, 0, 1184800741849, 1308901425339, 874612019090, 434289406250, 788396879662, 0, 230788317974, 874612019090, 801306257136, 383494484713, 861863417206, 243536919859]) (branchResiduals073 16 1) 10683060
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck073_17_0 :
    integerResidualCheck 73 17 0 (dualNumerators073 17 0) ∧
    integerMassCheck 73 17 0 (dualNumerators073 17 0) := by
  apply integerChecks_of_simple 73 17 0 (dualNumerators073 17 0)
    (![275782051153, 50770698773, 275782051153, 0, 1, 414444535771, 490742607366, 0, 386670191328, 275782051153, 414444535771, 0, 0, 0, 1032887523019, 0, 0, 457855084348, 928815106981, 784407834273, 427425359826, 642333698256, 427425359826, 506113164564, 414444535771, 0, 0, 0, 0, 542144915654, 642333698256, 709614252839, 474166459319, 235447793521, 427425359826, 0, 125120713182, 474166459319, 434424113188, 207909585069, 467254869626, 132032302875]) (branchResiduals073 17 0) 15120968
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck073_17_1 :
    integerResidualCheck 73 17 1 (dualNumerators073 17 1) ∧
    integerMassCheck 73 17 1 (dualNumerators073 17 1) := by
  apply integerChecks_of_simple 73 17 1 (dualNumerators073 17 1)
    (![508686963928, 93647837150, 508686963928, 0, 1, 764453421592, 905187143136, 0, 713222941253, 508686963927, 764453421593, 0, 0, 1000000000000, 905187143136, 0, 844525275674, 0, 1713222941251, 1446860076751, 788396879661, 1184800741848, 788396879661, 933538524388, 764453421592, 1, 0, 1000000000000, 0, 0, 1184800741848, 1308901425338, 874612019089, 434289406250, 788396879661, 0, 230788317974, 874612019090, 801306257136, 383494484713, 861863417205, 243536919859]) (branchResiduals073 17 1) 15120968
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck073_18_0 :
    integerResidualCheck 73 18 0 (dualNumerators073 18 0) ∧
    integerMassCheck 73 18 0 (dualNumerators073 18 0) := by
  apply integerChecks_of_simple 73 18 0 (dualNumerators073 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 562515489548, 74022925577, 0, 476109064652, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 934970696450, 333426002978, 763999473637, 0, 136222375797, 934970696451, 772489965679, 214059593984, 835192545885, 236000526363]) (branchResiduals073 18 0) 13565580
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck073_18_1 :
    integerResidualCheck 73 18 1 (dualNumerators073 18 1) ∧
    integerMassCheck 73 18 1 (dualNumerators073 18 1) := by
  apply integerChecks_of_simple 73 18 1 (dualNumerators073 18 1)
    (![543792441172, 100110656623, 543792441172, 0, 1, 180671424657, 213932525007, 0, 71292007252, 50847095100, 88490012639, 92181412018, 0, 592902881267, 213932525007, 0, 0, 500721469250, 171249542446, 144624567044, 842805682483, 280016586907, 78806208846, 93314209907, 180671424657, 1, 92181412018, 500721469249, 0, 0, 280016586907, 776051426377, 0, 130834560290, 78806208846, 0, 110493093096, 1, 84115995539, 195900591369, 86149742858, 24343350238]) (branchResiduals073 18 1) 13565580
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck073_19_0 :
    integerResidualCheck 73 19 0 (dualNumerators073 19 0) ∧
    integerMassCheck 73 19 0 (dualNumerators073 19 0) := by
  apply integerChecks_of_simple 73 19 0 (dualNumerators073 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 216703300504, 217988955956, 0, 1402086139076, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 875874933151, 195318139098, 645216866088, 0, 28774691489, 875874933151, 648421029826, 25293932239, 705341215054, 199308409586]) (branchResiduals073 19 0) 8248658
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck073_19_1 :
    integerResidualCheck 73 19 1 (dualNumerators073 19 1) ∧
    integerMassCheck 73 19 1 (dualNumerators073 19 1) := by
  apply integerChecks_of_simple 73 19 1 (dualNumerators073 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 1, 0, 0, 0, 0, 987477735649, 0, 350406455885, 413593017753, 460183470977, 0, 294810410203, 350406455885, 475079366460, 512398369190, 503065535987, 142151330101]) (branchResiduals073 19 1) 8248658
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck073_20_0 :
    integerResidualCheck 73 20 0 (dualNumerators073 20 0) ∧
    integerMassCheck 73 20 0 (dualNumerators073 20 0) := by
  apply integerChecks_of_simple 73 20 0 (dualNumerators073 20 0)
    (![581614421967, 107073576748, 581614421967, 0, 2, 2066609823264, 2447066870339, 0, 815473519328, 581614421966, 1888845602177, 177764221089, 0, 1143364118231, 2447066870339, 0, 0, 965599897145, 1958837637558, 1654287895858, 901424703130, 3202969314486, 901424703130, 1067374451772, 2066609823264, 2, 177764221088, 965599897144, 0, 0, 3202969314486, 1496550924034, 0, 1496550924034, 901424703130, 0, 1263875081678, 1, 962160690350, 2240808624136, 985423706049, 278451375631]) (branchResiduals073 20 0) 35312013
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck073_20_1 :
    integerResidualCheck 73 20 1 (dualNumerators073 20 1) ∧
    integerMassCheck 73 20 1 (dualNumerators073 20 1) := by
  apply integerChecks_of_simple 73 20 1 (dualNumerators073 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 25837005087, 1204076434982, 564110399358, 1160334187225, 0, 0, 1344522571906, 379922014678]) (branchResiduals073 20 1) 35312013
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck073_21_0 :
    integerResidualCheck 73 21 0 (dualNumerators073 21 0) ∧
    integerMassCheck 73 21 0 (dualNumerators073 21 0) := by
  apply integerChecks_of_simple 73 21 0 (dualNumerators073 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 604293255477, 704608169863, 757887471419, 892563449519, 1020530044549, 288371380791]) (branchResiduals073 21 0) 11182451
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck073_21_1 :
    integerResidualCheck 73 21 1 (dualNumerators073 21 1) ∧
    integerMassCheck 73 21 1 (dualNumerators073 21 1) := by
  apply integerChecks_of_simple 73 21 1 (dualNumerators073 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 860003851037, 963321782180, 3460174706, 161253783489, 75547476522, 155395681176, 0, 0, 180062781238, 50880376460]) (branchResiduals073 21 1) 11182451
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck073_22_0 :
    integerResidualCheck 73 22 0 (dualNumerators073 22 0) ∧
    integerMassCheck 73 22 0 (dualNumerators073 22 0) := by
  apply integerChecks_of_simple 73 22 0 (dualNumerators073 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 583695195717, 0, 612220343875, 0, 492945346072, 0, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 583695195717, 0, 0, 0, 801336080718, 763999473637, 59391303775, 704608169863, 9067941093, 451115529884, 645216866088, 0, 19333649461, 782002431258, 503065535987, 142151330101]) (branchResiduals073 22 0) 6465674
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck073_22_1 :
    integerResidualCheck 73 22 1 (dualNumerators073 22 1) ∧
    integerMassCheck 73 22 1 (dualNumerators073 22 1) := by
  apply integerChecks_of_simple 73 22 1 (dualNumerators073 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 9522456419, 111749239332, 1534493418, 71511669319, 33503252091, 68913760194, 0, 0, 79852948501, 22564063785]) (branchResiduals073 22 1) 6465674
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck073_23_0 :
    integerResidualCheck 73 23 0 (dualNumerators073 23 0) ∧
    integerMassCheck 73 23 0 (dualNumerators073 23 0) := by
  apply integerChecks_of_simple 73 23 0 (dualNumerators073 23 0)
    (![581614421966, 107073576748, 581614421967, 0, 2, 2066609823263, 2447066870339, 0, 815473519327, 581614421966, 1888845602178, 177764221088, 0, 1143364118230, 2447066870339, 0, 0, 965599897144, 1958837637556, 1654287895857, 901424703129, 3202969314485, 901424703129, 1067374451772, 2066609823265, 0, 177764221088, 965599897143, 0, 0, 3202969314485, 1496550924032, 1000000000000, 496550924033, 901424703129, 0, 1263875081678, 0, 962160690349, 2240808624136, 985423706048, 278451375631]) (branchResiduals073 23 0) 35297932
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck073_23_1 :
    integerResidualCheck 73 23 1 (dualNumerators073 23 1) ∧
    integerMassCheck 73 23 1 (dualNumerators073 23 1) := by
  apply integerChecks_of_simple 73 23 1 (dualNumerators073 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 160334187224, 1881575790198, 25837005087, 1204076434982, 564110399358, 1160334187225, 0, 0, 1344522571906, 379922014678]) (branchResiduals073 23 1) 35297932
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck073_24_0 :
    integerResidualCheck 73 24 0 (dualNumerators073 24 0) ∧
    integerMassCheck 73 24 0 (dualNumerators073 24 0) := by
  apply integerChecks_of_simple 73 24 0 (dualNumerators073 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 276221246109, 150663467366, 0, 969054410724, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 384946583730, 686246488518, 705016048726, 601815130180, 835192545885, 236000526363]) (branchResiduals073 24 0) 9356857
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck073_24_1 :
    integerResidualCheck 73 24 1 (dualNumerators073 24 1) ∧
    integerMassCheck 73 24 1 (dualNumerators073 24 1) := by
  apply integerChecks_of_simple 73 24 1 (dualNumerators073 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 395480180778, 20824623507, 0, 133942179966, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 690777049383, 178822020994, 48434165160, 99625565721, 0, 0, 115439864933, 32619865948]) (branchResiduals073 24 1) 9356857
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck073_25_0 :
    integerResidualCheck 73 25 0 (dualNumerators073 25 0) ∧
    integerMassCheck 73 25 0 (dualNumerators073 25 0) := by
  apply integerChecks_of_simple 73 25 0 (dualNumerators073 25 0)
    (![34966365041, 6437209308, 34966365041, 0, 1, 22997469043, 27231238312, 0, 632721051475, 451271169324, 378016613693, 137926201423, 0, 887129416173, 610926434029, 0, 0, 749203214752, 1519850467647, 1283552135172, 54193197479, 35643006641, 699410063567, 828169486116, 515942815114, 1, 137926201422, 749203214751, 0, 0, 799642480277, 1161164957288, 639671999392, 521492957897, 54193197479, 0, 340961156265, 639671999393, 0, 35643006641, 764584390126, 216048765531]) (branchResiduals073 25 0) 8671199
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck073_25_1 :
    integerResidualCheck 73 25 1 (dualNumerators073 25 1) ∧
    integerMassCheck 73 25 1 (dualNumerators073 25 1) := by
  apply integerChecks_of_simple 73 25 1 (dualNumerators073 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals073 25 1) 8671199
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck073_26_0 :
    integerResidualCheck 73 26 0 (dualNumerators073 26 0) ∧
    integerMassCheck 73 26 0 (dualNumerators073 26 0) := by
  apply integerChecks_of_simple 73 26 0 (dualNumerators073 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals073 26 0) 15099566
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck073_26_1 :
    integerResidualCheck 73 26 1 (dualNumerators073 26 1) ∧
    integerMassCheck 73 26 1 (dualNumerators073 26 1) := by
  apply integerChecks_of_simple 73 26 1 (dualNumerators073 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 1025837005087, 204076434982, 564110399358, 1160334187225, 0, 0, 1344522571906, 379922014678]) (branchResiduals073 26 1) 15099566
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck073_27_0 :
    integerResidualCheck 73 27 0 (dualNumerators073 27 0) ∧
    integerMassCheck 73 27 0 (dualNumerators073 27 0) := by
  apply integerChecks_of_simple 73 27 0 (dualNumerators073 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312724, 1, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 436855949686, 304617712691, 595678484088, 168320989550]) (branchResiduals073 27 0) 7338775
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck073_27_1 :
    integerResidualCheck 73 27 1 (dualNumerators073 27 1) ∧
    integerMassCheck 73 27 1 (dualNumerators073 27 1) := by
  apply integerChecks_of_simple 73 27 1 (dualNumerators073 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 234337221023, 181967583262, 0, 1170399780726, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 908602750628, 623335190581, 377837583379, 0, 385157561486, 908602750628, 385949753226, 259267112862, 413046270426, 116714568052]) (branchResiduals073 27 1) 7338775
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck073_28_0 :
    integerResidualCheck 73 28 0 (dualNumerators073 28 0) ∧
    integerMassCheck 73 28 0 (dualNumerators073 28 0) := by
  apply integerChecks_of_simple 73 28 0 (dualNumerators073 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 1, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 374399059503, 471423145846, 503065535987, 142151330101]) (branchResiduals073 28 0) 10335557
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck073_28_1 :
    integerResidualCheck 73 28 1 (dualNumerators073 28 1) ∧
    integerMassCheck 73 28 1 (dualNumerators073 28 1) := by
  apply integerChecks_of_simple 73 28 1 (dualNumerators073 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 426731607120, 507685338329, 2156352207, 100492021777, 362407121329, 426731607121, 0, 0, 112213633330, 31708229033]) (branchResiduals073 28 1) 10335557
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck073_29_0 :
    integerResidualCheck 73 29 0 (dualNumerators073 29 0) ∧
    integerMassCheck 73 29 0 (dualNumerators073 29 0) := by
  apply integerChecks_of_simple 73 29 0 (dualNumerators073 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals073 29 0) 40352153
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck073_29_1 :
    integerResidualCheck 73 29 1 (dualNumerators073 29 1) ∧
    integerMassCheck 73 29 1 (dualNumerators073 29 1) := by
  apply integerChecks_of_simple 73 29 1 (dualNumerators073 29 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 160334187224, 1881575790198, 25837005087, 1204076434982, 1564110399358, 160334187225, 0, 0, 1344522571906, 379922014678]) (branchResiduals073 29 1) 40352153
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck073_30_0 :
    integerResidualCheck 73 30 0 (dualNumerators073 30 0) ∧
    integerMassCheck 73 30 0 (dualNumerators073 30 0) := by
  apply integerChecks_of_simple 73 30 0 (dualNumerators073 30 0)
    (![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 77683757550, 37915592377, 0, 243869815754, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 1, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 199771188218, 119430361220, 178745918050, 13520283734, 69802588317, 199771188218, 179163558800, 0, 269573776534, 0]) (branchResiduals073 30 0) 7680628
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck073_30_1 :
    integerResidualCheck 73 30 1 (dualNumerators073 30 1) ∧
    integerMassCheck 73 30 1 (dualNumerators073 30 1) := by
  apply integerChecks_of_simple 73 30 1 (dualNumerators073 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 491724510490, 107456641334, 0, 691151837050, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 604489703699, 300159920941, 544901951702, 0, 159509769938, 604489703700, 556554858415, 372095930671, 536287180313, 227712293325]) (branchResiduals073 30 1) 7680628
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck073_31_0 :
    integerResidualCheck 73 31 0 (dualNumerators073 31 0) ∧
    integerMassCheck 73 31 0 (dualNumerators073 31 0) := by
  apply integerChecks_of_simple 73 31 0 (dualNumerators073 31 0)
    (![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1719079079316, 0, 231835083176, 1259308150412, 2035556695381, 0, 0, 1259308150414, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079315, 2, 231835083174, 1259308150413, 0, 0, 2664343059941, 1951759503826, 0, 1951759503826, 743462473285, 1537550536267, 1648310233016, 2, 761819131890, 1902523928052, 1648310233018, 0]) (branchResiduals073 31 0) 32891612
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck073_31_1 :
    integerResidualCheck 73 31 1 (dualNumerators073 31 1) ∧
    integerMassCheck 73 31 1 (dualNumerators073 31 1) := by
  apply integerChecks_of_simple 73 31 1 (dualNumerators073 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 274671058114, 217988955956, 0, 1402086139076, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 556963843680, 992902647048, 18993131489, 744564115640, 845258320866, 704608169862]) (branchResiduals073 31 1) 32891612
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck073_32_0 :
    integerResidualCheck 73 32 0 (dualNumerators073 32 0) ∧
    integerMassCheck 73 32 0 (dualNumerators073 32 0) := by
  apply integerChecks_of_simple 73 32 0 (dualNumerators073 32 0)
    (![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 979882959195, 1099655708204, 1160276651773, 0, 382837210862, 2079538667397, 0, 979882959196, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 180393692578, 979882959195, 0, 0, 3223007296772, 1518687763292, 100033413308, 1418654349984, 0, 914758491801, 1182536788648, 100033413309, 60954317499, 3162052979273, 0, 1282570201956]) (branchResiduals073 32 0) 67647473
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck073_32_1 :
    integerResidualCheck 73 32 1 (dualNumerators073 32 1) ∧
    integerMassCheck 73 32 1 (dualNumerators073 32 1) := by
  apply integerChecks_of_simple 73 32 1 (dualNumerators073 32 1)
    (![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1307998858623, 638403098873, 0, 4106153599144, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957494, 2, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 3363643757916, 2010906540662, 3009631152853, 227647532122, 1175299814610, 3363643757919, 3016663171407, 0, 4538943572529, 0]) (branchResiduals073 32 1) 67647473
    branchSparseDots073 branchIntegerCurvature073 branchDots073
    branchIntegerCurvature073_entry rfl
    (congrFun (congrFun branchResiduals073_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks073 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 73 j s (dualNumerators073 j s) ∧
    integerMassCheck 73 j s (dualNumerators073 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck073_0_0
    · exact integerCheck073_0_1
  · fin_cases s
    · exact integerCheck073_1_0
    · exact integerCheck073_1_1
  · fin_cases s
    · exact integerCheck073_2_0
    · exact integerCheck073_2_1
  · fin_cases s
    · exact integerCheck073_3_0
    · exact integerCheck073_3_1
  · fin_cases s
    · exact integerCheck073_4_0
    · exact integerCheck073_4_1
  · fin_cases s
    · exact integerCheck073_5_0
    · exact integerCheck073_5_1
  · fin_cases s
    · exact integerCheck073_6_0
    · exact integerCheck073_6_1
  · fin_cases s
    · exact integerCheck073_7_0
    · exact integerCheck073_7_1
  · fin_cases s
    · exact integerCheck073_8_0
    · exact integerCheck073_8_1
  · fin_cases s
    · exact integerCheck073_9_0
    · exact integerCheck073_9_1
  · fin_cases s
    · exact integerCheck073_10_0
    · exact integerCheck073_10_1
  · fin_cases s
    · exact integerCheck073_11_0
    · exact integerCheck073_11_1
  · fin_cases s
    · exact integerCheck073_12_0
    · exact integerCheck073_12_1
  · fin_cases s
    · exact integerCheck073_13_0
    · exact integerCheck073_13_1
  · fin_cases s
    · exact integerCheck073_14_0
    · exact integerCheck073_14_1
  · fin_cases s
    · exact integerCheck073_15_0
    · exact integerCheck073_15_1
  · fin_cases s
    · exact integerCheck073_16_0
    · exact integerCheck073_16_1
  · fin_cases s
    · exact integerCheck073_17_0
    · exact integerCheck073_17_1
  · fin_cases s
    · exact integerCheck073_18_0
    · exact integerCheck073_18_1
  · fin_cases s
    · exact integerCheck073_19_0
    · exact integerCheck073_19_1
  · fin_cases s
    · exact integerCheck073_20_0
    · exact integerCheck073_20_1
  · fin_cases s
    · exact integerCheck073_21_0
    · exact integerCheck073_21_1
  · fin_cases s
    · exact integerCheck073_22_0
    · exact integerCheck073_22_1
  · fin_cases s
    · exact integerCheck073_23_0
    · exact integerCheck073_23_1
  · fin_cases s
    · exact integerCheck073_24_0
    · exact integerCheck073_24_1
  · fin_cases s
    · exact integerCheck073_25_0
    · exact integerCheck073_25_1
  · fin_cases s
    · exact integerCheck073_26_0
    · exact integerCheck073_26_1
  · fin_cases s
    · exact integerCheck073_27_0
    · exact integerCheck073_27_1
  · fin_cases s
    · exact integerCheck073_28_0
    · exact integerCheck073_28_1
  · fin_cases s
    · exact integerCheck073_29_0
    · exact integerCheck073_29_1
  · fin_cases s
    · exact integerCheck073_30_0
    · exact integerCheck073_30_1
  · fin_cases s
    · exact integerCheck073_31_0
    · exact integerCheck073_31_1
  · fin_cases s
    · exact integerCheck073_32_0
    · exact integerCheck073_32_1

end ElevenSquare.Tasks.T06
