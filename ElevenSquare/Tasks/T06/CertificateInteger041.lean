import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual041
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
import ElevenSquare.Tasks.T06.SparseColumn24
import ElevenSquare.Tasks.T06.SparseColumn25
import ElevenSquare.Tasks.T06.SparseColumn27
import ElevenSquare.Tasks.T06.SparseColumn28
import ElevenSquare.Tasks.T06.SparseColumn30
import ElevenSquare.Tasks.T06.SparseColumn31
import ElevenSquare.Tasks.T06.SparseColumn32
import ElevenSquare.Tasks.T06.SparseColumn33
import ElevenSquare.Tasks.T06.SparseColumn34
import ElevenSquare.Tasks.T06.SparseColumn44
import ElevenSquare.Tasks.T06.SparseColumn45
import ElevenSquare.Tasks.T06.SparseColumn52
import ElevenSquare.Tasks.T06.SparseColumn53

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix041 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral28, roundedGradientLiteral42, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix041_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = branchIntegerMatrix041 := by
  change roundedGradients ∘ branchRows 41 = branchIntegerMatrix041
  rw [show branchRows 41 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 34, 35, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral28_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral42_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, branchIntegerMatrix041]

theorem branchColumn041_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 0) i) = _
  rw [branchColumn041_0]
  exact sparseColumn00_sum n

theorem branchColumn041_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 1) i) = _
  rw [branchColumn041_1]
  exact sparseColumn01_sum n

theorem branchColumn041_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 2) i) = _
  rw [branchColumn041_2]
  exact sparseColumn02_sum n

theorem branchColumn041_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 3) i) = _
  rw [branchColumn041_3]
  exact sparseColumn03_sum n

theorem branchColumn041_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 4) i) = _
  rw [branchColumn041_4]
  exact sparseColumn04_sum n

theorem branchColumn041_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 5) i) = _
  rw [branchColumn041_5]
  exact sparseColumn05_sum n

theorem branchColumn041_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 6) i) = _
  rw [branchColumn041_6]
  exact sparseColumn06_sum n

theorem branchColumn041_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 7) i) = _
  rw [branchColumn041_7]
  exact sparseColumn07_sum n

theorem branchColumn041_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 8) i) = _
  rw [branchColumn041_8]
  exact sparseColumn08_sum n

theorem branchColumn041_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 9) i) = _
  rw [branchColumn041_9]
  exact sparseColumn09_sum n

theorem branchColumn041_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 10) i) = _
  rw [branchColumn041_10]
  exact sparseColumn10_sum n

theorem branchColumn041_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 11) i) = _
  rw [branchColumn041_11]
  exact sparseColumn11_sum n

theorem branchColumn041_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 12) = sparseColumn12 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 12) = sparseDot12 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 12) i) = _
  rw [branchColumn041_12]
  exact sparseColumn12_sum n

theorem branchColumn041_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 13) = sparseColumn13 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 13) = sparseDot13 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 13) i) = _
  rw [branchColumn041_13]
  exact sparseColumn13_sum n

theorem branchColumn041_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 14) = sparseColumn33 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 14) = sparseDot33 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 14) i) = _
  rw [branchColumn041_14]
  exact sparseColumn33_sum n

theorem branchColumn041_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 15) = sparseColumn15 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 15) = sparseDot15 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 15) i) = _
  rw [branchColumn041_15]
  exact sparseColumn15_sum n

theorem branchColumn041_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 16) = sparseColumn16 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 16) = sparseDot16 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 16) i) = _
  rw [branchColumn041_16]
  exact sparseColumn16_sum n

theorem branchColumn041_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 17) = sparseColumn34 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 17) = sparseDot34 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 17) i) = _
  rw [branchColumn041_17]
  exact sparseColumn34_sum n

theorem branchColumn041_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 18) i) = _
  rw [branchColumn041_18]
  exact sparseColumn18_sum n

theorem branchColumn041_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 19) i) = _
  rw [branchColumn041_19]
  exact sparseColumn19_sum n

theorem branchColumn041_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 20) = sparseColumn52 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 20) = sparseDot52 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 20) i) = _
  rw [branchColumn041_20]
  exact sparseColumn52_sum n

theorem branchColumn041_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 21) i) = _
  rw [branchColumn041_21]
  exact sparseColumn21_sum n

theorem branchColumn041_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 22) i) = _
  rw [branchColumn041_22]
  exact sparseColumn22_sum n

theorem branchColumn041_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 23) = sparseColumn53 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 23) = sparseDot53 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 23) i) = _
  rw [branchColumn041_23]
  exact sparseColumn53_sum n

theorem branchColumn041_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 24) i) = _
  rw [branchColumn041_24]
  exact sparseColumn24_sum n

theorem branchColumn041_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 25) i) = _
  rw [branchColumn041_25]
  exact sparseColumn25_sum n

theorem branchColumn041_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 26) = sparseColumn44 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 26) = sparseDot44 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 26) i) = _
  rw [branchColumn041_26]
  exact sparseColumn44_sum n

theorem branchColumn041_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 27) i) = _
  rw [branchColumn041_27]
  exact sparseColumn27_sum n

theorem branchColumn041_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 28) i) = _
  rw [branchColumn041_28]
  exact sparseColumn28_sum n

theorem branchColumn041_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 29) = sparseColumn45 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 29) = sparseDot45 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 29) i) = _
  rw [branchColumn041_29]
  exact sparseColumn45_sum n

theorem branchColumn041_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 30) i) = _
  rw [branchColumn041_30]
  exact sparseColumn30_sum n

theorem branchColumn041_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 31) i) = _
  rw [branchColumn041_31]
  exact sparseColumn31_sum n

theorem branchColumn041_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 41 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 41 i)) = _
  rw [branchIntegerMatrix041_eq]
  simp only [branchIntegerMatrix041, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot041_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 41 i) 32) i) = _
  rw [branchColumn041_32]
  exact sparseColumn32_sum n

def branchSparseDots041 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot12, sparseDot13, sparseDot33, sparseDot15, sparseDot16, sparseDot34, sparseDot18, sparseDot19, sparseDot52, sparseDot21, sparseDot22, sparseDot53, sparseDot24, sparseDot25, sparseDot44, sparseDot27, sparseDot28, sparseDot45, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot041_0 :
    branchSparseDots041 0 = sparseDot00 := rfl

private theorem branchSparseDot041_1 :
    branchSparseDots041 1 = sparseDot01 := rfl

private theorem branchSparseDot041_2 :
    branchSparseDots041 2 = sparseDot02 := rfl

private theorem branchSparseDot041_3 :
    branchSparseDots041 3 = sparseDot03 := rfl

private theorem branchSparseDot041_4 :
    branchSparseDots041 4 = sparseDot04 := rfl

private theorem branchSparseDot041_5 :
    branchSparseDots041 5 = sparseDot05 := rfl

private theorem branchSparseDot041_6 :
    branchSparseDots041 6 = sparseDot06 := rfl

private theorem branchSparseDot041_7 :
    branchSparseDots041 7 = sparseDot07 := rfl

private theorem branchSparseDot041_8 :
    branchSparseDots041 8 = sparseDot08 := rfl

private theorem branchSparseDot041_9 :
    branchSparseDots041 9 = sparseDot09 := rfl

private theorem branchSparseDot041_10 :
    branchSparseDots041 10 = sparseDot10 := rfl

private theorem branchSparseDot041_11 :
    branchSparseDots041 11 = sparseDot11 := rfl

private theorem branchSparseDot041_12 :
    branchSparseDots041 12 = sparseDot12 := rfl

private theorem branchSparseDot041_13 :
    branchSparseDots041 13 = sparseDot13 := rfl

private theorem branchSparseDot041_14 :
    branchSparseDots041 14 = sparseDot33 := rfl

private theorem branchSparseDot041_15 :
    branchSparseDots041 15 = sparseDot15 := rfl

private theorem branchSparseDot041_16 :
    branchSparseDots041 16 = sparseDot16 := rfl

private theorem branchSparseDot041_17 :
    branchSparseDots041 17 = sparseDot34 := rfl

private theorem branchSparseDot041_18 :
    branchSparseDots041 18 = sparseDot18 := rfl

private theorem branchSparseDot041_19 :
    branchSparseDots041 19 = sparseDot19 := rfl

private theorem branchSparseDot041_20 :
    branchSparseDots041 20 = sparseDot52 := rfl

private theorem branchSparseDot041_21 :
    branchSparseDots041 21 = sparseDot21 := rfl

private theorem branchSparseDot041_22 :
    branchSparseDots041 22 = sparseDot22 := rfl

private theorem branchSparseDot041_23 :
    branchSparseDots041 23 = sparseDot53 := rfl

private theorem branchSparseDot041_24 :
    branchSparseDots041 24 = sparseDot24 := rfl

private theorem branchSparseDot041_25 :
    branchSparseDots041 25 = sparseDot25 := rfl

private theorem branchSparseDot041_26 :
    branchSparseDots041 26 = sparseDot44 := rfl

private theorem branchSparseDot041_27 :
    branchSparseDots041 27 = sparseDot27 := rfl

private theorem branchSparseDot041_28 :
    branchSparseDots041 28 = sparseDot28 := rfl

private theorem branchSparseDot041_29 :
    branchSparseDots041 29 = sparseDot45 := rfl

private theorem branchSparseDot041_30 :
    branchSparseDots041 30 = sparseDot30 := rfl

private theorem branchSparseDot041_31 :
    branchSparseDots041 31 = sparseDot31 := rfl

private theorem branchSparseDot041_32 :
    branchSparseDots041 32 = sparseDot32 := rfl

theorem branchDots041 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 41 i) k) = branchSparseDots041 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot041_0 n
      _ = _ := congrFun branchSparseDot041_0.symm n
  · calc
      _ = sparseDot01 n := branchDot041_1 n
      _ = _ := congrFun branchSparseDot041_1.symm n
  · calc
      _ = sparseDot02 n := branchDot041_2 n
      _ = _ := congrFun branchSparseDot041_2.symm n
  · calc
      _ = sparseDot03 n := branchDot041_3 n
      _ = _ := congrFun branchSparseDot041_3.symm n
  · calc
      _ = sparseDot04 n := branchDot041_4 n
      _ = _ := congrFun branchSparseDot041_4.symm n
  · calc
      _ = sparseDot05 n := branchDot041_5 n
      _ = _ := congrFun branchSparseDot041_5.symm n
  · calc
      _ = sparseDot06 n := branchDot041_6 n
      _ = _ := congrFun branchSparseDot041_6.symm n
  · calc
      _ = sparseDot07 n := branchDot041_7 n
      _ = _ := congrFun branchSparseDot041_7.symm n
  · calc
      _ = sparseDot08 n := branchDot041_8 n
      _ = _ := congrFun branchSparseDot041_8.symm n
  · calc
      _ = sparseDot09 n := branchDot041_9 n
      _ = _ := congrFun branchSparseDot041_9.symm n
  · calc
      _ = sparseDot10 n := branchDot041_10 n
      _ = _ := congrFun branchSparseDot041_10.symm n
  · calc
      _ = sparseDot11 n := branchDot041_11 n
      _ = _ := congrFun branchSparseDot041_11.symm n
  · calc
      _ = sparseDot12 n := branchDot041_12 n
      _ = _ := congrFun branchSparseDot041_12.symm n
  · calc
      _ = sparseDot13 n := branchDot041_13 n
      _ = _ := congrFun branchSparseDot041_13.symm n
  · calc
      _ = sparseDot33 n := branchDot041_14 n
      _ = _ := congrFun branchSparseDot041_14.symm n
  · calc
      _ = sparseDot15 n := branchDot041_15 n
      _ = _ := congrFun branchSparseDot041_15.symm n
  · calc
      _ = sparseDot16 n := branchDot041_16 n
      _ = _ := congrFun branchSparseDot041_16.symm n
  · calc
      _ = sparseDot34 n := branchDot041_17 n
      _ = _ := congrFun branchSparseDot041_17.symm n
  · calc
      _ = sparseDot18 n := branchDot041_18 n
      _ = _ := congrFun branchSparseDot041_18.symm n
  · calc
      _ = sparseDot19 n := branchDot041_19 n
      _ = _ := congrFun branchSparseDot041_19.symm n
  · calc
      _ = sparseDot52 n := branchDot041_20 n
      _ = _ := congrFun branchSparseDot041_20.symm n
  · calc
      _ = sparseDot21 n := branchDot041_21 n
      _ = _ := congrFun branchSparseDot041_21.symm n
  · calc
      _ = sparseDot22 n := branchDot041_22 n
      _ = _ := congrFun branchSparseDot041_22.symm n
  · calc
      _ = sparseDot53 n := branchDot041_23 n
      _ = _ := congrFun branchSparseDot041_23.symm n
  · calc
      _ = sparseDot24 n := branchDot041_24 n
      _ = _ := congrFun branchSparseDot041_24.symm n
  · calc
      _ = sparseDot25 n := branchDot041_25 n
      _ = _ := congrFun branchSparseDot041_25.symm n
  · calc
      _ = sparseDot44 n := branchDot041_26 n
      _ = _ := congrFun branchSparseDot041_26.symm n
  · calc
      _ = sparseDot27 n := branchDot041_27 n
      _ = _ := congrFun branchSparseDot041_27.symm n
  · calc
      _ = sparseDot28 n := branchDot041_28 n
      _ = _ := congrFun branchSparseDot041_28.symm n
  · calc
      _ = sparseDot45 n := branchDot041_29 n
      _ = _ := congrFun branchSparseDot041_29.symm n
  · calc
      _ = sparseDot30 n := branchDot041_30 n
      _ = _ := congrFun branchSparseDot041_30.symm n
  · calc
      _ = sparseDot31 n := branchDot041_31 n
      _ = _ := congrFun branchSparseDot041_31.symm n
  · calc
      _ = sparseDot32 n := branchDot041_32 n
      _ = _ := congrFun branchSparseDot041_32.symm n

def branchIntegerCurvature041 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101955390, 101955390, 44932602, 44932602, 115699695, 115699695, 88123140, 88123140, 204734428, 204734428]

theorem branchIntegerCurvature041_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 41 i)) = branchIntegerCurvature041 := by
  change curvatureNumerators ∘ branchRows 41 = branchIntegerCurvature041
  rw [show branchRows 41 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 34, 35, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature041_entry (i : Fin 42) :
    curvatureNumerators (branchRows 41 i) = branchIntegerCurvature041 i :=
  congrFun branchIntegerCurvature041_eq i

def branchResiduals041 : Fin 33 → Fin 2 → ℕ := ![![1301447592154059, 33000000000000], ![1544665193933912, 33000000000000], ![1583394030459660, 1338015587232531], ![33000000000000, 1023659975168347], ![855520321020789, 33000000000000], ![1054809807837484, 892138604345179], ![724995409792713, 622122527367398], ![33000000000000, 759802416544043], ![1578949874552363, 1129555909982049], ![1025318157806699, 33000000000000], ![33000000000000, 778533855898330], ![482185299944744, 465692607595900], ![989159975168347, 66000000000000], ![33000000000000, 410944121240206], ![465048216115688, 578088261942029], ![926011512869311, 33000000000000], ![66000000000000, 744628813252447], ![445812402866454, 811054504375535], ![620645736811204, 247946712911351], ![631064931697397, 512598396342732], ![1231419309971632, 952262476725451], ![754748557282293, 388883262710236], ![469818346763073, 105297405644388], ![1230919309971599, 952262476725451], ![669446766784002, 230466723420330], ![504894193304050, 223581994926723], ![398970616796057, 856050208658842], ![409028509487699, 550488936910950], ![285695880026063, 311552136715899], ![398970616796057, 952262476725451], ![217994585943459, 556178156509698], ![1682722015279290, 651377065214029], ![1328162455871842, 2881333759689713]]

theorem branchResiduals041_eq : residualNumerators 41 = branchResiduals041 := rfl

theorem integerCheck041_0_0 :
    integerResidualCheck 41 0 0 (dualNumerators041 0 0) ∧
    integerMassCheck 41 0 0 (dualNumerators041 0 0) := by
  apply integerChecks_of_simple 41 0 0 (dualNumerators041 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1011030237961, 258120108700, 0, 1660206247774, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 511481744370, 1661564579697, 1308901425339, 0, 227681483087, 1607511062798, 1485808378804, 481205215181, 1430871029972, 404321515913]) (branchResiduals041 0 0) 18767167
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck041_0_1 :
    integerResidualCheck 41 0 1 (dualNumerators041 0 1) ∧
    integerMassCheck 41 0 1 (dualNumerators041 0 1) := by
  apply integerChecks_of_simple 41 0 1 (dualNumerators041 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals041 0 1) 18767167
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck041_1_0 :
    integerResidualCheck 41 1 0 (dualNumerators041 1 0) ∧
    integerMassCheck 41 1 0 (dualNumerators041 1 0) := by
  apply integerChecks_of_simple 41 1 0 (dualNumerators041 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1197158056821, 305639293618, 0, 1965845541389, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 605644092726, 1967453938394, 1549866490727, 0, 269597002772, 1903449321295, 1759341515999, 569793739799, 1694290356000, 478755968067]) (branchResiduals041 1 0) 22176635
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck041_1_1 :
    integerResidualCheck 41 1 1 (dualNumerators041 1 1) ∧
    integerMassCheck 41 1 1 (dualNumerators041 1 1) := by
  apply integerChecks_of_simple 41 1 1 (dualNumerators041 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals041 1 1) 22176635
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck041_2_0 :
    integerResidualCheck 41 2 0 (dualNumerators041 2 0) ∧
    integerMassCheck 41 2 0 (dualNumerators041 2 0) := by
  apply integerChecks_of_simple 41 2 0 (dualNumerators041 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1197158056822, 305639293619, 0, 1965845541391, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 605644092727, 1967453938395, 1549866490728, 0, 269597002773, 1903449321296, 1759341516001, 569793739799, 1694290356001, 478755968068]) (branchResiduals041 2 0) 22681452
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck041_2_1 :
    integerResidualCheck 41 2 1 (dualNumerators041 2 1) ∧
    integerMassCheck 41 2 1 (dualNumerators041 2 1) := by
  apply integerChecks_of_simple 41 2 1 (dualNumerators041 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1011030237961, 258120108700, 0, 1660206247773, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 511481744370, 1661564579696, 1308901425338, 0, 227681483087, 1607511062796, 1485808378803, 481205215180, 1430871029971, 404321515912]) (branchResiduals041 2 1) 22681452
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck041_3_0 :
    integerResidualCheck 41 3 0 (dualNumerators041 3 0) ∧
    integerMassCheck 41 3 0 (dualNumerators041 3 0) := by
  apply integerChecks_of_simple 41 3 0 (dualNumerators041 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals041 3 0) 16360330
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck041_3_1 :
    integerResidualCheck 41 3 1 (dualNumerators041 3 1) ∧
    integerMassCheck 41 3 1 (dualNumerators041 3 1) := by
  apply integerChecks_of_simple 41 3 1 (dualNumerators041 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 796619754801, 203380245200, 0, 1308124173107, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 403011152868, 1309194441832, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 1127424369963, 318576531911]) (branchResiduals041 3 1) 16360330
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck041_4_0 :
    integerResidualCheck 41 4 0 (dualNumerators041 4 0) ∧
    integerMassCheck 41 4 0 (dualNumerators041 4 0) := by
  apply integerChecks_of_simple 41 4 0 (dualNumerators041 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 672765518030, 171759757645, 0, 1104743927909, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 340353104975, 1105647796899, 870976665588, 0, 151505113461, 1069679196819, 988695101419, 320206323920, 952138376845, 269045933435]) (branchResiduals041 4 0) 13760362
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck041_4_1 :
    integerResidualCheck 41 4 1 (dualNumerators041 4 1) ∧
    integerMassCheck 41 4 1 (dualNumerators041 4 1) := by
  apply integerChecks_of_simple 41 4 1 (dualNumerators041 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals041 4 1) 13760362
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck041_5_0 :
    integerResidualCheck 41 5 0 (dualNumerators041 5 0) ∧
    integerMassCheck 41 5 0 (dualNumerators041 5 0) := by
  apply integerChecks_of_simple 41 5 0 (dualNumerators041 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 796619754801, 203380245201, 0, 1308124173108, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000000, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 403011152868, 1309194441833, 1031321016288, 0, 179396778078, 1266604123797, 1170711084557, 379155406172, 1127424369964, 318576531911]) (branchResiduals041 5 0) 17641130
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck041_5_1 :
    integerResidualCheck 41 5 1 (dualNumerators041 5 1) ∧
    integerMassCheck 41 5 1 (dualNumerators041 5 1) := by
  apply integerChecks_of_simple 41 5 1 (dualNumerators041 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 340353104975, 1105647796898, 870976665588, 0, 151505113461, 1069679196818, 988695101418, 320206323920, 952138376844, 269045933435]) (branchResiduals041 5 1) 17641130
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck041_6_0 :
    integerResidualCheck 41 6 0 (dualNumerators041 6 0) ∧
    integerMassCheck 41 6 0 (dualNumerators041 6 0) := by
  apply integerChecks_of_simple 41 6 0 (dualNumerators041 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 0, 70552396879, 187567711821, 1472638535954, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 1, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 659499318402, 1175693227483, 2719950702, 106626845062, 1430871029972, 404321515913]) (branchResiduals041 6 0) 8962451
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck041_6_1 :
    integerResidualCheck 41 6 1 (dualNumerators041 6 1) ∧
    integerMassCheck 41 6 1 (dualNumerators041 6 1) := by
  apply integerChecks_of_simple 41 6 1 (dualNumerators041 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949782, 1, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals041 6 1) 8962451
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck041_7_0 :
    integerResidualCheck 41 7 0 (dualNumerators041 7 0) ∧
    integerMassCheck 41 7 0 (dualNumerators041 7 0) := by
  apply integerChecks_of_simple 41 7 0 (dualNumerators041 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals041 7 0) 10424794
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck041_7_1 :
    integerResidualCheck 41 7 1 (dualNumerators041 7 1) ∧
    integerMassCheck 41 7 1 (dualNumerators041 7 1) := by
  apply integerChecks_of_simple 41 7 1 (dualNumerators041 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 598579028412, 152819646809, 0, 982922770697, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 302822046364, 983726969199, 774933245365, 0, 134798501387, 951724660649, 879670758001, 284896869900, 847145178002, 239377984034]) (branchResiduals041 7 1) 10424794
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck041_8_0 :
    integerResidualCheck 41 8 0 (dualNumerators041 8 0) ∧
    integerMassCheck 41 8 0 (dualNumerators041 8 0) := by
  apply integerChecks_of_simple 41 8 0 (dualNumerators041 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1197158056824, 305639293618, 0, 1965845541393, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 605644092727, 1967453938397, 1549866490730, 0, 269597002773, 1903449321298, 1759341516002, 569793739800, 1694290356003, 478755968068]) (branchResiduals041 8 0) 22681452
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck041_8_1 :
    integerResidualCheck 41 8 1 (dualNumerators041 8 1) ∧
    integerMassCheck 41 8 1 (dualNumerators041 8 1) := by
  apply integerChecks_of_simple 41 8 1 (dualNumerators041 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590429, 217988955956, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546384, 0, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 431959261166, 1403233284717, 1105400337063, 0, 192282767270, 1357583723456, 1254802730706, 406389967006, 1208406751039, 341459739686]) (branchResiduals041 8 1) 22681452
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck041_9_0 :
    integerResidualCheck 41 9 0 (dualNumerators041 9 0) ∧
    integerMassCheck 41 9 0 (dualNumerators041 9 0) := by
  apply integerChecks_of_simple 41 9 0 (dualNumerators041 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 887477428322, 296619754801, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 703380245200, 296619754801, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 403011152868, 1309194441832, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 1127424369963, 318576531911]) (branchResiduals041 9 0) 16350530
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck041_9_1 :
    integerResidualCheck 41 9 1 (dualNumerators041 9 1) ∧
    integerMassCheck 41 9 1 (dualNumerators041 9 1) := by
  apply integerChecks_of_simple 41 9 1 (dualNumerators041 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals041 9 1) 16350530
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck041_10_0 :
    integerResidualCheck 41 10 0 (dualNumerators041 10 0) ∧
    integerMassCheck 41 10 0 (dualNumerators041 10 0) := by
  apply integerChecks_of_simple 41 10 0 (dualNumerators041 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals041 10 0) 10683139
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck041_10_1 :
    integerResidualCheck 41 10 1 (dualNumerators041 10 1) ∧
    integerMassCheck 41 10 1 (dualNumerators041 10 1) := by
  apply integerChecks_of_simple 41 10 1 (dualNumerators041 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 560661867464, 344525275673, 0, 844525275674, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 419928145920, 344525275674, 155474724327, 844525275674, 0, 0, 1184800741849, 1308901425339, 308083254750, 1000818170589, 788396879662, 0, 137140480825, 968259856240, 894954094286, 289846647564, 861863417206, 243536919859]) (branchResiduals041 10 1) 10683139
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck041_11_0 :
    integerResidualCheck 41 11 0 (dualNumerators041 11 0) ∧
    integerMassCheck 41 11 0 (dualNumerators041 11 0) := by
  apply integerChecks_of_simple 41 11 0 (dualNumerators041 11 0)
    (![301584229951, 55520807208, 301584229951, 0, 1, 453219981703, 536656503669, 0, 422847068578, 301584229950, 0, 453219981704, 546780018297, 0, 582744499174, 0, 0, 500692022794, 1015715082378, 857797059952, 467415292132, 702430462570, 467415292132, 553465130761, 453219981704, 0, 0, 546780018297, 0, 46087995504, 702430462570, 776005788302, 182652707329, 593353080973, 467415292132, 0, 81306204478, 574050297812, 530589656322, 171840806248, 510971252327, 144385249964]) (branchResiduals041 11 0) 15120968
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck041_11_1 :
    integerResidualCheck 41 11 1 (dualNumerators041 11 1) ∧
    integerMassCheck 41 11 1 (dualNumerators041 11 1) := by
  apply integerChecks_of_simple 41 11 1 (dualNumerators041 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 174605490278, 567211442559, 446822154676, 0, 77724058423, 548759091281, 507213215908, 164269934257, 488459149252, 138024000452]) (branchResiduals041 11 1) 15120968
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck041_12_0 :
    integerResidualCheck 41 12 0 (dualNumerators041 12 0) ∧
    integerMassCheck 41 12 0 (dualNumerators041 12 0) := by
  apply integerChecks_of_simple 41 12 0 (dualNumerators041 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 403011152868, 1309194441832, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 1127424369963, 318576531911]) (branchResiduals041 12 0) 16348076
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck041_12_1 :
    integerResidualCheck 41 12 1 (dualNumerators041 12 1) ∧
    integerMassCheck 41 12 1 (dualNumerators041 12 1) := by
  apply integerChecks_of_simple 41 12 1 (dualNumerators041 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals041 12 1) 16348076
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck041_13_0 :
    integerResidualCheck 41 13 0 (dualNumerators041 13 0) ∧
    integerMassCheck 41 13 0 (dualNumerators041 13 0) := by
  apply integerChecks_of_simple 41 13 0 (dualNumerators041 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals041 13 0) 13962901
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck041_13_1 :
    integerResidualCheck 41 13 1 (dualNumerators041 13 1) ∧
    integerMassCheck 41 13 1 (dualNumerators041 13 1) := by
  apply integerChecks_of_simple 41 13 1 (dualNumerators041 13 1)
    (![271504920046, 49983290985, 271504920046, 0, 1, 408016874475, 483131631732, 0, 380673285087, 271504920045, 408016874475, 0, 0, 16868368268, 0, 0, 450754164561, 0, 914410021623, 772242375590, 420796377646, 632371681400, 420796377646, 498263805438, 408016874475, 0, 0, 16868368268, 500000000001, 16868368269, 632371681400, 698608775208, 164435350972, 534173424237, 420796377646, 0, 73196912683, 516795855789, 477669877634, 154701803767, 460008167640, 129984600832]) (branchResiduals041 13 1) 13962901
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck041_14_0 :
    integerResidualCheck 41 14 0 (dualNumerators041 14 0) ∧
    integerMassCheck 41 14 0 (dualNumerators041 14 0) := by
  apply integerChecks_of_simple 41 14 0 (dualNumerators041 14 0)
    (![288297190339, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 0, 433252253780, 0, 0, 1079760519503, 0, 478632796615, 1, 970965240730, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253780, 0, 0, 566747746222, 0, 671483150164, 741816932837, 174605490278, 567211442559, 446822154676, 0, 77724058423, 548759091281, 507213215908, 164269934257, 488459149252, 138024000452]) (branchResiduals041 14 0) 20161291
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck041_14_1 :
    integerResidualCheck 41 14 1 (dualNumerators041 14 1) ∧
    integerMassCheck 41 14 1 (dualNumerators041 14 1) := by
  apply integerChecks_of_simple 41 14 1 (dualNumerators041 14 1)
    (![362006560060, 66644387979, 362006560061, 0, 1, 544022499300, 644175508976, 0, 507564380116, 362006560060, 544022499300, 0, 0, 355824491024, 0, 1000000000000, 601005552747, 0, 1219213362163, 1029656500786, 561061836861, 843162241867, 561061836861, 664351740584, 544022499300, 0, 0, 355824491024, 0, 355824491025, 843162241867, 931478366944, 219247134629, 712231232315, 561061836861, 0, 97595883576, 689061141051, 636893170178, 206269071689, 613344223519, 173312801109]) (branchResiduals041 14 1) 20161291
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck041_15_0 :
    integerResidualCheck 41 15 0 (dualNumerators041 15 0) ∧
    integerMassCheck 41 15 0 (dualNumerators041 15 0) := by
  apply integerChecks_of_simple 41 15 0 (dualNumerators041 15 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546385, 0, 844525275675, 602334801077, 221089960014, 684097183123, 0, 1184097183122, 1071829546385, 0, 0, 0, 2028622458796, 1713222941252, 933538524389, 1402919220983, 933538524389, 1105400337064, 905187143136, 0, 684097183123, 500000000000, 0, 0, 1402919220983, 1549866490727, 364800514116, 1185065976612, 933538524389, 0, 162387657036, 1146513768303, 1059712622067, 343206598917, 1020530044549, 288371380791]) (branchResiduals041 15 0) 12900283
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck041_15_1 :
    integerResidualCheck 41 15 1 (dualNumerators041 15 1) ∧
    integerMassCheck 41 15 1 (dualNumerators041 15 1) := by
  apply integerChecks_of_simple 41 15 1 (dualNumerators041 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals041 15 1) 12900283
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck041_16_0 :
    integerResidualCheck 41 16 0 (dualNumerators041 16 0) ∧
    integerMassCheck 41 16 0 (dualNumerators041 16 0) := by
  apply integerChecks_of_simple 41 16 0 (dualNumerators041 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals041 16 0) 10683060
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck041_16_1 :
    integerResidualCheck 41 16 1 (dualNumerators041 16 1) ∧
    integerMassCheck 41 16 1 (dualNumerators041 16 1) := by
  apply integerChecks_of_simple 41 16 1 (dualNumerators041 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 0, 0, 0, 0, 1184800741849, 1308901425339, 308083254750, 1000818170589, 788396879662, 0, 137140480825, 968259856240, 894954094286, 289846647564, 861863417206, 243536919859]) (branchResiduals041 16 1) 10683060
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck041_17_0 :
    integerResidualCheck 41 17 0 (dualNumerators041 17 0) ∧
    integerMassCheck 41 17 0 (dualNumerators041 17 0) := by
  apply integerChecks_of_simple 41 17 0 (dualNumerators041 17 0)
    (![275782051153, 50770698773, 275782051153, 0, 1, 414444535771, 490742607366, 0, 386670191328, 275782051153, 414444535771, 0, 0, 0, 1032887523019, 0, 0, 457855084348, 928815106981, 784407834273, 427425359826, 642333698256, 427425359826, 506113164564, 414444535771, 0, 0, 0, 0, 542144915654, 642333698256, 709614252839, 167025770161, 542588482679, 427425359826, 0, 74350014410, 524937158092, 485194811960, 157138886296, 467254869626, 132032302875]) (branchResiduals041 17 0) 15120968
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck041_17_1 :
    integerResidualCheck 41 17 1 (dualNumerators041 17 1) ∧
    integerMassCheck 41 17 1 (dualNumerators041 17 1) := by
  apply integerChecks_of_simple 41 17 1 (dualNumerators041 17 1)
    (![508686963928, 93647837150, 508686963928, 0, 1, 764453421592, 905187143136, 0, 713222941253, 508686963927, 764453421593, 0, 0, 1000000000000, 905187143136, 0, 844525275674, 0, 1713222941251, 1446860076751, 788396879661, 1184800741848, 788396879661, 933538524388, 764453421592, 1, 0, 1000000000000, 0, 0, 1184800741848, 1308901425338, 308083254750, 1000818170589, 788396879661, 0, 137140480824, 968259856239, 894954094285, 289846647563, 861863417205, 243536919859]) (branchResiduals041 17 1) 15120968
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck041_18_0 :
    integerResidualCheck 41 18 0 (dualNumerators041 18 0) ∧
    integerMassCheck 41 18 0 (dualNumerators041 18 0) := by
  apply integerChecks_of_simple 41 18 0 (dualNumerators041 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 562515489548, 74022925577, 0, 476109064652, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 211125375206, 1057271324222, 763999473637, 0, 45472526152, 1025720546096, 863239815324, 123309744339, 835192545885, 236000526363]) (branchResiduals041 18 0) 13565580
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck041_18_1 :
    integerResidualCheck 41 18 1 (dualNumerators041 18 1) ∧
    integerMassCheck 41 18 1 (dualNumerators041 18 1) := by
  apply integerChecks_of_simple 41 18 1 (dualNumerators041 18 1)
    (![538874628613, 99205301184, 538874628613, 0, 1, 173280948973, 205181483568, 0, 64396810428, 45929282541, 82602613712, 90678335261, 0, 583235221374, 205181483568, 0, 0, 492556886114, 154686685730, 130636815909, 835183729590, 268562336295, 71184255953, 84289076957, 173280948973, 1, 90678335261, 492556886113, 0, 0, 268562336295, 763397412564, 115240860334, 2939686143, 71184255953, 0, 99806458592, 0, 84824690714, 183737645581, 77817540467, 21988918126]) (branchResiduals041 18 1) 13565580
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck041_19_0 :
    integerResidualCheck 41 19 0 (dualNumerators041 19 0) ∧
    integerMassCheck 41 19 0 (dualNumerators041 19 0) := by
  apply integerChecks_of_simple 41 19 0 (dualNumerators041 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 216703300504, 217988955956, 0, 1402086139076, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 143378777264, 927814294984, 593870256538, 51346609551, 3480759251, 901168865389, 673714962064, 0, 705341215054, 199308409586]) (branchResiduals041 19 0) 8248658
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck041_19_1 :
    integerResidualCheck 41 19 1 (dualNumerators041 19 1) ∧
    integerMassCheck 41 19 1 (dualNumerators041 19 1) := by
  apply integerChecks_of_simple 41 19 1 (dualNumerators041 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 1, 0, 0, 0, 0, 987477735649, 0, 339927093453, 424072380185, 460183470977, 0, 240148617570, 405068248519, 529741159093, 457736576556, 503065535987, 142151330101]) (branchResiduals041 19 1) 8248658
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck041_20_0 :
    integerResidualCheck 41 20 0 (dualNumerators041 20 0) ∧
    integerMassCheck 41 20 0 (dualNumerators041 20 0) := by
  apply integerChecks_of_simple 41 20 0 (dualNumerators041 20 0)
    (![525362030296, 96717669897, 525362030296, 0, 2, 1982073878105, 2346968095804, 0, 736602820676, 525362030295, 1821502598274, 160571279833, 0, 1032780604872, 2346968095805, 0, 0, 872209325040, 1769383425546, 1494289025232, 814241006256, 3071949885821, 814241006256, 964140481889, 1982073878106, 0, 160571279833, 872209325039, 0, 0, 3071949885821, 1351808005779, 1318182410191, 33625595588, 814241006256, 0, 1141636028738, 0, 970267099055, 2101682786767, 890115821339, 251520207400]) (branchResiduals041 20 0) 35312013
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck041_20_1 :
    integerResidualCheck 41 20 1 (dualNumerators041 20 1) ∧
    integerMassCheck 41 20 1 (dualNumerators041 20 1) := by
  apply integerChecks_of_simple 41 20 1 (dualNumerators041 20 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 832818137783, 1355072182930, 0, 1317842481106, 547079247729, 1300649428515, 132139529898, 0, 1440645255461, 407083420783]) (branchResiduals041 20 1) 35312013
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck041_21_0 :
    integerResidualCheck 41 21 0 (dualNumerators041 21 0) ∧
    integerMassCheck 41 21 0 (dualNumerators041 21 0) := by
  apply integerChecks_of_simple 41 21 0 (dualNumerators041 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 604293255477, 704608169863, 757887471419, 892563449519, 1020530044549, 288371380791]) (branchResiduals041 21 0) 11182451
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck041_21_1 :
    integerResidualCheck 41 21 1 (dualNumerators041 21 1) ∧
    integerMassCheck 41 21 1 (dualNumerators041 21 1) := by
  apply integerChecks_of_simple 41 21 1 (dualNumerators041 21 1)
    (![113874129702, 20963906509, 113874129702, 0, 1, 11418112698, 13520155082, 0, 159661338854, 113874129702, 0, 11418112698, 207483478989, 1200472654287, 13520155082, 0, 0, 1189054541591, 1567617472129, 323892577801, 176489697786, 17696550257, 176489697786, 208980953998, 11418112698, 0, 218901591686, 1189054541590, 0, 0, 17696550257, 1842875789658, 918239792457, 924635997201, 0, 176489697786, 73266609994, 174187148961, 17696550257, 0, 192935839752, 54517919203]) (branchResiduals041 21 1) 11182451
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck041_22_0 :
    integerResidualCheck 41 22 0 (dualNumerators041 22 0) ∧
    integerMassCheck 41 22 0 (dualNumerators041 22 0) := by
  apply integerChecks_of_simple 41 22 0 (dualNumerators041 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 583695195717, 0, 612220343875, 0, 492945346072, 0, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 583695195717, 0, 0, 0, 801336080718, 763999473637, 640010186655, 123989286983, 0, 460183470977, 599623014547, 45593851542, 64927501002, 736408579717, 503065535987, 142151330101]) (branchResiduals041 22 0) 6465674
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck041_22_1 :
    integerResidualCheck 41 22 1 (dualNumerators041 22 1) ∧
    integerMassCheck 41 22 1 (dualNumerators041 22 1) := by
  apply integerChecks_of_simple 41 22 1 (dualNumerators041 22 1)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 0, 5063622582, 10371186464, 88904172359, 5995821236, 0, 0, 83840549778, 1170080822236, 143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 108853458786, 21088199879, 0, 78268383123, 32491749791, 77247265314, 7847938961, 0, 85561800000, 24177215106]) (branchResiduals041 22 1) 6465674
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck041_23_0 :
    integerResidualCheck 41 23 0 (dualNumerators041 23 0) ∧
    integerMassCheck 41 23 0 (dualNumerators041 23 0) := by
  apply integerChecks_of_simple 41 23 0 (dualNumerators041 23 0)
    (![525362030296, 96717669897, 525362030296, 0, 2, 1982073878105, 2346968095804, 0, 736602820676, 525362030295, 1821502598274, 160571279833, 0, 1032780604872, 2346968095804, 0, 0, 872209325040, 1769383425546, 1494289025232, 814241006256, 3071949885821, 814241006256, 964140481889, 1982073878106, 0, 160571279833, 872209325039, 0, 0, 3071949885821, 1351808005779, 318182410191, 1033625595588, 814241006256, 0, 1141636028738, 0, 970267099055, 2101682786767, 890115821339, 251520207400]) (branchResiduals041 23 0) 35297932
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck041_23_1 :
    integerResidualCheck 41 23 1 (dualNumerators041 23 1) ∧
    integerMassCheck 41 23 1 (dualNumerators041 23 1) := by
  apply integerChecks_of_simple 41 23 1 (dualNumerators041 23 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 1832818137783, 355072182930, 0, 1317842481106, 547079247729, 1300649428515, 132139529898, 0, 1440645255461, 407083420783]) (branchResiduals041 23 1) 35297932
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck041_24_0 :
    integerResidualCheck 41 24 0 (dualNumerators041 24 0) ∧
    integerMassCheck 41 24 0 (dualNumerators041 24 0) := by
  apply integerChecks_of_simple 41 24 0 (dualNumerators041 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 276221246109, 150663467366, 0, 969054410724, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 384946583730, 686246488518, 705016048726, 601815130180, 835192545885, 236000526363]) (branchResiduals041 24 0) 9356857
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck041_24_1 :
    integerResidualCheck 41 24 1 (dualNumerators041 24 1) ∧
    integerMassCheck 41 24 1 (dualNumerators041 24 1) := by
  apply integerChecks_of_simple 41 24 1 (dualNumerators041 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 395480180778, 20824623507, 0, 133942179966, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 587483804282, 282115266095, 48434165160, 99625565721, 0, 0, 115439864933, 32619865948]) (branchResiduals041 24 1) 9356857
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck041_25_0 :
    integerResidualCheck 41 25 0 (dualNumerators041 25 0) ∧
    integerMassCheck 41 25 0 (dualNumerators041 25 0) := by
  apply integerChecks_of_simple 41 25 0 (dualNumerators041 25 0)
    (![31307490826, 5763620872, 31307490826, 0, 1, 17498922567, 20720424919, 0, 627590994654, 447612295109, 373636362947, 136807905692, 0, 879936634611, 604415620636, 0, 0, 743128728921, 1507527629264, 1273145186690, 48522430940, 27120993710, 693739297027, 821454747430, 510444268639, 1, 136807905692, 743128728920, 0, 0, 791120467347, 1151750315250, 483956334634, 667793980617, 48522430940, 0, 333537525435, 639144727060, 0, 27120993710, 758385194830, 214297057664]) (branchResiduals041 25 0) 8671199
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck041_25_1 :
    integerResidualCheck 41 25 1 (dualNumerators041 25 1) ∧
    integerMassCheck 41 25 1 (dualNumerators041 25 1) := by
  apply integerChecks_of_simple 41 25 1 (dualNumerators041 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 0, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals041 25 1) 8671199
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck041_26_0 :
    integerResidualCheck 41 26 0 (dualNumerators041 26 0) ∧
    integerMassCheck 41 26 0 (dualNumerators041 26 0) := by
  apply integerChecks_of_simple 41 26 0 (dualNumerators041 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals041 26 0) 15099566
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck041_26_1 :
    integerResidualCheck 41 26 1 (dualNumerators041 26 1) ∧
    integerMassCheck 41 26 1 (dualNumerators041 26 1) := by
  apply integerChecks_of_simple 41 26 1 (dualNumerators041 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 879744679617, 350168760452, 564110399358, 1160334187225, 0, 0, 1344522571906, 379922014678]) (branchResiduals041 26 1) 15099566
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck041_27_0 :
    integerResidualCheck 41 27 0 (dualNumerators041 27 0) ∧
    integerMassCheck 41 27 0 (dualNumerators041 27 0) := by
  apply integerChecks_of_simple 41 27 0 (dualNumerators041 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312724, 1, 0, 0, 0, 0, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 436855949686, 304617712691, 595678484088, 168320989550]) (branchResiduals041 27 0) 7338775
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck041_27_1 :
    integerResidualCheck 41 27 1 (dualNumerators041 27 1) ∧
    integerMassCheck 41 27 1 (dualNumerators041 27 1) := by
  apply integerChecks_of_simple 41 27 1 (dualNumerators041 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 234337221023, 181967583262, 0, 1170399780726, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 540348413221, 991589527988, 377837583379, 0, 340277028102, 953483284012, 430830286610, 214386579479, 413046270426, 116714568052]) (branchResiduals041 27 1) 7338775
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck041_28_0 :
    integerResidualCheck 41 28 0 (dualNumerators041 28 0) ∧
    integerMassCheck 41 28 0 (dualNumerators041 28 0) := by
  apply integerChecks_of_simple 41 28 0 (dualNumerators041 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 1, 0, 0, 0, 0, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 374399059503, 471423145846, 503065535987, 142151330101]) (branchResiduals041 28 0) 10335557
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck041_28_1 :
    integerResidualCheck 41 28 1 (dualNumerators041 28 1) ∧
    integerMassCheck 41 28 1 (dualNumerators041 28 1) := by
  apply integerChecks_of_simple 41 28 1 (dualNumerators041 28 1)
    (![70965414109, 13064532837, 70965414109, 0, 1, 500061019298, 592120844340, 0, 99499623476, 70965414109, 0, 7115673227, 105323995459, 617878243177, 8425648624, 0, 0, 610762569951, 1239006666393, 201847170824, 109986917328, 775027817129, 109986917328, 130235198988, 7115673227, 0, 112439668685, 610762569950, 0, 0, 11028343493, 946600440957, 484611900989, 461988539969, 0, 109986917328, 360985704208, 438442294145, 11028343493, 0, 120236016734, 33975115531]) (branchResiduals041 28 1) 10335557
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck041_29_0 :
    integerResidualCheck 41 29 0 (dualNumerators041 29 0) ∧
    integerMassCheck 41 29 0 (dualNumerators041 29 0) := by
  apply integerChecks_of_simple 41 29 0 (dualNumerators041 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals041 29 0) 40352153
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck041_29_1 :
    integerResidualCheck 41 29 1 (dualNumerators041 29 1) ∧
    integerMassCheck 41 29 1 (dualNumerators041 29 1) := by
  apply integerChecks_of_simple 41 29 1 (dualNumerators041 29 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 1832818137783, 355072182930, 0, 1317842481106, 1547079247729, 300649428515, 132139529898, 0, 1440645255461, 407083420783]) (branchResiduals041 29 1) 40352153
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck041_30_0 :
    integerResidualCheck 41 30 0 (dualNumerators041 30 0) ∧
    integerMassCheck 41 30 0 (dualNumerators041 30 0) := by
  apply integerChecks_of_simple 41 30 0 (dualNumerators041 30 0)
    (![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 77683757550, 37915592377, 0, 243869815754, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 1, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 111490371098, 207711178340, 155908037259, 36358164526, 69802588317, 199771188218, 179163558800, 0, 269573776534, 0]) (branchResiduals041 30 0) 7680628
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck041_30_1 :
    integerResidualCheck 41 30 1 (dualNumerators041 30 1) ∧
    integerMassCheck 41 30 1 (dualNumerators041 30 1) := by
  apply integerChecks_of_simple 41 30 1 (dualNumerators041 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 491724510490, 107456641334, 0, 691151837050, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 212932307485, 691717317156, 544901951702, 0, 94784895256, 669214578382, 621279733097, 307371055990, 536287180313, 227712293325]) (branchResiduals041 30 1) 7680628
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck041_31_0 :
    integerResidualCheck 41 31 0 (dualNumerators041 31 0) ∧
    integerMassCheck 41 31 0 (dualNumerators041 31 0) := by
  apply integerChecks_of_simple 41 31 0 (dualNumerators041 31 0)
    (![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1719079079316, 0, 231835083176, 1259308150412, 2035556695381, 0, 0, 1259308150414, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079315, 2, 231835083174, 1259308150413, 0, 0, 2664343059941, 1951759503826, 1903210393687, 48549110140, 472517800157, 1808495209396, 1648310233018, 0, 761819131889, 1902523928053, 1648310233018, 0]) (branchResiduals041 31 0) 32891612
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck041_31_1 :
    integerResidualCheck 41 31 1 (dualNumerators041 31 1) ∧
    integerMassCheck 41 31 1 (dualNumerators041 31 1) := by
  apply integerChecks_of_simple 41 31 1 (dualNumerators041 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 274671058114, 217988955956, 0, 1402086139076, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 556963843680, 992902647048, 18993131489, 744564115640, 845258320866, 704608169862]) (branchResiduals041 31 1) 32891612
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck041_32_0 :
    integerResidualCheck 41 32 0 (dualNumerators041 32 0) ∧
    integerMassCheck 41 32 0 (dualNumerators041 32 0) := by
  apply integerChecks_of_simple 41 32 0 (dualNumerators041 32 0)
    (![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 979882959195, 1099655708204, 1160276651773, 0, 382837210862, 2079538667397, 0, 979882959196, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 180393692578, 979882959195, 0, 0, 3223007296772, 1518687763292, 1272220299089, 246467464203, 0, 914758491801, 1073879389714, 208690812243, 169611716433, 3053395580339, 0, 1282570201956]) (branchResiduals041 32 0) 67647473
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck041_32_1 :
    integerResidualCheck 41 32 1 (dualNumerators041 32 1) ∧
    integerMassCheck 41 32 1 (dualNumerators041 32 1) := by
  apply integerChecks_of_simple 41 32 1 (dualNumerators041 32 1)
    (![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1307998858623, 638403098873, 0, 4106153599144, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957494, 2, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 1877217101011, 3497333197567, 2625098749289, 612179935686, 1175299814610, 3363643757919, 3016663171407, 0, 4538943572529, 0]) (branchResiduals041 32 1) 67647473
    branchSparseDots041 branchIntegerCurvature041 branchDots041
    branchIntegerCurvature041_entry rfl
    (congrFun (congrFun branchResiduals041_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks041 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 41 j s (dualNumerators041 j s) ∧
    integerMassCheck 41 j s (dualNumerators041 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck041_0_0
    · exact integerCheck041_0_1
  · fin_cases s
    · exact integerCheck041_1_0
    · exact integerCheck041_1_1
  · fin_cases s
    · exact integerCheck041_2_0
    · exact integerCheck041_2_1
  · fin_cases s
    · exact integerCheck041_3_0
    · exact integerCheck041_3_1
  · fin_cases s
    · exact integerCheck041_4_0
    · exact integerCheck041_4_1
  · fin_cases s
    · exact integerCheck041_5_0
    · exact integerCheck041_5_1
  · fin_cases s
    · exact integerCheck041_6_0
    · exact integerCheck041_6_1
  · fin_cases s
    · exact integerCheck041_7_0
    · exact integerCheck041_7_1
  · fin_cases s
    · exact integerCheck041_8_0
    · exact integerCheck041_8_1
  · fin_cases s
    · exact integerCheck041_9_0
    · exact integerCheck041_9_1
  · fin_cases s
    · exact integerCheck041_10_0
    · exact integerCheck041_10_1
  · fin_cases s
    · exact integerCheck041_11_0
    · exact integerCheck041_11_1
  · fin_cases s
    · exact integerCheck041_12_0
    · exact integerCheck041_12_1
  · fin_cases s
    · exact integerCheck041_13_0
    · exact integerCheck041_13_1
  · fin_cases s
    · exact integerCheck041_14_0
    · exact integerCheck041_14_1
  · fin_cases s
    · exact integerCheck041_15_0
    · exact integerCheck041_15_1
  · fin_cases s
    · exact integerCheck041_16_0
    · exact integerCheck041_16_1
  · fin_cases s
    · exact integerCheck041_17_0
    · exact integerCheck041_17_1
  · fin_cases s
    · exact integerCheck041_18_0
    · exact integerCheck041_18_1
  · fin_cases s
    · exact integerCheck041_19_0
    · exact integerCheck041_19_1
  · fin_cases s
    · exact integerCheck041_20_0
    · exact integerCheck041_20_1
  · fin_cases s
    · exact integerCheck041_21_0
    · exact integerCheck041_21_1
  · fin_cases s
    · exact integerCheck041_22_0
    · exact integerCheck041_22_1
  · fin_cases s
    · exact integerCheck041_23_0
    · exact integerCheck041_23_1
  · fin_cases s
    · exact integerCheck041_24_0
    · exact integerCheck041_24_1
  · fin_cases s
    · exact integerCheck041_25_0
    · exact integerCheck041_25_1
  · fin_cases s
    · exact integerCheck041_26_0
    · exact integerCheck041_26_1
  · fin_cases s
    · exact integerCheck041_27_0
    · exact integerCheck041_27_1
  · fin_cases s
    · exact integerCheck041_28_0
    · exact integerCheck041_28_1
  · fin_cases s
    · exact integerCheck041_29_0
    · exact integerCheck041_29_1
  · fin_cases s
    · exact integerCheck041_30_0
    · exact integerCheck041_30_1
  · fin_cases s
    · exact integerCheck041_31_0
    · exact integerCheck041_31_1
  · fin_cases s
    · exact integerCheck041_32_0
    · exact integerCheck041_32_1

end ElevenSquare.Tasks.T06
