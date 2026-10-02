import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual057
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
import ElevenSquare.Tasks.T06.SparseColumn50
import ElevenSquare.Tasks.T06.SparseColumn52
import ElevenSquare.Tasks.T06.SparseColumn54

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix057 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral28, roundedGradientLiteral42, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix057_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = branchIntegerMatrix057 := by
  change roundedGradients ∘ branchRows 57 = branchIntegerMatrix057
  rw [show branchRows 57 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 34, 35, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral28_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral42_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, branchIntegerMatrix057]

theorem branchColumn057_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 0) i) = _
  rw [branchColumn057_0]
  exact sparseColumn00_sum n

theorem branchColumn057_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 1) i) = _
  rw [branchColumn057_1]
  exact sparseColumn01_sum n

theorem branchColumn057_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 2) i) = _
  rw [branchColumn057_2]
  exact sparseColumn02_sum n

theorem branchColumn057_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 3) i) = _
  rw [branchColumn057_3]
  exact sparseColumn03_sum n

theorem branchColumn057_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 4) i) = _
  rw [branchColumn057_4]
  exact sparseColumn04_sum n

theorem branchColumn057_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 5) i) = _
  rw [branchColumn057_5]
  exact sparseColumn05_sum n

theorem branchColumn057_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 6) i) = _
  rw [branchColumn057_6]
  exact sparseColumn06_sum n

theorem branchColumn057_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 7) i) = _
  rw [branchColumn057_7]
  exact sparseColumn07_sum n

theorem branchColumn057_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 8) i) = _
  rw [branchColumn057_8]
  exact sparseColumn08_sum n

theorem branchColumn057_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 9) i) = _
  rw [branchColumn057_9]
  exact sparseColumn09_sum n

theorem branchColumn057_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 10) i) = _
  rw [branchColumn057_10]
  exact sparseColumn10_sum n

theorem branchColumn057_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 11) i) = _
  rw [branchColumn057_11]
  exact sparseColumn11_sum n

theorem branchColumn057_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 12) = sparseColumn12 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 12) = sparseDot12 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 12) i) = _
  rw [branchColumn057_12]
  exact sparseColumn12_sum n

theorem branchColumn057_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 13) = sparseColumn13 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 13) = sparseDot13 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 13) i) = _
  rw [branchColumn057_13]
  exact sparseColumn13_sum n

theorem branchColumn057_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 14) = sparseColumn33 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 14) = sparseDot33 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 14) i) = _
  rw [branchColumn057_14]
  exact sparseColumn33_sum n

theorem branchColumn057_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 15) = sparseColumn15 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 15) = sparseDot15 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 15) i) = _
  rw [branchColumn057_15]
  exact sparseColumn15_sum n

theorem branchColumn057_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 16) = sparseColumn16 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 16) = sparseDot16 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 16) i) = _
  rw [branchColumn057_16]
  exact sparseColumn16_sum n

theorem branchColumn057_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 17) = sparseColumn34 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 17) = sparseDot34 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 17) i) = _
  rw [branchColumn057_17]
  exact sparseColumn34_sum n

theorem branchColumn057_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 18) i) = _
  rw [branchColumn057_18]
  exact sparseColumn18_sum n

theorem branchColumn057_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 19) i) = _
  rw [branchColumn057_19]
  exact sparseColumn19_sum n

theorem branchColumn057_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 20) = sparseColumn52 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 20) = sparseDot52 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 20) i) = _
  rw [branchColumn057_20]
  exact sparseColumn52_sum n

theorem branchColumn057_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 21) i) = _
  rw [branchColumn057_21]
  exact sparseColumn21_sum n

theorem branchColumn057_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 22) i) = _
  rw [branchColumn057_22]
  exact sparseColumn22_sum n

theorem branchColumn057_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 23) = sparseColumn54 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 23) = sparseDot54 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 23) i) = _
  rw [branchColumn057_23]
  exact sparseColumn54_sum n

theorem branchColumn057_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 24) i) = _
  rw [branchColumn057_24]
  exact sparseColumn24_sum n

theorem branchColumn057_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 25) i) = _
  rw [branchColumn057_25]
  exact sparseColumn25_sum n

theorem branchColumn057_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 26) = sparseColumn44 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 26) = sparseDot44 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 26) i) = _
  rw [branchColumn057_26]
  exact sparseColumn44_sum n

theorem branchColumn057_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 27) i) = _
  rw [branchColumn057_27]
  exact sparseColumn27_sum n

theorem branchColumn057_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 28) i) = _
  rw [branchColumn057_28]
  exact sparseColumn28_sum n

theorem branchColumn057_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 29) = sparseColumn50 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 29) = sparseDot50 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 29) i) = _
  rw [branchColumn057_29]
  exact sparseColumn50_sum n

theorem branchColumn057_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 30) i) = _
  rw [branchColumn057_30]
  exact sparseColumn30_sum n

theorem branchColumn057_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 31) i) = _
  rw [branchColumn057_31]
  exact sparseColumn31_sum n

theorem branchColumn057_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 57 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 57 i)) = _
  rw [branchIntegerMatrix057_eq]
  simp only [branchIntegerMatrix057, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot057_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 57 i) 32) i) = _
  rw [branchColumn057_32]
  exact sparseColumn32_sum n

def branchSparseDots057 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot12, sparseDot13, sparseDot33, sparseDot15, sparseDot16, sparseDot34, sparseDot18, sparseDot19, sparseDot52, sparseDot21, sparseDot22, sparseDot54, sparseDot24, sparseDot25, sparseDot44, sparseDot27, sparseDot28, sparseDot50, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot057_0 :
    branchSparseDots057 0 = sparseDot00 := rfl

private theorem branchSparseDot057_1 :
    branchSparseDots057 1 = sparseDot01 := rfl

private theorem branchSparseDot057_2 :
    branchSparseDots057 2 = sparseDot02 := rfl

private theorem branchSparseDot057_3 :
    branchSparseDots057 3 = sparseDot03 := rfl

private theorem branchSparseDot057_4 :
    branchSparseDots057 4 = sparseDot04 := rfl

private theorem branchSparseDot057_5 :
    branchSparseDots057 5 = sparseDot05 := rfl

private theorem branchSparseDot057_6 :
    branchSparseDots057 6 = sparseDot06 := rfl

private theorem branchSparseDot057_7 :
    branchSparseDots057 7 = sparseDot07 := rfl

private theorem branchSparseDot057_8 :
    branchSparseDots057 8 = sparseDot08 := rfl

private theorem branchSparseDot057_9 :
    branchSparseDots057 9 = sparseDot09 := rfl

private theorem branchSparseDot057_10 :
    branchSparseDots057 10 = sparseDot10 := rfl

private theorem branchSparseDot057_11 :
    branchSparseDots057 11 = sparseDot11 := rfl

private theorem branchSparseDot057_12 :
    branchSparseDots057 12 = sparseDot12 := rfl

private theorem branchSparseDot057_13 :
    branchSparseDots057 13 = sparseDot13 := rfl

private theorem branchSparseDot057_14 :
    branchSparseDots057 14 = sparseDot33 := rfl

private theorem branchSparseDot057_15 :
    branchSparseDots057 15 = sparseDot15 := rfl

private theorem branchSparseDot057_16 :
    branchSparseDots057 16 = sparseDot16 := rfl

private theorem branchSparseDot057_17 :
    branchSparseDots057 17 = sparseDot34 := rfl

private theorem branchSparseDot057_18 :
    branchSparseDots057 18 = sparseDot18 := rfl

private theorem branchSparseDot057_19 :
    branchSparseDots057 19 = sparseDot19 := rfl

private theorem branchSparseDot057_20 :
    branchSparseDots057 20 = sparseDot52 := rfl

private theorem branchSparseDot057_21 :
    branchSparseDots057 21 = sparseDot21 := rfl

private theorem branchSparseDot057_22 :
    branchSparseDots057 22 = sparseDot22 := rfl

private theorem branchSparseDot057_23 :
    branchSparseDots057 23 = sparseDot54 := rfl

private theorem branchSparseDot057_24 :
    branchSparseDots057 24 = sparseDot24 := rfl

private theorem branchSparseDot057_25 :
    branchSparseDots057 25 = sparseDot25 := rfl

private theorem branchSparseDot057_26 :
    branchSparseDots057 26 = sparseDot44 := rfl

private theorem branchSparseDot057_27 :
    branchSparseDots057 27 = sparseDot27 := rfl

private theorem branchSparseDot057_28 :
    branchSparseDots057 28 = sparseDot28 := rfl

private theorem branchSparseDot057_29 :
    branchSparseDots057 29 = sparseDot50 := rfl

private theorem branchSparseDot057_30 :
    branchSparseDots057 30 = sparseDot30 := rfl

private theorem branchSparseDot057_31 :
    branchSparseDots057 31 = sparseDot31 := rfl

private theorem branchSparseDot057_32 :
    branchSparseDots057 32 = sparseDot32 := rfl

theorem branchDots057 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 57 i) k) = branchSparseDots057 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot057_0 n
      _ = _ := congrFun branchSparseDot057_0.symm n
  · calc
      _ = sparseDot01 n := branchDot057_1 n
      _ = _ := congrFun branchSparseDot057_1.symm n
  · calc
      _ = sparseDot02 n := branchDot057_2 n
      _ = _ := congrFun branchSparseDot057_2.symm n
  · calc
      _ = sparseDot03 n := branchDot057_3 n
      _ = _ := congrFun branchSparseDot057_3.symm n
  · calc
      _ = sparseDot04 n := branchDot057_4 n
      _ = _ := congrFun branchSparseDot057_4.symm n
  · calc
      _ = sparseDot05 n := branchDot057_5 n
      _ = _ := congrFun branchSparseDot057_5.symm n
  · calc
      _ = sparseDot06 n := branchDot057_6 n
      _ = _ := congrFun branchSparseDot057_6.symm n
  · calc
      _ = sparseDot07 n := branchDot057_7 n
      _ = _ := congrFun branchSparseDot057_7.symm n
  · calc
      _ = sparseDot08 n := branchDot057_8 n
      _ = _ := congrFun branchSparseDot057_8.symm n
  · calc
      _ = sparseDot09 n := branchDot057_9 n
      _ = _ := congrFun branchSparseDot057_9.symm n
  · calc
      _ = sparseDot10 n := branchDot057_10 n
      _ = _ := congrFun branchSparseDot057_10.symm n
  · calc
      _ = sparseDot11 n := branchDot057_11 n
      _ = _ := congrFun branchSparseDot057_11.symm n
  · calc
      _ = sparseDot12 n := branchDot057_12 n
      _ = _ := congrFun branchSparseDot057_12.symm n
  · calc
      _ = sparseDot13 n := branchDot057_13 n
      _ = _ := congrFun branchSparseDot057_13.symm n
  · calc
      _ = sparseDot33 n := branchDot057_14 n
      _ = _ := congrFun branchSparseDot057_14.symm n
  · calc
      _ = sparseDot15 n := branchDot057_15 n
      _ = _ := congrFun branchSparseDot057_15.symm n
  · calc
      _ = sparseDot16 n := branchDot057_16 n
      _ = _ := congrFun branchSparseDot057_16.symm n
  · calc
      _ = sparseDot34 n := branchDot057_17 n
      _ = _ := congrFun branchSparseDot057_17.symm n
  · calc
      _ = sparseDot18 n := branchDot057_18 n
      _ = _ := congrFun branchSparseDot057_18.symm n
  · calc
      _ = sparseDot19 n := branchDot057_19 n
      _ = _ := congrFun branchSparseDot057_19.symm n
  · calc
      _ = sparseDot52 n := branchDot057_20 n
      _ = _ := congrFun branchSparseDot057_20.symm n
  · calc
      _ = sparseDot21 n := branchDot057_21 n
      _ = _ := congrFun branchSparseDot057_21.symm n
  · calc
      _ = sparseDot22 n := branchDot057_22 n
      _ = _ := congrFun branchSparseDot057_22.symm n
  · calc
      _ = sparseDot54 n := branchDot057_23 n
      _ = _ := congrFun branchSparseDot057_23.symm n
  · calc
      _ = sparseDot24 n := branchDot057_24 n
      _ = _ := congrFun branchSparseDot057_24.symm n
  · calc
      _ = sparseDot25 n := branchDot057_25 n
      _ = _ := congrFun branchSparseDot057_25.symm n
  · calc
      _ = sparseDot44 n := branchDot057_26 n
      _ = _ := congrFun branchSparseDot057_26.symm n
  · calc
      _ = sparseDot27 n := branchDot057_27 n
      _ = _ := congrFun branchSparseDot057_27.symm n
  · calc
      _ = sparseDot28 n := branchDot057_28 n
      _ = _ := congrFun branchSparseDot057_28.symm n
  · calc
      _ = sparseDot50 n := branchDot057_29 n
      _ = _ := congrFun branchSparseDot057_29.symm n
  · calc
      _ = sparseDot30 n := branchDot057_30 n
      _ = _ := congrFun branchSparseDot057_30.symm n
  · calc
      _ = sparseDot31 n := branchDot057_31 n
      _ = _ := congrFun branchSparseDot057_31.symm n
  · calc
      _ = sparseDot32 n := branchDot057_32 n
      _ = _ := congrFun branchSparseDot057_32.symm n

def branchIntegerCurvature057 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101955390, 101955390, 44932602, 44932602, 106371291, 106371291, 88123140, 88123140, 204734428, 204734428]

theorem branchIntegerCurvature057_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 57 i)) = branchIntegerCurvature057 := by
  change curvatureNumerators ∘ branchRows 57 = branchIntegerCurvature057
  rw [show branchRows 57 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 34, 35, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature057_entry (i : Fin 42) :
    curvatureNumerators (branchRows 57 i) = branchIntegerCurvature057 i :=
  congrFun branchIntegerCurvature057_eq i

def branchResiduals057 : Fin 33 → Fin 2 → ℕ := ![![1301447592154059, 33000000000000], ![1546085664500166, 33000000000000], ![1583103240284604, 1338828071769077], ![33000000000000, 1025217134833129], ![855491293628229, 33000000000000], ![1056484410753391, 892062475511075], ![725114192400229, 622122527367398], ![33000000000000, 759760968924515], ![1579104544528405, 1129806521251147], ![1026875317471481, 33000000000000], ![33000000000000, 778493393093358], ![482201199409336, 465442676784098], ![990717134833129, 66000000000000], ![33000000000000, 409793587600922], ![465466336762532, 578088261942029], ![925273190301089, 33000000000000], ![66000000000000, 744588350447475], ![446016396479858, 809645288035845], ![620645736811204, 261264582951761], ![633325768477521, 510811977907392], ![1362162822532732, 951613813993539], ![754308253543593, 388776044635672], ![466862178282494, 105297405644388], ![1361162822532666, 951613813993539], ![669871126225656, 230563481461668], ![504894193304050, 223581994926723], ![398970616796057, 856050208658842], ![409028509487699, 551482613248176], ![285695880026063, 310753415170659], ![398970616796057, 951613813993539], ![215890011049063, 556607905923174], ![1681843826308746, 651506017335273], ![1328362461418628, 2883627282374997]]

theorem branchResiduals057_eq : residualNumerators 57 = branchResiduals057 := rfl

theorem integerCheck057_0_0 :
    integerResidualCheck 57 0 0 (dualNumerators057 0 0) ∧
    integerMassCheck 57 0 0 (dualNumerators057 0 0) := by
  apply integerChecks_of_simple 57 0 0 (dualNumerators057 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1011030237961, 258120108700, 0, 1660206247774, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 511481744370, 1661564579697, 1308901425339, 0, 445670439042, 1389522106843, 1485808378804, 481205215181, 1430871029972, 404321515913]) (branchResiduals057 0 0) 18767167
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck057_0_1 :
    integerResidualCheck 57 0 1 (dualNumerators057 0 1) ∧
    integerMassCheck 57 0 1 (dualNumerators057 0 1) := by
  apply integerChecks_of_simple 57 0 1 (dualNumerators057 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals057 0 1) 18767167
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck057_1_0 :
    integerResidualCheck 57 1 0 (dualNumerators057 1 0) ∧
    integerMassCheck 57 1 0 (dualNumerators057 1 0) := by
  apply integerChecks_of_simple 57 1 0 (dualNumerators057 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1197158056821, 305639293618, 0, 1965845541389, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 605644092726, 1967453938394, 1549866490727, 0, 527717111470, 1645329212598, 1759341515999, 569793739799, 1694290356000, 478755968067]) (branchResiduals057 1 0) 22176635
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck057_1_1 :
    integerResidualCheck 57 1 1 (dualNumerators057 1 1) ∧
    integerMassCheck 57 1 1 (dualNumerators057 1 1) := by
  apply integerChecks_of_simple 57 1 1 (dualNumerators057 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals057 1 1) 22176635
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck057_2_0 :
    integerResidualCheck 57 2 0 (dualNumerators057 2 0) ∧
    integerMassCheck 57 2 0 (dualNumerators057 2 0) := by
  apply integerChecks_of_simple 57 2 0 (dualNumerators057 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1197158056822, 305639293619, 0, 1965845541391, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 605644092727, 1967453938395, 1549866490728, 0, 527717111470, 1645329212599, 1759341516001, 569793739799, 1694290356001, 478755968068]) (branchResiduals057 2 0) 22681452
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck057_2_1 :
    integerResidualCheck 57 2 1 (dualNumerators057 2 1) ∧
    integerMassCheck 57 2 1 (dualNumerators057 2 1) := by
  apply integerChecks_of_simple 57 2 1 (dualNumerators057 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1011030237961, 258120108700, 0, 1660206247773, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 511481744370, 1661564579696, 1308901425338, 0, 445670439042, 1389522106842, 1485808378803, 481205215180, 1430871029971, 404321515912]) (branchResiduals057 2 1) 22681452
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck057_3_0 :
    integerResidualCheck 57 3 0 (dualNumerators057 3 0) ∧
    integerMassCheck 57 3 0 (dualNumerators057 3 0) := by
  apply integerChecks_of_simple 57 3 0 (dualNumerators057 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals057 3 0) 16360330
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck057_3_1 :
    integerResidualCheck 57 3 1 (dualNumerators057 3 1) ∧
    integerMassCheck 57 3 1 (dualNumerators057 3 1) := by
  apply integerChecks_of_simple 57 3 1 (dualNumerators057 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 796619754801, 203380245200, 0, 1308124173107, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 403011152868, 1309194441832, 1031321016287, 0, 351156535721, 1094844366154, 1170711084556, 379155406172, 1127424369963, 318576531911]) (branchResiduals057 3 1) 16360330
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck057_4_0 :
    integerResidualCheck 57 4 0 (dualNumerators057 4 0) ∧
    integerMassCheck 57 4 0 (dualNumerators057 4 0) := by
  apply integerChecks_of_simple 57 4 0 (dualNumerators057 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 672765518030, 171759757645, 0, 1104743927909, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 340353104975, 1105647796899, 870976665588, 0, 296560570134, 924623740146, 988695101419, 320206323920, 952138376845, 269045933435]) (branchResiduals057 4 0) 13760362
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck057_4_1 :
    integerResidualCheck 57 4 1 (dualNumerators057 4 1) ∧
    integerMassCheck 57 4 1 (dualNumerators057 4 1) := by
  apply integerChecks_of_simple 57 4 1 (dualNumerators057 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals057 4 1) 13760362
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck057_5_0 :
    integerResidualCheck 57 5 0 (dualNumerators057 5 0) ∧
    integerMassCheck 57 5 0 (dualNumerators057 5 0) := by
  apply integerChecks_of_simple 57 5 0 (dualNumerators057 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 796619754801, 203380245201, 0, 1308124173108, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 403011152868, 1309194441833, 1031321016288, 0, 351156535721, 1094844366155, 1170711084557, 379155406172, 1127424369964, 318576531911]) (branchResiduals057 5 0) 17641130
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck057_5_1 :
    integerResidualCheck 57 5 1 (dualNumerators057 5 1) ∧
    integerMassCheck 57 5 1 (dualNumerators057 5 1) := by
  apply integerChecks_of_simple 57 5 1 (dualNumerators057 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 340353104975, 1105647796898, 870976665588, 0, 296560570134, 924623740145, 988695101418, 320206323920, 952138376844, 269045933435]) (branchResiduals057 5 1) 17641130
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck057_6_0 :
    integerResidualCheck 57 6 0 (dualNumerators057 6 0) ∧
    integerMassCheck 57 6 0 (dualNumerators057 6 0) := by
  apply integerChecks_of_simple 57 6 0 (dualNumerators057 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 0, 70552396879, 187567711821, 1472638535954, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 1, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 877488274356, 957704271528, 2719950702, 106626845062, 1430871029972, 404321515913]) (branchResiduals057 6 0) 8962451
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck057_6_1 :
    integerResidualCheck 57 6 1 (dualNumerators057 6 1) ∧
    integerMassCheck 57 6 1 (dualNumerators057 6 1) := by
  apply integerChecks_of_simple 57 6 1 (dualNumerators057 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949782, 1, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals057 6 1) 8962451
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck057_7_0 :
    integerResidualCheck 57 7 0 (dualNumerators057 7 0) ∧
    integerMassCheck 57 7 0 (dualNumerators057 7 0) := by
  apply integerChecks_of_simple 57 7 0 (dualNumerators057 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals057 7 0) 10424794
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck057_7_1 :
    integerResidualCheck 57 7 1 (dualNumerators057 7 1) ∧
    integerMassCheck 57 7 1 (dualNumerators057 7 1) := by
  apply integerChecks_of_simple 57 7 1 (dualNumerators057 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 598579028412, 152819646809, 0, 982922770697, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 302822046364, 983726969199, 774933245365, 0, 263858555736, 822664606300, 879670758001, 284896869900, 847145178002, 239377984034]) (branchResiduals057 7 1) 10424794
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck057_8_0 :
    integerResidualCheck 57 8 0 (dualNumerators057 8 0) ∧
    integerMassCheck 57 8 0 (dualNumerators057 8 0) := by
  apply integerChecks_of_simple 57 8 0 (dualNumerators057 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1197158056824, 305639293618, 0, 1965845541393, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 605644092727, 1967453938397, 1549866490730, 0, 527717111471, 1645329212600, 1759341516002, 569793739800, 1694290356003, 478755968068]) (branchResiduals057 8 0) 22681452
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck057_8_1 :
    integerResidualCheck 57 8 1 (dualNumerators057 8 1) ∧
    integerMassCheck 57 8 1 (dualNumerators057 8 1) := by
  apply integerChecks_of_simple 57 8 1 (dualNumerators057 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590429, 217988955956, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546384, 0, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 431959261166, 1403233284717, 1105400337063, 0, 376379950391, 1173486540335, 1254802730706, 406389967006, 1208406751039, 341459739686]) (branchResiduals057 8 1) 22681452
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck057_9_0 :
    integerResidualCheck 57 9 0 (dualNumerators057 9 0) ∧
    integerMassCheck 57 9 0 (dualNumerators057 9 0) := by
  apply integerChecks_of_simple 57 9 0 (dualNumerators057 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 887477428322, 296619754801, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 703380245200, 296619754801, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 403011152868, 1309194441832, 1031321016287, 0, 351156535721, 1094844366154, 1170711084556, 379155406172, 1127424369963, 318576531911]) (branchResiduals057 9 0) 16350530
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck057_9_1 :
    integerResidualCheck 57 9 1 (dualNumerators057 9 1) ∧
    integerMassCheck 57 9 1 (dualNumerators057 9 1) := by
  apply integerChecks_of_simple 57 9 1 (dualNumerators057 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals057 9 1) 16350530
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck057_10_0 :
    integerResidualCheck 57 10 0 (dualNumerators057 10 0) ∧
    integerMassCheck 57 10 0 (dualNumerators057 10 0) := by
  apply integerChecks_of_simple 57 10 0 (dualNumerators057 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals057 10 0) 10683139
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck057_10_1 :
    integerResidualCheck 57 10 1 (dualNumerators057 10 1) ∧
    integerMassCheck 57 10 1 (dualNumerators057 10 1) := by
  apply integerChecks_of_simple 57 10 1 (dualNumerators057 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 560661867464, 344525275673, 0, 844525275674, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 419928145920, 344525275674, 155474724327, 844525275674, 0, 0, 1184800741849, 1308901425339, 308083254750, 1000818170589, 788396879662, 0, 268442815247, 836957521818, 894954094286, 289846647564, 861863417206, 243536919859]) (branchResiduals057 10 1) 10683139
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck057_11_0 :
    integerResidualCheck 57 11 0 (dualNumerators057 11 0) ∧
    integerMassCheck 57 11 0 (dualNumerators057 11 0) := by
  apply integerChecks_of_simple 57 11 0 (dualNumerators057 11 0)
    (![301584229951, 55520807208, 301584229951, 0, 1, 453219981703, 536656503669, 0, 422847068578, 301584229950, 0, 453219981704, 546780018297, 0, 582744499174, 0, 0, 500692022794, 1015715082378, 857797059952, 467415292132, 702430462570, 467415292132, 553465130761, 453219981704, 0, 0, 546780018297, 0, 46087995504, 702430462570, 776005788302, 182652707329, 593353080973, 467415292132, 0, 159151158695, 496205343596, 530589656322, 171840806248, 510971252327, 144385249964]) (branchResiduals057 11 0) 15120968
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck057_11_1 :
    integerResidualCheck 57 11 1 (dualNumerators057 11 1) ∧
    integerMassCheck 57 11 1 (dualNumerators057 11 1) := by
  apply integerChecks_of_simple 57 11 1 (dualNumerators057 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 174605490278, 567211442559, 446822154676, 0, 152139360530, 474343789173, 507213215908, 164269934257, 488459149252, 138024000452]) (branchResiduals057 11 1) 15120968
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck057_12_0 :
    integerResidualCheck 57 12 0 (dualNumerators057 12 0) ∧
    integerMassCheck 57 12 0 (dualNumerators057 12 0) := by
  apply integerChecks_of_simple 57 12 0 (dualNumerators057 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 403011152868, 1309194441832, 1031321016287, 0, 351156535721, 1094844366154, 1170711084556, 379155406172, 1127424369963, 318576531911]) (branchResiduals057 12 0) 16348076
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck057_12_1 :
    integerResidualCheck 57 12 1 (dualNumerators057 12 1) ∧
    integerMassCheck 57 12 1 (dualNumerators057 12 1) := by
  apply integerChecks_of_simple 57 12 1 (dualNumerators057 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals057 12 1) 16348076
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck057_13_0 :
    integerResidualCheck 57 13 0 (dualNumerators057 13 0) ∧
    integerMassCheck 57 13 0 (dualNumerators057 13 0) := by
  apply integerChecks_of_simple 57 13 0 (dualNumerators057 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals057 13 0) 13962901
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck057_13_1 :
    integerResidualCheck 57 13 1 (dualNumerators057 13 1) ∧
    integerMassCheck 57 13 1 (dualNumerators057 13 1) := by
  apply integerChecks_of_simple 57 13 1 (dualNumerators057 13 1)
    (![271504920046, 49983290985, 271504920046, 0, 1, 408016874475, 483131631732, 0, 380673285087, 271504920045, 408016874475, 0, 0, 16868368268, 0, 0, 450754164561, 0, 914410021623, 772242375590, 420796377646, 632371681400, 420796377646, 498263805438, 408016874475, 0, 0, 16868368268, 500000000001, 16868368269, 632371681400, 698608775208, 164435350972, 534173424237, 420796377646, 0, 143277792156, 446714976315, 477669877634, 154701803767, 460008167640, 129984600832]) (branchResiduals057 13 1) 13962901
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck057_14_0 :
    integerResidualCheck 57 14 0 (dualNumerators057 14 0) ∧
    integerMassCheck 57 14 0 (dualNumerators057 14 0) := by
  apply integerChecks_of_simple 57 14 0 (dualNumerators057 14 0)
    (![288297190339, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 0, 433252253780, 0, 0, 1079760519503, 0, 478632796615, 1, 970965240730, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253780, 0, 0, 566747746222, 0, 671483150164, 741816932837, 174605490278, 567211442559, 446822154676, 0, 152139360530, 474343789174, 507213215908, 164269934257, 488459149252, 138024000452]) (branchResiduals057 14 0) 20161291
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck057_14_1 :
    integerResidualCheck 57 14 1 (dualNumerators057 14 1) ∧
    integerMassCheck 57 14 1 (dualNumerators057 14 1) := by
  apply integerChecks_of_simple 57 14 1 (dualNumerators057 14 1)
    (![362006560060, 66644387979, 362006560061, 0, 1, 544022499300, 644175508976, 0, 507564380116, 362006560060, 544022499300, 0, 0, 355824491024, 0, 1000000000000, 601005552747, 0, 1219213362163, 1029656500786, 561061836861, 843162241867, 561061836861, 664351740584, 544022499300, 0, 0, 355824491024, 0, 355824491025, 843162241867, 931478366944, 219247134629, 712231232315, 561061836861, 0, 191037056208, 595619968419, 636893170178, 206269071689, 613344223519, 173312801109]) (branchResiduals057 14 1) 20161291
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck057_15_0 :
    integerResidualCheck 57 15 0 (dualNumerators057 15 0) ∧
    integerMassCheck 57 15 0 (dualNumerators057 15 0) := by
  apply integerChecks_of_simple 57 15 0 (dualNumerators057 15 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546385, 0, 844525275675, 602334801077, 221089960014, 684097183123, 0, 1184097183122, 1071829546385, 0, 0, 0, 2028622458796, 1713222941252, 933538524389, 1402919220983, 933538524389, 1105400337064, 905187143136, 0, 684097183123, 500000000000, 0, 0, 1402919220983, 1549866490727, 364800514116, 1185065976612, 933538524389, 0, 317862381362, 991039043977, 1059712622067, 343206598917, 1020530044549, 288371380791]) (branchResiduals057 15 0) 12900283
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck057_15_1 :
    integerResidualCheck 57 15 1 (dualNumerators057 15 1) ∧
    integerMassCheck 57 15 1 (dualNumerators057 15 1) := by
  apply integerChecks_of_simple 57 15 1 (dualNumerators057 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals057 15 1) 12900283
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck057_16_0 :
    integerResidualCheck 57 16 0 (dualNumerators057 16 0) ∧
    integerMassCheck 57 16 0 (dualNumerators057 16 0) := by
  apply integerChecks_of_simple 57 16 0 (dualNumerators057 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals057 16 0) 10683060
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck057_16_1 :
    integerResidualCheck 57 16 1 (dualNumerators057 16 1) ∧
    integerMassCheck 57 16 1 (dualNumerators057 16 1) := by
  apply integerChecks_of_simple 57 16 1 (dualNumerators057 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 0, 0, 0, 0, 1184800741849, 1308901425339, 308083254750, 1000818170589, 788396879662, 0, 268442815247, 836957521818, 894954094286, 289846647564, 861863417206, 243536919859]) (branchResiduals057 16 1) 10683060
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck057_17_0 :
    integerResidualCheck 57 17 0 (dualNumerators057 17 0) ∧
    integerMassCheck 57 17 0 (dualNumerators057 17 0) := by
  apply integerChecks_of_simple 57 17 0 (dualNumerators057 17 0)
    (![275782051153, 50770698773, 275782051153, 0, 1, 414444535771, 490742607366, 0, 386670191328, 275782051153, 414444535771, 0, 0, 0, 1032887523019, 0, 0, 457855084348, 928815106981, 784407834273, 427425359826, 642333698256, 427425359826, 506113164564, 414444535771, 0, 0, 0, 0, 542144915654, 642333698256, 709614252839, 167025770161, 542588482679, 427425359826, 0, 145534907430, 453752265072, 485194811960, 157138886296, 467254869626, 132032302875]) (branchResiduals057 17 0) 15120968
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck057_17_1 :
    integerResidualCheck 57 17 1 (dualNumerators057 17 1) ∧
    integerMassCheck 57 17 1 (dualNumerators057 17 1) := by
  apply integerChecks_of_simple 57 17 1 (dualNumerators057 17 1)
    (![508686963928, 93647837150, 508686963928, 0, 1, 764453421592, 905187143136, 0, 713222941253, 508686963927, 764453421593, 0, 0, 1000000000000, 905187143136, 0, 844525275674, 0, 1713222941251, 1446860076751, 788396879661, 1184800741848, 788396879661, 933538524388, 764453421592, 1, 0, 1000000000000, 0, 0, 1184800741848, 1308901425338, 308083254750, 1000818170589, 788396879661, 0, 268442815246, 836957521818, 894954094285, 289846647563, 861863417205, 243536919859]) (branchResiduals057 17 1) 15120968
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck057_18_0 :
    integerResidualCheck 57 18 0 (dualNumerators057 18 0) ∧
    integerMassCheck 57 18 0 (dualNumerators057 18 0) := by
  apply integerChecks_of_simple 57 18 0 (dualNumerators057 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 562515489548, 74022925577, 0, 476109064652, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 211125375206, 1057271324222, 763999473637, 0, 172711632462, 898481439786, 863239815324, 123309744339, 835192545885, 236000526363]) (branchResiduals057 18 0) 13565580
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck057_18_1 :
    integerResidualCheck 57 18 1 (dualNumerators057 18 1) ∧
    integerMassCheck 57 18 1 (dualNumerators057 18 1) := by
  apply integerChecks_of_simple 57 18 1 (dualNumerators057 18 1)
    (![546080038515, 100531796850, 546080038516, 0, 1, 184109219884, 218003208651, 0, 74499415779, 53134692444, 91228628230, 92880591654, 0, 597399944305, 218003208651, 0, 0, 504519352652, 178954014012, 151131188017, 846351152950, 285344710532, 82351679314, 97512391500, 184109219884, 1, 92880591654, 504519352652, 0, 0, 285344710532, 781937638598, 119604774277, 17115998234, 82351679314, 0, 115464148095, 0, 97501467496, 187843243037, 90025596976, 25438551119]) (branchResiduals057 18 1) 13565580
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck057_19_0 :
    integerResidualCheck 57 19 0 (dualNumerators057 19 0) ∧
    integerMassCheck 57 19 0 (dualNumerators057 19 0) := by
  apply integerChecks_of_simple 57 19 0 (dualNumerators057 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 216703300504, 217988955956, 0, 1402086139076, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 143378777264, 927814294984, 593870256538, 51346609551, 110937400584, 793712224057, 673714962064, 0, 705341215054, 199308409586]) (branchResiduals057 19 0) 8248658
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck057_19_1 :
    integerResidualCheck 57 19 1 (dualNumerators057 19 1) ∧
    integerMassCheck 57 19 1 (dualNumerators057 19 1) := by
  apply integerChecks_of_simple 57 19 1 (dualNumerators057 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 1, 0, 0, 0, 0, 987477735649, 0, 339927093453, 424072380185, 460183470977, 0, 316789159358, 328427706730, 529741159093, 457736576556, 503065535987, 142151330101]) (branchResiduals057 19 1) 8248658
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck057_20_0 :
    integerResidualCheck 57 20 0 (dualNumerators057 20 0) ∧
    integerMassCheck 57 20 0 (dualNumerators057 20 0) := by
  apply integerChecks_of_simple 57 20 0 (dualNumerators057 20 0)
    (![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 1920171252556, 185761786321, 0, 1194803767136, 2493629379177, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038876, 0, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 1368099033367, 195781320438, 941979561817, 0, 1320736486917, 0, 1115270391492, 2148644657176, 1029757657634, 290978829284]) (branchResiduals057 20 0) 35312013
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck057_20_1 :
    integerResidualCheck 57 20 1 (dualNumerators057 20 1) ∧
    integerMassCheck 57 20 1 (dualNumerators057 20 1) := by
  apply integerChecks_of_simple 57 20 1 (dualNumerators057 20 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 832818137783, 1355072182930, 0, 1317842481106, 766557277936, 1081171398308, 132139529898, 0, 1440645255461, 407083420783]) (branchResiduals057 20 1) 35312013
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck057_21_0 :
    integerResidualCheck 57 21 0 (dualNumerators057 21 0) ∧
    integerMassCheck 57 21 0 (dualNumerators057 21 0) := by
  apply integerChecks_of_simple 57 21 0 (dualNumerators057 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 759767979803, 549133445537, 757887471419, 892563449519, 1020530044549, 288371380791]) (branchResiduals057 21 0) 11182451
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck057_21_1 :
    integerResidualCheck 57 21 1 (dualNumerators057 21 1) ∧
    integerMassCheck 57 21 1 (dualNumerators057 21 1) := by
  apply integerChecks_of_simple 57 21 1 (dualNumerators057 21 1)
    (![113874129702, 20963906509, 113874129702, 0, 1, 11418112698, 13520155082, 0, 159661338854, 113874129702, 0, 11418112698, 207483478989, 1200472654287, 13520155082, 0, 0, 1189054541591, 1567617472129, 323892577801, 176489697786, 17696550257, 176489697786, 208980953998, 11418112698, 0, 218901591686, 1189054541590, 0, 0, 17696550257, 1842875789658, 918239792457, 924635997201, 0, 176489697786, 102659812730, 144793946225, 17696550257, 0, 192935839752, 54517919203]) (branchResiduals057 21 1) 11182451
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck057_22_0 :
    integerResidualCheck 57 22 0 (dualNumerators057 22 0) ∧
    integerMassCheck 57 22 0 (dualNumerators057 22 0) := by
  apply integerChecks_of_simple 57 22 0 (dualNumerators057 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 583695195717, 0, 612220343875, 0, 492945346072, 0, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 583695195717, 0, 0, 0, 801336080718, 763999473637, 608963496407, 155035977230, 31046690248, 429136780729, 645216866088, 0, 95974191249, 705361889470, 503065535987, 142151330101]) (branchResiduals057 22 0) 6465674
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck057_22_1 :
    integerResidualCheck 57 22 1 (dualNumerators057 22 1) ∧
    integerMassCheck 57 22 1 (dualNumerators057 22 1) := by
  apply integerChecks_of_simple 57 22 1 (dualNumerators057 22 1)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 0, 5063622582, 10371186464, 88904172359, 5995821236, 0, 0, 83840549778, 1170080822236, 143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 108853458786, 21088199879, 0, 78268383123, 45526836155, 64212178950, 7847938961, 0, 85561800000, 24177215106]) (branchResiduals057 22 1) 6465674
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck057_23_0 :
    integerResidualCheck 57 23 0 (dualNumerators057 23 0) ∧
    integerMassCheck 57 23 0 (dualNumerators057 23 0) := by
  apply integerChecks_of_simple 57 23 0 (dualNumerators057 23 0)
    (![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 1920171252556, 185761786321, 0, 1194803767136, 2493629379175, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038876, 0, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 368099033367, 1195781320438, 941979561817, 0, 1320736486917, 0, 1115270391492, 2148644657176, 1029757657634, 290978829284]) (branchResiduals057 23 0) 35297932
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck057_23_1 :
    integerResidualCheck 57 23 1 (dualNumerators057 23 1) ∧
    integerMassCheck 57 23 1 (dualNumerators057 23 1) := by
  apply integerChecks_of_simple 57 23 1 (dualNumerators057 23 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 1832818137783, 355072182930, 0, 1317842481106, 766557277936, 1081171398308, 132139529898, 0, 1440645255461, 407083420783]) (branchResiduals057 23 1) 35297932
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck057_24_0 :
    integerResidualCheck 57 24 0 (dualNumerators057 24 0) ∧
    integerMassCheck 57 24 0 (dualNumerators057 24 0) := by
  apply integerChecks_of_simple 57 24 0 (dualNumerators057 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 276221246109, 150663467366, 0, 969054410724, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 512185690040, 559007382209, 705016048726, 601815130180, 835192545885, 236000526363]) (branchResiduals057 24 0) 9356857
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck057_24_1 :
    integerResidualCheck 57 24 1 (dualNumerators057 24 1) ∧
    integerMassCheck 57 24 1 (dualNumerators057 24 1) := by
  apply integerChecks_of_simple 57 24 1 (dualNumerators057 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 395480180778, 20824623507, 0, 133942179966, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 587483804282, 282115266095, 66021086067, 82038644814, 0, 0, 115439864933, 32619865948]) (branchResiduals057 24 1) 9356857
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck057_25_0 :
    integerResidualCheck 57 25 0 (dualNumerators057 25 0) ∧
    integerMassCheck 57 25 0 (dualNumerators057 25 0) := by
  apply integerChecks_of_simple 57 25 0 (dualNumerators057 25 0)
    (![31307490826, 5763620872, 31307490826, 0, 1, 17498922567, 20720424919, 0, 627590994654, 447612295109, 373636362947, 136807905692, 0, 879936634611, 604415620636, 0, 0, 743128728921, 1507527629264, 1273145186690, 48522430940, 27120993710, 693739297027, 821454747430, 510444268639, 1, 136807905692, 743128728920, 0, 0, 791120467347, 1151750315250, 483956334634, 667793980617, 48522430940, 0, 449075259703, 523606992792, 0, 27120993710, 758385194830, 214297057664]) (branchResiduals057 25 0) 8671199
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck057_25_1 :
    integerResidualCheck 57 25 1 (dualNumerators057 25 1) ∧
    integerMassCheck 57 25 1 (dualNumerators057 25 1) := by
  apply integerChecks_of_simple 57 25 1 (dualNumerators057 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 0, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals057 25 1) 8671199
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck057_26_0 :
    integerResidualCheck 57 26 0 (dualNumerators057 26 0) ∧
    integerMassCheck 57 26 0 (dualNumerators057 26 0) := by
  apply integerChecks_of_simple 57 26 0 (dualNumerators057 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals057 26 0) 15099566
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck057_26_1 :
    integerResidualCheck 57 26 1 (dualNumerators057 26 1) ∧
    integerMassCheck 57 26 1 (dualNumerators057 26 1) := by
  apply integerChecks_of_simple 57 26 1 (dualNumerators057 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 879744679617, 350168760452, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals057 26 1) 15099566
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck057_27_0 :
    integerResidualCheck 57 27 0 (dualNumerators057 27 0) ∧
    integerMassCheck 57 27 0 (dualNumerators057 27 0) := by
  apply integerChecks_of_simple 57 27 0 (dualNumerators057 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312724, 1, 0, 0, 0, 0, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 436855949686, 304617712691, 595678484088, 168320989550]) (branchResiduals057 27 0) 7338775
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck057_27_1 :
    integerResidualCheck 57 27 1 (dualNumerators057 27 1) ∧
    integerMassCheck 57 27 1 (dualNumerators057 27 1) := by
  apply integerChecks_of_simple 57 27 1 (dualNumerators057 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 234337221023, 181967583262, 0, 1170399780726, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 540348413221, 991589527988, 377837583379, 0, 493953251519, 799807060596, 430830286610, 214386579479, 413046270426, 116714568052]) (branchResiduals057 27 1) 7338775
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck057_28_0 :
    integerResidualCheck 57 28 0 (dualNumerators057 28 0) ∧
    integerMassCheck 57 28 0 (dualNumerators057 28 0) := by
  apply integerChecks_of_simple 57 28 0 (dualNumerators057 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 1, 0, 0, 0, 0, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 374399059503, 471423145846, 503065535987, 142151330101]) (branchResiduals057 28 0) 10335557
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck057_28_1 :
    integerResidualCheck 57 28 1 (dualNumerators057 28 1) ∧
    integerMassCheck 57 28 1 (dualNumerators057 28 1) := by
  apply integerChecks_of_simple 57 28 1 (dualNumerators057 28 1)
    (![70965414109, 13064532837, 70965414109, 0, 1, 500061019298, 592120844340, 0, 99499623476, 70965414109, 0, 7115673227, 105323995459, 617878243177, 8425648624, 0, 0, 610762569951, 1239006666393, 201847170824, 109986917328, 775027817129, 109986917328, 130235198988, 7115673227, 0, 112439668685, 610762569950, 0, 0, 11028343493, 946600440957, 484611900989, 461988539969, 0, 109986917328, 455943846399, 343484151953, 11028343493, 0, 120236016734, 33975115531]) (branchResiduals057 28 1) 10335557
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck057_29_0 :
    integerResidualCheck 57 29 0 (dualNumerators057 29 0) ∧
    integerMassCheck 57 29 0 (dualNumerators057 29 0) := by
  apply integerChecks_of_simple 57 29 0 (dualNumerators057 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals057 29 0) 40352153
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck057_29_1 :
    integerResidualCheck 57 29 1 (dualNumerators057 29 1) ∧
    integerMassCheck 57 29 1 (dualNumerators057 29 1) := by
  apply integerChecks_of_simple 57 29 1 (dualNumerators057 29 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 1832818137783, 355072182930, 0, 1317842481106, 1766557277936, 81171398308, 132139529898, 0, 1440645255461, 407083420783]) (branchResiduals057 29 1) 40352153
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck057_30_0 :
    integerResidualCheck 57 30 0 (dualNumerators057 30 0) ∧
    integerMassCheck 57 30 0 (dualNumerators057 30 0) := by
  apply integerChecks_of_simple 57 30 0 (dualNumerators057 30 0)
    (![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 77683757550, 37915592377, 0, 243869815754, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 1, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 111490371098, 207711178340, 155908037259, 36358164526, 101823264420, 167750512114, 179163558800, 0, 269573776534, 0]) (branchResiduals057 30 0) 7680628
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck057_30_1 :
    integerResidualCheck 57 30 1 (dualNumerators057 30 1) ∧
    integerMassCheck 57 30 1 (dualNumerators057 30 1) := by
  apply integerChecks_of_simple 57 30 1 (dualNumerators057 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 491724510490, 107456641334, 0, 691151837050, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 212932307485, 691717317156, 544901951702, 0, 185534744901, 578464728737, 621279733097, 307371055990, 536287180313, 227712293325]) (branchResiduals057 30 1) 7680628
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck057_31_0 :
    integerResidualCheck 57 31 0 (dualNumerators057 31 0) ∧
    integerMassCheck 57 31 0 (dualNumerators057 31 0) := by
  apply integerChecks_of_simple 57 31 0 (dualNumerators057 31 0)
    (![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1719079079316, 0, 231835083176, 1259308150412, 2035556695381, 0, 0, 1259308150414, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079315, 2, 231835083174, 1259308150413, 0, 0, 2664343059941, 1951759503826, 1707419806160, 244339697667, 668308387684, 1612704621868, 1648310233018, 0, 957609719416, 1706733340526, 1648310233018, 0]) (branchResiduals057 31 0) 32891612
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck057_31_1 :
    integerResidualCheck 57 31 1 (dualNumerators057 31 1) ∧
    integerMassCheck 57 31 1 (dualNumerators057 31 1) := by
  apply integerChecks_of_simple 57 31 1 (dualNumerators057 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 274671058114, 217988955956, 0, 1402086139076, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 741061026801, 808805463926, 18993131489, 744564115640, 845258320866, 704608169862]) (branchResiduals057 31 1) 32891612
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck057_32_0 :
    integerResidualCheck 57 32 0 (dualNumerators057 32 0) ∧
    integerMassCheck 57 32 0 (dualNumerators057 32 0) := by
  apply integerChecks_of_simple 57 32 0 (dualNumerators057 32 0)
    (![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 979882959195, 1099655708204, 1160276651773, 0, 382837210862, 2079538667397, 0, 979882959196, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 180393692578, 979882959195, 0, 0, 3223007296772, 1518687763292, 1272220299089, 246467464203, 0, 914758491801, 1226226422667, 56343779290, 169611716433, 3053395580339, 0, 1282570201956]) (branchResiduals057 32 0) 67647473
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck057_32_1 :
    integerResidualCheck 57 32 1 (dualNumerators057 32 1) ∧
    integerMassCheck 57 32 1 (dualNumerators057 32 1) := by
  apply integerChecks_of_simple 57 32 1 (dualNumerators057 32 1)
    (![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1307998858623, 638403098873, 0, 4106153599144, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957494, 2, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 1877217101011, 3497333197567, 2625098749289, 612179935686, 1714447367673, 2824496204857, 3016663171407, 0, 4538943572529, 0]) (branchResiduals057 32 1) 67647473
    branchSparseDots057 branchIntegerCurvature057 branchDots057
    branchIntegerCurvature057_entry rfl
    (congrFun (congrFun branchResiduals057_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks057 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 57 j s (dualNumerators057 j s) ∧
    integerMassCheck 57 j s (dualNumerators057 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck057_0_0
    · exact integerCheck057_0_1
  · fin_cases s
    · exact integerCheck057_1_0
    · exact integerCheck057_1_1
  · fin_cases s
    · exact integerCheck057_2_0
    · exact integerCheck057_2_1
  · fin_cases s
    · exact integerCheck057_3_0
    · exact integerCheck057_3_1
  · fin_cases s
    · exact integerCheck057_4_0
    · exact integerCheck057_4_1
  · fin_cases s
    · exact integerCheck057_5_0
    · exact integerCheck057_5_1
  · fin_cases s
    · exact integerCheck057_6_0
    · exact integerCheck057_6_1
  · fin_cases s
    · exact integerCheck057_7_0
    · exact integerCheck057_7_1
  · fin_cases s
    · exact integerCheck057_8_0
    · exact integerCheck057_8_1
  · fin_cases s
    · exact integerCheck057_9_0
    · exact integerCheck057_9_1
  · fin_cases s
    · exact integerCheck057_10_0
    · exact integerCheck057_10_1
  · fin_cases s
    · exact integerCheck057_11_0
    · exact integerCheck057_11_1
  · fin_cases s
    · exact integerCheck057_12_0
    · exact integerCheck057_12_1
  · fin_cases s
    · exact integerCheck057_13_0
    · exact integerCheck057_13_1
  · fin_cases s
    · exact integerCheck057_14_0
    · exact integerCheck057_14_1
  · fin_cases s
    · exact integerCheck057_15_0
    · exact integerCheck057_15_1
  · fin_cases s
    · exact integerCheck057_16_0
    · exact integerCheck057_16_1
  · fin_cases s
    · exact integerCheck057_17_0
    · exact integerCheck057_17_1
  · fin_cases s
    · exact integerCheck057_18_0
    · exact integerCheck057_18_1
  · fin_cases s
    · exact integerCheck057_19_0
    · exact integerCheck057_19_1
  · fin_cases s
    · exact integerCheck057_20_0
    · exact integerCheck057_20_1
  · fin_cases s
    · exact integerCheck057_21_0
    · exact integerCheck057_21_1
  · fin_cases s
    · exact integerCheck057_22_0
    · exact integerCheck057_22_1
  · fin_cases s
    · exact integerCheck057_23_0
    · exact integerCheck057_23_1
  · fin_cases s
    · exact integerCheck057_24_0
    · exact integerCheck057_24_1
  · fin_cases s
    · exact integerCheck057_25_0
    · exact integerCheck057_25_1
  · fin_cases s
    · exact integerCheck057_26_0
    · exact integerCheck057_26_1
  · fin_cases s
    · exact integerCheck057_27_0
    · exact integerCheck057_27_1
  · fin_cases s
    · exact integerCheck057_28_0
    · exact integerCheck057_28_1
  · fin_cases s
    · exact integerCheck057_29_0
    · exact integerCheck057_29_1
  · fin_cases s
    · exact integerCheck057_30_0
    · exact integerCheck057_30_1
  · fin_cases s
    · exact integerCheck057_31_0
    · exact integerCheck057_31_1
  · fin_cases s
    · exact integerCheck057_32_0
    · exact integerCheck057_32_1

end ElevenSquare.Tasks.T06
