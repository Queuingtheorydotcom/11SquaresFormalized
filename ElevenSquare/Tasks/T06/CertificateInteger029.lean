import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual029
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
import ElevenSquare.Tasks.T06.SparseColumn24
import ElevenSquare.Tasks.T06.SparseColumn25
import ElevenSquare.Tasks.T06.SparseColumn27
import ElevenSquare.Tasks.T06.SparseColumn28
import ElevenSquare.Tasks.T06.SparseColumn30
import ElevenSquare.Tasks.T06.SparseColumn31
import ElevenSquare.Tasks.T06.SparseColumn33
import ElevenSquare.Tasks.T06.SparseColumn34
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn44
import ElevenSquare.Tasks.T06.SparseColumn47
import ElevenSquare.Tasks.T06.SparseColumn51

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix029 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral28, roundedGradientLiteral42, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix029_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = branchIntegerMatrix029 := by
  change roundedGradients ∘ branchRows 29 = branchIntegerMatrix029
  rw [show branchRows 29 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 32, 33, 34, 35, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral28_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral42_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, branchIntegerMatrix029]

theorem branchColumn029_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 0) i) = _
  rw [branchColumn029_0]
  exact sparseColumn00_sum n

theorem branchColumn029_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 1) i) = _
  rw [branchColumn029_1]
  exact sparseColumn01_sum n

theorem branchColumn029_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 2) i) = _
  rw [branchColumn029_2]
  exact sparseColumn02_sum n

theorem branchColumn029_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 3) i) = _
  rw [branchColumn029_3]
  exact sparseColumn03_sum n

theorem branchColumn029_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 4) i) = _
  rw [branchColumn029_4]
  exact sparseColumn04_sum n

theorem branchColumn029_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 5) i) = _
  rw [branchColumn029_5]
  exact sparseColumn05_sum n

theorem branchColumn029_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 6) i) = _
  rw [branchColumn029_6]
  exact sparseColumn06_sum n

theorem branchColumn029_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 7) i) = _
  rw [branchColumn029_7]
  exact sparseColumn07_sum n

theorem branchColumn029_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 8) i) = _
  rw [branchColumn029_8]
  exact sparseColumn08_sum n

theorem branchColumn029_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 9) i) = _
  rw [branchColumn029_9]
  exact sparseColumn09_sum n

theorem branchColumn029_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 10) i) = _
  rw [branchColumn029_10]
  exact sparseColumn10_sum n

theorem branchColumn029_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 11) i) = _
  rw [branchColumn029_11]
  exact sparseColumn11_sum n

theorem branchColumn029_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 12) = sparseColumn12 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 12) = sparseDot12 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 12) i) = _
  rw [branchColumn029_12]
  exact sparseColumn12_sum n

theorem branchColumn029_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 13) = sparseColumn13 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 13) = sparseDot13 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 13) i) = _
  rw [branchColumn029_13]
  exact sparseColumn13_sum n

theorem branchColumn029_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 14) = sparseColumn33 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 14) = sparseDot33 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 14) i) = _
  rw [branchColumn029_14]
  exact sparseColumn33_sum n

theorem branchColumn029_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 15) = sparseColumn15 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 15) = sparseDot15 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 15) i) = _
  rw [branchColumn029_15]
  exact sparseColumn15_sum n

theorem branchColumn029_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 16) = sparseColumn16 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 16) = sparseDot16 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 16) i) = _
  rw [branchColumn029_16]
  exact sparseColumn16_sum n

theorem branchColumn029_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 17) = sparseColumn34 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 17) = sparseDot34 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 17) i) = _
  rw [branchColumn029_17]
  exact sparseColumn34_sum n

theorem branchColumn029_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 18) i) = _
  rw [branchColumn029_18]
  exact sparseColumn18_sum n

theorem branchColumn029_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 19) i) = _
  rw [branchColumn029_19]
  exact sparseColumn19_sum n

theorem branchColumn029_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 20) = sparseColumn20 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 20) = sparseDot20 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 20) i) = _
  rw [branchColumn029_20]
  exact sparseColumn20_sum n

theorem branchColumn029_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 21) i) = _
  rw [branchColumn029_21]
  exact sparseColumn21_sum n

theorem branchColumn029_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 22) i) = _
  rw [branchColumn029_22]
  exact sparseColumn22_sum n

theorem branchColumn029_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 23) = sparseColumn47 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 23) = sparseDot47 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 23) i) = _
  rw [branchColumn029_23]
  exact sparseColumn47_sum n

theorem branchColumn029_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 24) i) = _
  rw [branchColumn029_24]
  exact sparseColumn24_sum n

theorem branchColumn029_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 25) i) = _
  rw [branchColumn029_25]
  exact sparseColumn25_sum n

theorem branchColumn029_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 26) = sparseColumn44 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 26) = sparseDot44 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 26) i) = _
  rw [branchColumn029_26]
  exact sparseColumn44_sum n

theorem branchColumn029_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 27) i) = _
  rw [branchColumn029_27]
  exact sparseColumn27_sum n

theorem branchColumn029_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 28) i) = _
  rw [branchColumn029_28]
  exact sparseColumn28_sum n

theorem branchColumn029_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 29) = sparseColumn51 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 29) = sparseDot51 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 29) i) = _
  rw [branchColumn029_29]
  exact sparseColumn51_sum n

theorem branchColumn029_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 30) i) = _
  rw [branchColumn029_30]
  exact sparseColumn30_sum n

theorem branchColumn029_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 31) i) = _
  rw [branchColumn029_31]
  exact sparseColumn31_sum n

theorem branchColumn029_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 29 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 29 i)) = _
  rw [branchIntegerMatrix029_eq]
  simp only [branchIntegerMatrix029, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot029_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 29 i) 32) i) = _
  rw [branchColumn029_32]
  exact sparseColumn43_sum n

def branchSparseDots029 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot12, sparseDot13, sparseDot33, sparseDot15, sparseDot16, sparseDot34, sparseDot18, sparseDot19, sparseDot20, sparseDot21, sparseDot22, sparseDot47, sparseDot24, sparseDot25, sparseDot44, sparseDot27, sparseDot28, sparseDot51, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot029_0 :
    branchSparseDots029 0 = sparseDot00 := rfl

private theorem branchSparseDot029_1 :
    branchSparseDots029 1 = sparseDot01 := rfl

private theorem branchSparseDot029_2 :
    branchSparseDots029 2 = sparseDot02 := rfl

private theorem branchSparseDot029_3 :
    branchSparseDots029 3 = sparseDot03 := rfl

private theorem branchSparseDot029_4 :
    branchSparseDots029 4 = sparseDot04 := rfl

private theorem branchSparseDot029_5 :
    branchSparseDots029 5 = sparseDot05 := rfl

private theorem branchSparseDot029_6 :
    branchSparseDots029 6 = sparseDot06 := rfl

private theorem branchSparseDot029_7 :
    branchSparseDots029 7 = sparseDot07 := rfl

private theorem branchSparseDot029_8 :
    branchSparseDots029 8 = sparseDot08 := rfl

private theorem branchSparseDot029_9 :
    branchSparseDots029 9 = sparseDot09 := rfl

private theorem branchSparseDot029_10 :
    branchSparseDots029 10 = sparseDot10 := rfl

private theorem branchSparseDot029_11 :
    branchSparseDots029 11 = sparseDot11 := rfl

private theorem branchSparseDot029_12 :
    branchSparseDots029 12 = sparseDot12 := rfl

private theorem branchSparseDot029_13 :
    branchSparseDots029 13 = sparseDot13 := rfl

private theorem branchSparseDot029_14 :
    branchSparseDots029 14 = sparseDot33 := rfl

private theorem branchSparseDot029_15 :
    branchSparseDots029 15 = sparseDot15 := rfl

private theorem branchSparseDot029_16 :
    branchSparseDots029 16 = sparseDot16 := rfl

private theorem branchSparseDot029_17 :
    branchSparseDots029 17 = sparseDot34 := rfl

private theorem branchSparseDot029_18 :
    branchSparseDots029 18 = sparseDot18 := rfl

private theorem branchSparseDot029_19 :
    branchSparseDots029 19 = sparseDot19 := rfl

private theorem branchSparseDot029_20 :
    branchSparseDots029 20 = sparseDot20 := rfl

private theorem branchSparseDot029_21 :
    branchSparseDots029 21 = sparseDot21 := rfl

private theorem branchSparseDot029_22 :
    branchSparseDots029 22 = sparseDot22 := rfl

private theorem branchSparseDot029_23 :
    branchSparseDots029 23 = sparseDot47 := rfl

private theorem branchSparseDot029_24 :
    branchSparseDots029 24 = sparseDot24 := rfl

private theorem branchSparseDot029_25 :
    branchSparseDots029 25 = sparseDot25 := rfl

private theorem branchSparseDot029_26 :
    branchSparseDots029 26 = sparseDot44 := rfl

private theorem branchSparseDot029_27 :
    branchSparseDots029 27 = sparseDot27 := rfl

private theorem branchSparseDot029_28 :
    branchSparseDots029 28 = sparseDot28 := rfl

private theorem branchSparseDot029_29 :
    branchSparseDots029 29 = sparseDot51 := rfl

private theorem branchSparseDot029_30 :
    branchSparseDots029 30 = sparseDot30 := rfl

private theorem branchSparseDot029_31 :
    branchSparseDots029 31 = sparseDot31 := rfl

private theorem branchSparseDot029_32 :
    branchSparseDots029 32 = sparseDot43 := rfl

theorem branchDots029 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 29 i) k) = branchSparseDots029 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot029_0 n
      _ = _ := congrFun branchSparseDot029_0.symm n
  · calc
      _ = sparseDot01 n := branchDot029_1 n
      _ = _ := congrFun branchSparseDot029_1.symm n
  · calc
      _ = sparseDot02 n := branchDot029_2 n
      _ = _ := congrFun branchSparseDot029_2.symm n
  · calc
      _ = sparseDot03 n := branchDot029_3 n
      _ = _ := congrFun branchSparseDot029_3.symm n
  · calc
      _ = sparseDot04 n := branchDot029_4 n
      _ = _ := congrFun branchSparseDot029_4.symm n
  · calc
      _ = sparseDot05 n := branchDot029_5 n
      _ = _ := congrFun branchSparseDot029_5.symm n
  · calc
      _ = sparseDot06 n := branchDot029_6 n
      _ = _ := congrFun branchSparseDot029_6.symm n
  · calc
      _ = sparseDot07 n := branchDot029_7 n
      _ = _ := congrFun branchSparseDot029_7.symm n
  · calc
      _ = sparseDot08 n := branchDot029_8 n
      _ = _ := congrFun branchSparseDot029_8.symm n
  · calc
      _ = sparseDot09 n := branchDot029_9 n
      _ = _ := congrFun branchSparseDot029_9.symm n
  · calc
      _ = sparseDot10 n := branchDot029_10 n
      _ = _ := congrFun branchSparseDot029_10.symm n
  · calc
      _ = sparseDot11 n := branchDot029_11 n
      _ = _ := congrFun branchSparseDot029_11.symm n
  · calc
      _ = sparseDot12 n := branchDot029_12 n
      _ = _ := congrFun branchSparseDot029_12.symm n
  · calc
      _ = sparseDot13 n := branchDot029_13 n
      _ = _ := congrFun branchSparseDot029_13.symm n
  · calc
      _ = sparseDot33 n := branchDot029_14 n
      _ = _ := congrFun branchSparseDot029_14.symm n
  · calc
      _ = sparseDot15 n := branchDot029_15 n
      _ = _ := congrFun branchSparseDot029_15.symm n
  · calc
      _ = sparseDot16 n := branchDot029_16 n
      _ = _ := congrFun branchSparseDot029_16.symm n
  · calc
      _ = sparseDot34 n := branchDot029_17 n
      _ = _ := congrFun branchSparseDot029_17.symm n
  · calc
      _ = sparseDot18 n := branchDot029_18 n
      _ = _ := congrFun branchSparseDot029_18.symm n
  · calc
      _ = sparseDot19 n := branchDot029_19 n
      _ = _ := congrFun branchSparseDot029_19.symm n
  · calc
      _ = sparseDot20 n := branchDot029_20 n
      _ = _ := congrFun branchSparseDot029_20.symm n
  · calc
      _ = sparseDot21 n := branchDot029_21 n
      _ = _ := congrFun branchSparseDot029_21.symm n
  · calc
      _ = sparseDot22 n := branchDot029_22 n
      _ = _ := congrFun branchSparseDot029_22.symm n
  · calc
      _ = sparseDot47 n := branchDot029_23 n
      _ = _ := congrFun branchSparseDot029_23.symm n
  · calc
      _ = sparseDot24 n := branchDot029_24 n
      _ = _ := congrFun branchSparseDot029_24.symm n
  · calc
      _ = sparseDot25 n := branchDot029_25 n
      _ = _ := congrFun branchSparseDot029_25.symm n
  · calc
      _ = sparseDot44 n := branchDot029_26 n
      _ = _ := congrFun branchSparseDot029_26.symm n
  · calc
      _ = sparseDot27 n := branchDot029_27 n
      _ = _ := congrFun branchSparseDot029_27.symm n
  · calc
      _ = sparseDot28 n := branchDot029_28 n
      _ = _ := congrFun branchSparseDot029_28.symm n
  · calc
      _ = sparseDot51 n := branchDot029_29 n
      _ = _ := congrFun branchSparseDot029_29.symm n
  · calc
      _ = sparseDot30 n := branchDot029_30 n
      _ = _ := congrFun branchSparseDot029_30.symm n
  · calc
      _ = sparseDot31 n := branchDot029_31 n
      _ = _ := congrFun branchSparseDot029_31.symm n
  · calc
      _ = sparseDot43 n := branchDot029_32 n
      _ = _ := congrFun branchSparseDot029_32.symm n

def branchIntegerCurvature029 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101981296, 101981296, 44932602, 44932602, 106371291, 106371291, 88123140, 88123140, 289103692, 289103692]

theorem branchIntegerCurvature029_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 29 i)) = branchIntegerCurvature029 := by
  change curvatureNumerators ∘ branchRows 29 = branchIntegerCurvature029
  rw [show branchRows 29 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 32, 33, 34, 35, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature029_entry (i : Fin 42) :
    curvatureNumerators (branchRows 29 i) = branchIntegerCurvature029 i :=
  congrFun branchIntegerCurvature029_eq i

def branchResiduals029 : Fin 33 → Fin 2 → ℕ := ![![1300358336468381, 33000000000000], ![1546816113778914, 33000000000000], ![1581653545167794, 1338393010626587], ![33000000000000, 1025699967847139], ![857891589261805, 33000000000000], ![1056307365133946, 892416068851973], ![724184911205947, 622122527367398], ![33000000000000, 760237208014157], ![1581035281472122, 1130499627291951], ![1027358150485491, 33000000000000], ![33000000000000, 777643431646002], ![483704323821615, 465887304914862], ![991199967847139, 66000000000000], ![33000000000000, 406703158519065], ![466763505236984, 578045837872483], ![922621511546050, 33000000000000], ![66000000000000, 743738389000119], ![445473203725890, 809789971105369], ![622901112200756, 265008284230372], ![632916882910007, 507587812833503], ![1358631289954845, 950345257352977], ![754727018943389, 388586934288278], ![469986195410709, 105616699803590], ![1360601484198278, 950345257352977], ![673006328062495, 230503409392854], ![504597306550354, 223581994926723], ![398970616796057, 852454589586214], ![408760111432613, 551427497466098], ![285791123956719, 308238571147190], ![398970616796057, 950345257352977], ![105616699803590, 554820378659989], ![966757458432735, 651647106671293], ![2026761002942682, 950345257352977]]

theorem branchResiduals029_eq : residualNumerators 29 = branchResiduals029 := rfl

theorem integerCheck029_0_0 :
    integerResidualCheck 29 0 0 (dualNumerators029 0 0) ∧
    integerMassCheck 29 0 0 (dualNumerators029 0 0) := by
  apply integerChecks_of_simple 29 0 0 (dualNumerators029 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1011030237961, 258120108700, 0, 1660206247774, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1607511062796, 565535261271, 1308901425339, 0, 445670439042, 1389522106843, 1485808378804, 481205215181, 818327875519, 1016864670366]) (branchResiduals029 0 0) 18767167
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck029_0_1 :
    integerResidualCheck 29 0 1 (dualNumerators029 0 1) ∧
    integerMassCheck 29 0 1 (dualNumerators029 0 1) := by
  apply integerChecks_of_simple 29 0 1 (dualNumerators029 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals029 0 1) 18767167
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck029_1_0 :
    integerResidualCheck 29 1 0 (dualNumerators029 1 0) ∧
    integerMassCheck 29 1 0 (dualNumerators029 1 0) := by
  apply integerChecks_of_simple 29 1 0 (dualNumerators029 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1197158056821, 305639293618, 0, 1965845541389, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 1903449321293, 669648709827, 1549866490727, 0, 527717111470, 1645329212598, 1759341515999, 569793739799, 968979732271, 1204066591796]) (branchResiduals029 1 0) 22176635
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck029_1_1 :
    integerResidualCheck 29 1 1 (dualNumerators029 1 1) ∧
    integerMassCheck 29 1 1 (dualNumerators029 1 1) := by
  apply integerChecks_of_simple 29 1 1 (dualNumerators029 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals029 1 1) 22176635
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck029_2_0 :
    integerResidualCheck 29 2 0 (dualNumerators029 2 0) ∧
    integerMassCheck 29 2 0 (dualNumerators029 2 0) := by
  apply integerChecks_of_simple 29 2 0 (dualNumerators029 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1197158056822, 305639293619, 0, 1965845541391, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 1903449321295, 669648709827, 1549866490728, 0, 527717111470, 1645329212599, 1759341516001, 569793739799, 968979732272, 1204066591797]) (branchResiduals029 2 0) 22681452
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck029_2_1 :
    integerResidualCheck 29 2 1 (dualNumerators029 2 1) ∧
    integerMassCheck 29 2 1 (dualNumerators029 2 1) := by
  apply integerChecks_of_simple 29 2 1 (dualNumerators029 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1011030237961, 258120108700, 0, 1660206247773, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1607511062795, 565535261271, 1308901425338, 0, 445670439042, 1389522106842, 1485808378803, 481205215180, 818327875518, 1016864670365]) (branchResiduals029 2 1) 22681452
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck029_3_0 :
    integerResidualCheck 29 3 0 (dualNumerators029 3 0) ∧
    integerMassCheck 29 3 0 (dualNumerators029 3 0) := by
  apply integerChecks_of_simple 29 3 0 (dualNumerators029 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals029 3 0) 16360330
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck029_3_1 :
    integerResidualCheck 29 3 1 (dualNumerators029 3 1) ∧
    integerMassCheck 29 3 1 (dualNumerators029 3 1) := by
  apply integerChecks_of_simple 29 3 1 (dualNumerators029 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 796619754801, 203380245200, 0, 1308124173107, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 351156535721, 1094844366154, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals029 3 1) 16360330
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck029_4_0 :
    integerResidualCheck 29 4 0 (dualNumerators029 4 0) ∧
    integerMassCheck 29 4 0 (dualNumerators029 4 0) := by
  apply integerChecks_of_simple 29 4 0 (dualNumerators029 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 672765518030, 171759757645, 0, 1104743927909, 1000000000001, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1069679196818, 376321705057, 870976665588, 0, 296560570134, 924623740146, 988695101419, 320206323920, 544536410901, 676647899379]) (branchResiduals029 4 0) 13760362
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck029_4_1 :
    integerResidualCheck 29 4 1 (dualNumerators029 4 1) ∧
    integerMassCheck 29 4 1 (dualNumerators029 4 1) := by
  apply integerChecks_of_simple 29 4 1 (dualNumerators029 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals029 4 1) 13760362
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck029_5_0 :
    integerResidualCheck 29 5 0 (dualNumerators029 5 0) ∧
    integerMassCheck 29 5 0 (dualNumerators029 5 0) := by
  apply integerChecks_of_simple 29 5 0 (dualNumerators029 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 796619754801, 203380245201, 0, 1308124173108, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000000, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1266604123796, 445601470905, 1031321016288, 0, 351156535721, 1094844366155, 1170711084557, 379155406172, 644784030255, 801216871620]) (branchResiduals029 5 0) 17641130
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck029_5_1 :
    integerResidualCheck 29 5 1 (dualNumerators029 5 1) ∧
    integerMassCheck 29 5 1 (dualNumerators029 5 1) := by
  apply integerChecks_of_simple 29 5 1 (dualNumerators029 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1069679196817, 376321705056, 870976665588, 0, 296560570134, 924623740145, 988695101418, 320206323920, 544536410901, 676647899378]) (branchResiduals029 5 1) 17641130
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck029_6_0 :
    integerResidualCheck 29 6 0 (dualNumerators029 6 0) ∧
    integerMassCheck 29 6 0 (dualNumerators029 6 0) := by
  apply integerChecks_of_simple 29 6 0 (dualNumerators029 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 0, 70552396879, 187567711821, 1472638535954, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 1, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 877488274356, 957704271528, 2719950702, 106626845062, 818327875519, 1016864670366]) (branchResiduals029 6 0) 8962451
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck029_6_1 :
    integerResidualCheck 29 6 1 (dualNumerators029 6 1) ∧
    integerMassCheck 29 6 1 (dualNumerators029 6 1) := by
  apply integerChecks_of_simple 29 6 1 (dualNumerators029 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949782, 1, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals029 6 1) 8962451
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck029_7_0 :
    integerResidualCheck 29 7 0 (dualNumerators029 7 0) ∧
    integerMassCheck 29 7 0 (dualNumerators029 7 0) := by
  apply integerChecks_of_simple 29 7 0 (dualNumerators029 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals029 7 0) 10424794
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck029_7_1 :
    integerResidualCheck 29 7 1 (dualNumerators029 7 1) ∧
    integerMassCheck 29 7 1 (dualNumerators029 7 1) := by
  apply integerChecks_of_simple 29 7 1 (dualNumerators029 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 598579028412, 152819646809, 0, 982922770697, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 951724660649, 334824354914, 774933245365, 0, 263858555736, 822664606300, 879670758001, 284896869900, 484489866137, 602033295899]) (branchResiduals029 7 1) 10424794
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck029_8_0 :
    integerResidualCheck 29 8 0 (dualNumerators029 8 0) ∧
    integerMassCheck 29 8 0 (dualNumerators029 8 0) := by
  apply integerChecks_of_simple 29 8 0 (dualNumerators029 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1197158056824, 305639293618, 0, 1965845541393, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 1903449321297, 669648709828, 1549866490730, 0, 527717111471, 1645329212600, 1759341516002, 569793739800, 968979732273, 1204066591798]) (branchResiduals029 8 0) 22681452
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck029_8_1 :
    integerResidualCheck 29 8 1 (dualNumerators029 8 1) ∧
    integerMassCheck 29 8 1 (dualNumerators029 8 1) := by
  apply integerChecks_of_simple 29 8 1 (dualNumerators029 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590429, 217988955956, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546384, 0, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1357583723455, 477608822428, 1105400337063, 0, 376379950391, 1173486540335, 1254802730706, 406389967006, 691098574663, 858767916063]) (branchResiduals029 8 1) 22681452
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck029_9_0 :
    integerResidualCheck 29 9 0 (dualNumerators029 9 0) ∧
    integerMassCheck 29 9 0 (dualNumerators029 9 0) := by
  apply integerChecks_of_simple 29 9 0 (dualNumerators029 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 887477428322, 296619754801, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 703380245200, 296619754801, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 351156535721, 1094844366154, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals029 9 0) 16350530
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck029_9_1 :
    integerResidualCheck 29 9 1 (dualNumerators029 9 1) ∧
    integerMassCheck 29 9 1 (dualNumerators029 9 1) := by
  apply integerChecks_of_simple 29 9 1 (dualNumerators029 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals029 9 1) 16350530
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck029_10_0 :
    integerResidualCheck 29 10 0 (dualNumerators029 10 0) ∧
    integerMassCheck 29 10 0 (dualNumerators029 10 0) := by
  apply integerChecks_of_simple 29 10 0 (dualNumerators029 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals029 10 0) 10683139
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck029_10_1 :
    integerResidualCheck 29 10 1 (dualNumerators029 10 1) ∧
    integerMassCheck 29 10 1 (dualNumerators029 10 1) := by
  apply integerChecks_of_simple 29 10 1 (dualNumerators029 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 560661867464, 344525275673, 0, 844525275674, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 419928145920, 344525275674, 155474724327, 844525275674, 0, 0, 1184800741849, 1308901425339, 968259856239, 340641569100, 788396879662, 0, 268442815247, 836957521818, 894954094286, 289846647564, 492907358117, 612492978948]) (branchResiduals029 10 1) 10683139
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck029_11_0 :
    integerResidualCheck 29 11 0 (dualNumerators029 11 0) ∧
    integerMassCheck 29 11 0 (dualNumerators029 11 0) := by
  apply integerChecks_of_simple 29 11 0 (dualNumerators029 11 0)
    (![301584229951, 55520807208, 301584229951, 0, 1, 453219981703, 536656503669, 0, 422847068578, 301584229950, 0, 453219981704, 546780018297, 0, 582744499174, 0, 0, 500692022794, 1015715082378, 857797059952, 467415292132, 702430462570, 467415292132, 553465130761, 453219981704, 0, 0, 546780018297, 0, 46087995504, 702430462570, 776005788302, 574050297812, 201955490491, 467415292132, 0, 159151158695, 496205343596, 530589656322, 171840806248, 292229006395, 363127495896]) (branchResiduals029 11 0) 15120968
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck029_11_1 :
    integerResidualCheck 29 11 1 (dualNumerators029 11 1) ∧
    integerMassCheck 29 11 1 (dualNumerators029 11 1) := by
  apply integerChecks_of_simple 29 11 1 (dualNumerators029 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 548759091280, 193057841557, 446822154676, 0, 152139360530, 474343789173, 507213215908, 164269934257, 279354134309, 347129015395]) (branchResiduals029 11 1) 15120968
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck029_12_0 :
    integerResidualCheck 29 12 0 (dualNumerators029 12 0) ∧
    integerMassCheck 29 12 0 (dualNumerators029 12 0) := by
  apply integerChecks_of_simple 29 12 0 (dualNumerators029 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 351156535721, 1094844366154, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals029 12 0) 16348076
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck029_12_1 :
    integerResidualCheck 29 12 1 (dualNumerators029 12 1) ∧
    integerMassCheck 29 12 1 (dualNumerators029 12 1) := by
  apply integerChecks_of_simple 29 12 1 (dualNumerators029 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals029 12 1) 16348076
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck029_13_0 :
    integerResidualCheck 29 13 0 (dualNumerators029 13 0) ∧
    integerMassCheck 29 13 0 (dualNumerators029 13 0) := by
  apply integerChecks_of_simple 29 13 0 (dualNumerators029 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals029 13 0) 13962901
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck029_13_1 :
    integerResidualCheck 29 13 1 (dualNumerators029 13 1) ∧
    integerMassCheck 29 13 1 (dualNumerators029 13 1) := by
  apply integerChecks_of_simple 29 13 1 (dualNumerators029 13 1)
    (![271504920046, 49983290985, 271504920046, 0, 1, 408016874475, 483131631732, 0, 380673285087, 271504920045, 408016874475, 0, 0, 16868368268, 0, 0, 450754164561, 0, 914410021623, 772242375590, 420796377646, 632371681400, 420796377646, 498263805438, 408016874475, 0, 0, 16868368268, 500000000001, 16868368269, 632371681400, 698608775208, 516795855788, 181812919420, 420796377646, 0, 143277792156, 446714976315, 477669877634, 154701803767, 263082764736, 326910003735]) (branchResiduals029 13 1) 13962901
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck029_14_0 :
    integerResidualCheck 29 14 0 (dualNumerators029 14 0) ∧
    integerMassCheck 29 14 0 (dualNumerators029 14 0) := by
  apply integerChecks_of_simple 29 14 0 (dualNumerators029 14 0)
    (![288297190339, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 0, 433252253780, 0, 0, 1079760519503, 0, 478632796615, 1, 970965240730, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253780, 0, 0, 566747746222, 0, 671483150164, 741816932837, 548759091280, 193057841557, 446822154676, 0, 152139360530, 474343789174, 507213215908, 164269934257, 279354134309, 347129015395]) (branchResiduals029 14 0) 20161291
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck029_14_1 :
    integerResidualCheck 29 14 1 (dualNumerators029 14 1) ∧
    integerMassCheck 29 14 1 (dualNumerators029 14 1) := by
  apply integerChecks_of_simple 29 14 1 (dualNumerators029 14 1)
    (![362006560060, 66644387979, 362006560061, 0, 1, 544022499300, 644175508976, 0, 507564380116, 362006560060, 544022499300, 0, 0, 355824491024, 0, 1000000000000, 601005552747, 0, 1219213362163, 1029656500786, 561061836861, 843162241867, 561061836861, 664351740584, 544022499300, 0, 0, 355824491024, 0, 355824491025, 843162241867, 931478366944, 689061141051, 242417225893, 561061836861, 0, 191037056208, 595619968419, 636893170178, 206269071689, 350777019648, 435880004980]) (branchResiduals029 14 1) 20161291
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck029_15_0 :
    integerResidualCheck 29 15 0 (dualNumerators029 15 0) ∧
    integerMassCheck 29 15 0 (dualNumerators029 15 0) := by
  apply integerChecks_of_simple 29 15 0 (dualNumerators029 15 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546385, 0, 844525275675, 602334801077, 221089960014, 684097183123, 0, 1184097183122, 1071829546385, 0, 0, 0, 2028622458796, 1713222941252, 933538524389, 1402919220983, 933538524389, 1105400337064, 905187143136, 0, 684097183123, 500000000000, 0, 0, 1402919220983, 1549866490727, 1146513768302, 403352722425, 933538524389, 0, 317862381362, 991039043977, 1059712622067, 343206598917, 583650214286, 725251211053]) (branchResiduals029 15 0) 12900283
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck029_15_1 :
    integerResidualCheck 29 15 1 (dualNumerators029 15 1) ∧
    integerMassCheck 29 15 1 (dualNumerators029 15 1) := by
  apply integerChecks_of_simple 29 15 1 (dualNumerators029 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals029 15 1) 12900283
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck029_16_0 :
    integerResidualCheck 29 16 0 (dualNumerators029 16 0) ∧
    integerMassCheck 29 16 0 (dualNumerators029 16 0) := by
  apply integerChecks_of_simple 29 16 0 (dualNumerators029 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals029 16 0) 10683060
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck029_16_1 :
    integerResidualCheck 29 16 1 (dualNumerators029 16 1) ∧
    integerMassCheck 29 16 1 (dualNumerators029 16 1) := by
  apply integerChecks_of_simple 29 16 1 (dualNumerators029 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 0, 0, 0, 0, 1184800741849, 1308901425339, 968259856239, 340641569100, 788396879662, 0, 268442815247, 836957521818, 894954094286, 289846647564, 492907358117, 612492978948]) (branchResiduals029 16 1) 10683060
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck029_17_0 :
    integerResidualCheck 29 17 0 (dualNumerators029 17 0) ∧
    integerMassCheck 29 17 0 (dualNumerators029 17 0) := by
  apply integerChecks_of_simple 29 17 0 (dualNumerators029 17 0)
    (![275782051153, 50770698773, 275782051153, 0, 1, 414444535771, 490742607366, 0, 386670191328, 275782051153, 414444535771, 0, 0, 0, 1032887523019, 0, 0, 457855084348, 928815106981, 784407834273, 427425359826, 642333698256, 427425359826, 506113164564, 414444535771, 0, 0, 0, 0, 542144915654, 642333698256, 709614252839, 524937158092, 184677094748, 427425359826, 0, 145534907430, 453752265072, 485194811960, 157138886296, 267227218091, 332059954410]) (branchResiduals029 17 0) 15120968
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck029_17_1 :
    integerResidualCheck 29 17 1 (dualNumerators029 17 1) ∧
    integerMassCheck 29 17 1 (dualNumerators029 17 1) := by
  apply integerChecks_of_simple 29 17 1 (dualNumerators029 17 1)
    (![508686963928, 93647837150, 508686963928, 0, 1, 764453421592, 905187143136, 0, 713222941253, 508686963927, 764453421593, 0, 0, 1000000000000, 905187143136, 0, 844525275674, 0, 1713222941251, 1446860076751, 788396879661, 1184800741848, 788396879661, 933538524388, 764453421592, 1, 0, 1000000000000, 0, 0, 1184800741848, 1308901425338, 968259856239, 340641569100, 788396879661, 0, 268442815246, 836957521818, 894954094285, 289846647563, 492907358117, 612492978947]) (branchResiduals029 17 1) 15120968
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck029_18_0 :
    integerResidualCheck 29 18 0 (dualNumerators029 18 0) ∧
    integerMassCheck 29 18 0 (dualNumerators029 18 0) := by
  apply integerChecks_of_simple 29 18 0 (dualNumerators029 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 562515489548, 74022925577, 0, 476109064652, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 1025720546095, 242676153333, 763999473637, 0, 172711632462, 898481439786, 863239815324, 123309744339, 477654049462, 593539022787]) (branchResiduals029 18 0) 13565580
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck029_18_1 :
    integerResidualCheck 29 18 1 (dualNumerators029 18 1) ∧
    integerMassCheck 29 18 1 (dualNumerators029 18 1) := by
  apply integerChecks_of_simple 29 18 1 (dualNumerators029 18 1)
    (![546080038515, 100531796850, 546080038516, 0, 1, 184109219884, 218003208651, 0, 74499415779, 53134692444, 91228628230, 92880591654, 0, 597399944305, 218003208651, 0, 0, 504519352652, 178954014012, 151131188017, 846351152950, 285344710532, 82351679314, 97512391500, 184109219884, 1, 92880591654, 504519352652, 0, 0, 285344710532, 781937638598, 13715132590, 123005639922, 82351679314, 0, 115464148095, 0, 97501467496, 187843243037, 51486440059, 63977708037]) (branchResiduals029 18 1) 13565580
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck029_19_0 :
    integerResidualCheck 29 19 0 (dualNumerators029 19 0) ∧
    integerMassCheck 29 19 0 (dualNumerators029 19 0) := by
  apply integerChecks_of_simple 29 19 0 (dualNumerators029 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 216703300504, 217988955956, 0, 1402086139076, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 901168865389, 170024206859, 593870256538, 51346609551, 110937400584, 793712224057, 673714962064, 0, 403390917798, 501258706842]) (branchResiduals029 19 0) 8248658
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck029_19_1 :
    integerResidualCheck 29 19 1 (dualNumerators029 19 1) ∧
    integerMassCheck 29 19 1 (dualNumerators029 19 1) := by
  apply integerChecks_of_simple 29 19 1 (dualNumerators029 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 1, 0, 0, 0, 0, 987477735649, 0, 405068248518, 358931225119, 460183470977, 0, 316789159358, 328427706730, 529741159093, 457736576556, 287707656866, 357509209222]) (branchResiduals029 19 1) 8248658
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck029_20_0 :
    integerResidualCheck 29 20 0 (dualNumerators029 20 0) ∧
    integerMassCheck 29 20 0 (dualNumerators029 20 0) := by
  apply integerChecks_of_simple 29 20 0 (dualNumerators029 20 0)
    (![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 1920171252554, 185761786322, 0, 1194803767136, 2493629379175, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038874, 2, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 156880523801, 1406999830004, 941979561817, 0, 1320736486917, 0, 1115270391492, 2148644657176, 588927568327, 731808918591]) (branchResiduals029 20 0) 35312013
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck029_20_1 :
    integerResidualCheck 29 20 1 (dualNumerators029 20 1) ∧
    integerMassCheck 29 20 1 (dualNumerators029 20 1) := by
  apply integerChecks_of_simple 29 20 1 (dualNumerators029 20 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 1300649428514, 887240892199, 0, 1317842481106, 766557277936, 1081171398308, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals029 20 1) 35312013
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck029_21_0 :
    integerResidualCheck 29 21 0 (dualNumerators029 21 0) ∧
    integerMassCheck 29 21 0 (dualNumerators029 21 0) := by
  apply integerChecks_of_simple 29 21 0 (dualNumerators029 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 759767979803, 549133445537, 757887471419, 892563449519, 583650214286, 725251211053]) (branchResiduals029 21 0) 11182451
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck029_21_1 :
    integerResidualCheck 29 21 1 (dualNumerators029 21 1) ∧
    integerMassCheck 29 21 1 (dualNumerators029 21 1) := by
  apply integerChecks_of_simple 29 21 1 (dualNumerators029 21 1)
    (![113874129702, 20963906509, 113874129702, 0, 1, 11418112698, 13520155082, 0, 159661338854, 113874129702, 0, 11418112698, 207483478989, 1200472654287, 13520155082, 0, 0, 1189054541591, 1567617472129, 323892577801, 176489697786, 17696550257, 176489697786, 208980953998, 11418112698, 0, 218901591686, 1189054541590, 0, 0, 17696550257, 1842875789658, 878795318822, 964080470836, 0, 176489697786, 102659812730, 144793946225, 17696550257, 0, 110341723711, 137112035244]) (branchResiduals029 21 1) 11182451
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck029_22_0 :
    integerResidualCheck 29 22 0 (dualNumerators029 22 0) ∧
    integerMassCheck 29 22 0 (dualNumerators029 22 0) := by
  apply integerChecks_of_simple 29 22 0 (dualNumerators029 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 583695195717, 0, 612220343875, 0, 492945346072, 0, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 583695195717, 0, 0, 0, 801336080718, 763999473637, 136031845564, 627967628074, 31046690248, 429136780729, 645216866088, 0, 95974191249, 705361889470, 287707656866, 357509209222]) (branchResiduals029 22 0) 6465674
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck029_22_1 :
    integerResidualCheck 29 22 1 (dualNumerators029 22 1) ∧
    integerMassCheck 29 22 1 (dualNumerators029 22 1) := by
  apply integerChecks_of_simple 29 22 1 (dualNumerators029 22 1)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 0, 5063622582, 10371186464, 88904172359, 5995821236, 0, 0, 83840549778, 1170080822236, 143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 17855961539, 112085697126, 0, 78268383123, 45526836155, 64212178950, 7847938961, 0, 48933554844, 60805460262]) (branchResiduals029 22 1) 6465674
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck029_23_0 :
    integerResidualCheck 29 23 0 (dualNumerators029 23 0) ∧
    integerMassCheck 29 23 0 (dualNumerators029 23 0) := by
  apply integerChecks_of_simple 29 23 0 (dualNumerators029 23 0)
    (![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 1920171252556, 185761786321, 0, 1194803767136, 2493629379175, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038876, 0, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 1156880523801, 406999830004, 941979561817, 0, 1320736486917, 0, 1115270391492, 2148644657176, 588927568327, 731808918591]) (branchResiduals029 23 0) 35297932
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck029_23_1 :
    integerResidualCheck 29 23 1 (dualNumerators029 23 1) ∧
    integerMassCheck 29 23 1 (dualNumerators029 23 1) := by
  apply integerChecks_of_simple 29 23 1 (dualNumerators029 23 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 766557277936, 1081171398308, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals029 23 1) 35297932
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck029_24_0 :
    integerResidualCheck 29 24 0 (dualNumerators029 24 0) ∧
    integerMassCheck 29 24 0 (dualNumerators029 24 0) := by
  apply integerChecks_of_simple 29 24 0 (dualNumerators029 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 276221246109, 150663467366, 0, 969054410724, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 512185690040, 559007382209, 705016048726, 601815130180, 477654049462, 593539022787]) (branchResiduals029 24 0) 9356857
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck029_24_1 :
    integerResidualCheck 29 24 1 (dualNumerators029 24 1) ∧
    integerMassCheck 29 24 1 (dualNumerators029 24 1) := by
  apply integerChecks_of_simple 29 24 1 (dualNumerators029 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 395480180778, 20824623507, 0, 133942179966, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 587483804282, 282115266095, 66021086067, 82038644814, 0, 0, 66021086067, 82038644814]) (branchResiduals029 24 1) 9356857
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck029_25_0 :
    integerResidualCheck 29 25 0 (dualNumerators029 25 0) ∧
    integerMassCheck 29 25 0 (dualNumerators029 25 0) := by
  apply integerChecks_of_simple 29 25 0 (dualNumerators029 25 0)
    (![31307490826, 5763620872, 31307490826, 0, 1, 17498922567, 20720424919, 0, 627590994654, 447612295109, 373636362947, 136807905692, 0, 879936634611, 604415620636, 0, 0, 743128728921, 1507527629264, 1273145186690, 48522430940, 27120993710, 693739297027, 821454747430, 510444268639, 1, 136807905692, 743128728920, 0, 0, 791120467347, 1151750315250, 639144727059, 512605588192, 48522430940, 0, 449075259703, 523606992792, 0, 27120993710, 433727241876, 538955010618]) (branchResiduals029 25 0) 8671199
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck029_25_1 :
    integerResidualCheck 29 25 1 (dualNumerators029 25 1) ∧
    integerMassCheck 29 25 1 (dualNumerators029 25 1) := by
  apply integerChecks_of_simple 29 25 1 (dualNumerators029 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 0, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals029 25 1) 8671199
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck029_26_0 :
    integerResidualCheck 29 26 0 (dualNumerators029 26 0) ∧
    integerMassCheck 29 26 0 (dualNumerators029 26 0) := by
  apply integerChecks_of_simple 29 26 0 (dualNumerators029 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals029 26 0) 15099566
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck029_26_1 :
    integerResidualCheck 29 26 1 (dualNumerators029 26 1) ∧
    integerMassCheck 29 26 1 (dualNumerators029 26 1) := by
  apply integerChecks_of_simple 29 26 1 (dualNumerators029 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 879744679617, 350168760452, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals029 26 1) 15099566
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck029_27_0 :
    integerResidualCheck 29 27 0 (dualNumerators029 27 0) ∧
    integerMassCheck 29 27 0 (dualNumerators029 27 0) := by
  apply integerChecks_of_simple 29 27 0 (dualNumerators029 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312724, 1, 0, 0, 0, 0, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 436855949686, 304617712691, 340673826058, 423325647580]) (branchResiduals029 27 0) 7338775
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck029_27_1 :
    integerResidualCheck 29 27 1 (dualNumerators029 27 1) ∧
    integerMassCheck 29 27 1 (dualNumerators029 27 1) := by
  apply integerChecks_of_simple 29 27 1 (dualNumerators029 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 234337221023, 181967583262, 0, 1170399780726, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 953483284011, 578454657198, 377837583379, 0, 493953251519, 799807060596, 430830286610, 214386579479, 236224837801, 293536000677]) (branchResiduals029 27 1) 7338775
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck029_28_0 :
    integerResidualCheck 29 28 0 (dualNumerators029 28 0) ∧
    integerMassCheck 29 28 0 (dualNumerators029 28 0) := by
  apply integerChecks_of_simple 29 28 0 (dualNumerators029 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 1, 0, 0, 0, 0, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 374399059503, 471423145846, 287707656866, 357509209222]) (branchResiduals029 28 0) 10335557
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck029_28_1 :
    integerResidualCheck 29 28 1 (dualNumerators029 28 1) ∧
    integerMassCheck 29 28 1 (dualNumerators029 28 1) := by
  apply integerChecks_of_simple 29 28 1 (dualNumerators029 28 1)
    (![70965414109, 13064532837, 70965414109, 0, 1, 500061019298, 592120844340, 0, 99499623476, 70965414109, 0, 7115673227, 105323995459, 617878243177, 8425648624, 0, 0, 610762569951, 1239006666393, 201847170824, 109986917328, 775027817129, 109986917328, 130235198988, 7115673227, 0, 112439668685, 610762569950, 0, 0, 11028343493, 946600440957, 438442294144, 508158146813, 0, 109986917328, 455943846399, 343484151953, 11028343493, 0, 68764047964, 85447084301]) (branchResiduals029 28 1) 10335557
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck029_29_0 :
    integerResidualCheck 29 29 0 (dualNumerators029 29 0) ∧
    integerMassCheck 29 29 0 (dualNumerators029 29 0) := by
  apply integerChecks_of_simple 29 29 0 (dualNumerators029 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals029 29 0) 40352153
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck029_29_1 :
    integerResidualCheck 29 29 1 (dualNumerators029 29 1) ∧
    integerMassCheck 29 29 1 (dualNumerators029 29 1) := by
  apply integerChecks_of_simple 29 29 1 (dualNumerators029 29 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 1766557277936, 81171398308, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals029 29 1) 40352153
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck029_30_0 :
    integerResidualCheck 29 30 0 (dualNumerators029 30 0) ∧
    integerMassCheck 29 30 0 (dualNumerators029 30 0) := by
  apply integerChecks_of_simple 29 30 0 (dualNumerators029 30 0)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 0, 5063622582, 10371186464, 88904172359, 5995821236, 0, 0, 83840549778, 170080822236, 1143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 17855961539, 112085697126, 0, 78268383123, 104918139930, 4820875175, 7847938961, 0, 108324858619, 1414156487]) (branchResiduals029 30 0) 7680628
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck029_30_1 :
    integerResidualCheck 29 30 1 (dualNumerators029 30 1) ∧
    integerMassCheck 29 30 1 (dualNumerators029 30 1) := by
  apply integerChecks_of_simple 29 30 1 (dualNumerators029 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 491724510490, 107456641334, 0, 691151837050, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 669214578381, 235435046259, 544901951702, 0, 185534744901, 578464728737, 621279733097, 307371055990, 281282522283, 482716951355]) (branchResiduals029 30 1) 7680628
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck029_31_0 :
    integerResidualCheck 29 31 0 (dualNumerators029 31 0) ∧
    integerMassCheck 29 31 0 (dualNumerators029 31 0) := by
  apply integerChecks_of_simple 29 31 0 (dualNumerators029 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 940234337176, 92181304950, 0, 592902192609, 1222480453651, 0, 0, 500720887661, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642124, 1, 92181304949, 500720887660, 0, 0, 1600106408231, 776050524992, 77849441973, 698201083019, 711927549445, 860915026216, 655394283556, 0, 905514817789, 694591590443, 655394283556, 0]) (branchResiduals029 31 0) 32891612
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck029_31_1 :
    integerResidualCheck 29 31 1 (dualNumerators029 31 1) ∧
    integerMassCheck 29 31 1 (dualNumerators029 31 1) := by
  apply integerChecks_of_simple 29 31 1 (dualNumerators029 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 274671058114, 217988955956, 0, 1402086139076, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 741061026801, 808805463926, 18993131489, 744564115640, 327950144489, 1221916346239]) (branchResiduals029 31 1) 32891612
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck029_32_0 :
    integerResidualCheck 29 32 0 (dualNumerators029 32 0) ∧
    integerMassCheck 29 32 0 (dualNumerators029 32 0) := by
  apply integerChecks_of_simple 29 32 0 (dualNumerators029 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 1713354977902, 1030113130681, 2028778803022, 0, 505064750776, 2743468108580, 0, 1713354977903, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 315423825121, 1713354977902, 0, 0, 4252009289869, 2655471466972, 364902194330, 2290569272643, 0, 1599482877825, 2144093971220, 98518801469, 262156886566, 3989852403304, 0, 2242612772688]) (branchResiduals029 32 0) 67647473
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck029_32_1 :
    integerResidualCheck 29 32 1 (dualNumerators029 32 1) ∧
    integerMassCheck 29 32 1 (dualNumerators029 32 1) := by
  apply integerChecks_of_simple 29 32 1 (dualNumerators029 32 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 1766557277936, 81171398308, 132139529898, 0, 1823917842058, 23810834186]) (branchResiduals029 32 1) 67647473
    branchSparseDots029 branchIntegerCurvature029 branchDots029
    branchIntegerCurvature029_entry rfl
    (congrFun (congrFun branchResiduals029_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks029 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 29 j s (dualNumerators029 j s) ∧
    integerMassCheck 29 j s (dualNumerators029 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck029_0_0
    · exact integerCheck029_0_1
  · fin_cases s
    · exact integerCheck029_1_0
    · exact integerCheck029_1_1
  · fin_cases s
    · exact integerCheck029_2_0
    · exact integerCheck029_2_1
  · fin_cases s
    · exact integerCheck029_3_0
    · exact integerCheck029_3_1
  · fin_cases s
    · exact integerCheck029_4_0
    · exact integerCheck029_4_1
  · fin_cases s
    · exact integerCheck029_5_0
    · exact integerCheck029_5_1
  · fin_cases s
    · exact integerCheck029_6_0
    · exact integerCheck029_6_1
  · fin_cases s
    · exact integerCheck029_7_0
    · exact integerCheck029_7_1
  · fin_cases s
    · exact integerCheck029_8_0
    · exact integerCheck029_8_1
  · fin_cases s
    · exact integerCheck029_9_0
    · exact integerCheck029_9_1
  · fin_cases s
    · exact integerCheck029_10_0
    · exact integerCheck029_10_1
  · fin_cases s
    · exact integerCheck029_11_0
    · exact integerCheck029_11_1
  · fin_cases s
    · exact integerCheck029_12_0
    · exact integerCheck029_12_1
  · fin_cases s
    · exact integerCheck029_13_0
    · exact integerCheck029_13_1
  · fin_cases s
    · exact integerCheck029_14_0
    · exact integerCheck029_14_1
  · fin_cases s
    · exact integerCheck029_15_0
    · exact integerCheck029_15_1
  · fin_cases s
    · exact integerCheck029_16_0
    · exact integerCheck029_16_1
  · fin_cases s
    · exact integerCheck029_17_0
    · exact integerCheck029_17_1
  · fin_cases s
    · exact integerCheck029_18_0
    · exact integerCheck029_18_1
  · fin_cases s
    · exact integerCheck029_19_0
    · exact integerCheck029_19_1
  · fin_cases s
    · exact integerCheck029_20_0
    · exact integerCheck029_20_1
  · fin_cases s
    · exact integerCheck029_21_0
    · exact integerCheck029_21_1
  · fin_cases s
    · exact integerCheck029_22_0
    · exact integerCheck029_22_1
  · fin_cases s
    · exact integerCheck029_23_0
    · exact integerCheck029_23_1
  · fin_cases s
    · exact integerCheck029_24_0
    · exact integerCheck029_24_1
  · fin_cases s
    · exact integerCheck029_25_0
    · exact integerCheck029_25_1
  · fin_cases s
    · exact integerCheck029_26_0
    · exact integerCheck029_26_1
  · fin_cases s
    · exact integerCheck029_27_0
    · exact integerCheck029_27_1
  · fin_cases s
    · exact integerCheck029_28_0
    · exact integerCheck029_28_1
  · fin_cases s
    · exact integerCheck029_29_0
    · exact integerCheck029_29_1
  · fin_cases s
    · exact integerCheck029_30_0
    · exact integerCheck029_30_1
  · fin_cases s
    · exact integerCheck029_31_0
    · exact integerCheck029_31_1
  · fin_cases s
    · exact integerCheck029_32_0
    · exact integerCheck029_32_1

end ElevenSquare.Tasks.T06
