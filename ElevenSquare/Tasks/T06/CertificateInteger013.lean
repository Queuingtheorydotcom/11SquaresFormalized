import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual013
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
import ElevenSquare.Tasks.T06.SparseColumn27
import ElevenSquare.Tasks.T06.SparseColumn28
import ElevenSquare.Tasks.T06.SparseColumn30
import ElevenSquare.Tasks.T06.SparseColumn31
import ElevenSquare.Tasks.T06.SparseColumn33
import ElevenSquare.Tasks.T06.SparseColumn34
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn44
import ElevenSquare.Tasks.T06.SparseColumn46

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix013 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral28, roundedGradientLiteral42, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix013_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = branchIntegerMatrix013 := by
  change roundedGradients ∘ branchRows 13 = branchIntegerMatrix013
  rw [show branchRows 13 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 32, 33, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral28_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral42_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, branchIntegerMatrix013]

theorem branchColumn013_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 0) i) = _
  rw [branchColumn013_0]
  exact sparseColumn00_sum n

theorem branchColumn013_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 1) i) = _
  rw [branchColumn013_1]
  exact sparseColumn01_sum n

theorem branchColumn013_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 2) i) = _
  rw [branchColumn013_2]
  exact sparseColumn02_sum n

theorem branchColumn013_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 3) i) = _
  rw [branchColumn013_3]
  exact sparseColumn03_sum n

theorem branchColumn013_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 4) i) = _
  rw [branchColumn013_4]
  exact sparseColumn04_sum n

theorem branchColumn013_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 5) i) = _
  rw [branchColumn013_5]
  exact sparseColumn05_sum n

theorem branchColumn013_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 6) i) = _
  rw [branchColumn013_6]
  exact sparseColumn06_sum n

theorem branchColumn013_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 7) i) = _
  rw [branchColumn013_7]
  exact sparseColumn07_sum n

theorem branchColumn013_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 8) i) = _
  rw [branchColumn013_8]
  exact sparseColumn08_sum n

theorem branchColumn013_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 9) i) = _
  rw [branchColumn013_9]
  exact sparseColumn09_sum n

theorem branchColumn013_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 10) i) = _
  rw [branchColumn013_10]
  exact sparseColumn10_sum n

theorem branchColumn013_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 11) i) = _
  rw [branchColumn013_11]
  exact sparseColumn11_sum n

theorem branchColumn013_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 12) = sparseColumn12 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 12) = sparseDot12 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 12) i) = _
  rw [branchColumn013_12]
  exact sparseColumn12_sum n

theorem branchColumn013_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 13) = sparseColumn13 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 13) = sparseDot13 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 13) i) = _
  rw [branchColumn013_13]
  exact sparseColumn13_sum n

theorem branchColumn013_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 14) = sparseColumn33 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 14) = sparseDot33 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 14) i) = _
  rw [branchColumn013_14]
  exact sparseColumn33_sum n

theorem branchColumn013_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 15) = sparseColumn15 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 15) = sparseDot15 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 15) i) = _
  rw [branchColumn013_15]
  exact sparseColumn15_sum n

theorem branchColumn013_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 16) = sparseColumn16 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 16) = sparseDot16 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 16) i) = _
  rw [branchColumn013_16]
  exact sparseColumn16_sum n

theorem branchColumn013_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 17) = sparseColumn34 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 17) = sparseDot34 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 17) i) = _
  rw [branchColumn013_17]
  exact sparseColumn34_sum n

theorem branchColumn013_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 18) i) = _
  rw [branchColumn013_18]
  exact sparseColumn18_sum n

theorem branchColumn013_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 19) i) = _
  rw [branchColumn013_19]
  exact sparseColumn19_sum n

theorem branchColumn013_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 20) = sparseColumn20 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 20) = sparseDot20 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 20) i) = _
  rw [branchColumn013_20]
  exact sparseColumn20_sum n

theorem branchColumn013_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 21) i) = _
  rw [branchColumn013_21]
  exact sparseColumn21_sum n

theorem branchColumn013_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 22) i) = _
  rw [branchColumn013_22]
  exact sparseColumn22_sum n

theorem branchColumn013_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 23) = sparseColumn23 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 23) = sparseDot23 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 23) i) = _
  rw [branchColumn013_23]
  exact sparseColumn23_sum n

theorem branchColumn013_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 24) i) = _
  rw [branchColumn013_24]
  exact sparseColumn24_sum n

theorem branchColumn013_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 25) i) = _
  rw [branchColumn013_25]
  exact sparseColumn25_sum n

theorem branchColumn013_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 26) = sparseColumn44 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 26) = sparseDot44 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 26) i) = _
  rw [branchColumn013_26]
  exact sparseColumn44_sum n

theorem branchColumn013_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 27) i) = _
  rw [branchColumn013_27]
  exact sparseColumn27_sum n

theorem branchColumn013_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 28) i) = _
  rw [branchColumn013_28]
  exact sparseColumn28_sum n

theorem branchColumn013_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 29) = sparseColumn46 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 29) = sparseDot46 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 29) i) = _
  rw [branchColumn013_29]
  exact sparseColumn46_sum n

theorem branchColumn013_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 30) i) = _
  rw [branchColumn013_30]
  exact sparseColumn30_sum n

theorem branchColumn013_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 31) i) = _
  rw [branchColumn013_31]
  exact sparseColumn31_sum n

theorem branchColumn013_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 13 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 13 i)) = _
  rw [branchIntegerMatrix013_eq]
  simp only [branchIntegerMatrix013, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot013_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 13 i) 32) i) = _
  rw [branchColumn013_32]
  exact sparseColumn43_sum n

def branchSparseDots013 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot12, sparseDot13, sparseDot33, sparseDot15, sparseDot16, sparseDot34, sparseDot18, sparseDot19, sparseDot20, sparseDot21, sparseDot22, sparseDot23, sparseDot24, sparseDot25, sparseDot44, sparseDot27, sparseDot28, sparseDot46, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot013_0 :
    branchSparseDots013 0 = sparseDot00 := rfl

private theorem branchSparseDot013_1 :
    branchSparseDots013 1 = sparseDot01 := rfl

private theorem branchSparseDot013_2 :
    branchSparseDots013 2 = sparseDot02 := rfl

private theorem branchSparseDot013_3 :
    branchSparseDots013 3 = sparseDot03 := rfl

private theorem branchSparseDot013_4 :
    branchSparseDots013 4 = sparseDot04 := rfl

private theorem branchSparseDot013_5 :
    branchSparseDots013 5 = sparseDot05 := rfl

private theorem branchSparseDot013_6 :
    branchSparseDots013 6 = sparseDot06 := rfl

private theorem branchSparseDot013_7 :
    branchSparseDots013 7 = sparseDot07 := rfl

private theorem branchSparseDot013_8 :
    branchSparseDots013 8 = sparseDot08 := rfl

private theorem branchSparseDot013_9 :
    branchSparseDots013 9 = sparseDot09 := rfl

private theorem branchSparseDot013_10 :
    branchSparseDots013 10 = sparseDot10 := rfl

private theorem branchSparseDot013_11 :
    branchSparseDots013 11 = sparseDot11 := rfl

private theorem branchSparseDot013_12 :
    branchSparseDots013 12 = sparseDot12 := rfl

private theorem branchSparseDot013_13 :
    branchSparseDots013 13 = sparseDot13 := rfl

private theorem branchSparseDot013_14 :
    branchSparseDots013 14 = sparseDot33 := rfl

private theorem branchSparseDot013_15 :
    branchSparseDots013 15 = sparseDot15 := rfl

private theorem branchSparseDot013_16 :
    branchSparseDots013 16 = sparseDot16 := rfl

private theorem branchSparseDot013_17 :
    branchSparseDots013 17 = sparseDot34 := rfl

private theorem branchSparseDot013_18 :
    branchSparseDots013 18 = sparseDot18 := rfl

private theorem branchSparseDot013_19 :
    branchSparseDots013 19 = sparseDot19 := rfl

private theorem branchSparseDot013_20 :
    branchSparseDots013 20 = sparseDot20 := rfl

private theorem branchSparseDot013_21 :
    branchSparseDots013 21 = sparseDot21 := rfl

private theorem branchSparseDot013_22 :
    branchSparseDots013 22 = sparseDot22 := rfl

private theorem branchSparseDot013_23 :
    branchSparseDots013 23 = sparseDot23 := rfl

private theorem branchSparseDot013_24 :
    branchSparseDots013 24 = sparseDot24 := rfl

private theorem branchSparseDot013_25 :
    branchSparseDots013 25 = sparseDot25 := rfl

private theorem branchSparseDot013_26 :
    branchSparseDots013 26 = sparseDot44 := rfl

private theorem branchSparseDot013_27 :
    branchSparseDots013 27 = sparseDot27 := rfl

private theorem branchSparseDot013_28 :
    branchSparseDots013 28 = sparseDot28 := rfl

private theorem branchSparseDot013_29 :
    branchSparseDots013 29 = sparseDot46 := rfl

private theorem branchSparseDot013_30 :
    branchSparseDots013 30 = sparseDot30 := rfl

private theorem branchSparseDot013_31 :
    branchSparseDots013 31 = sparseDot31 := rfl

private theorem branchSparseDot013_32 :
    branchSparseDots013 32 = sparseDot43 := rfl

theorem branchDots013 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 13 i) k) = branchSparseDots013 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot013_0 n
      _ = _ := congrFun branchSparseDot013_0.symm n
  · calc
      _ = sparseDot01 n := branchDot013_1 n
      _ = _ := congrFun branchSparseDot013_1.symm n
  · calc
      _ = sparseDot02 n := branchDot013_2 n
      _ = _ := congrFun branchSparseDot013_2.symm n
  · calc
      _ = sparseDot03 n := branchDot013_3 n
      _ = _ := congrFun branchSparseDot013_3.symm n
  · calc
      _ = sparseDot04 n := branchDot013_4 n
      _ = _ := congrFun branchSparseDot013_4.symm n
  · calc
      _ = sparseDot05 n := branchDot013_5 n
      _ = _ := congrFun branchSparseDot013_5.symm n
  · calc
      _ = sparseDot06 n := branchDot013_6 n
      _ = _ := congrFun branchSparseDot013_6.symm n
  · calc
      _ = sparseDot07 n := branchDot013_7 n
      _ = _ := congrFun branchSparseDot013_7.symm n
  · calc
      _ = sparseDot08 n := branchDot013_8 n
      _ = _ := congrFun branchSparseDot013_8.symm n
  · calc
      _ = sparseDot09 n := branchDot013_9 n
      _ = _ := congrFun branchSparseDot013_9.symm n
  · calc
      _ = sparseDot10 n := branchDot013_10 n
      _ = _ := congrFun branchSparseDot013_10.symm n
  · calc
      _ = sparseDot11 n := branchDot013_11 n
      _ = _ := congrFun branchSparseDot013_11.symm n
  · calc
      _ = sparseDot12 n := branchDot013_12 n
      _ = _ := congrFun branchSparseDot013_12.symm n
  · calc
      _ = sparseDot13 n := branchDot013_13 n
      _ = _ := congrFun branchSparseDot013_13.symm n
  · calc
      _ = sparseDot33 n := branchDot013_14 n
      _ = _ := congrFun branchSparseDot013_14.symm n
  · calc
      _ = sparseDot15 n := branchDot013_15 n
      _ = _ := congrFun branchSparseDot013_15.symm n
  · calc
      _ = sparseDot16 n := branchDot013_16 n
      _ = _ := congrFun branchSparseDot013_16.symm n
  · calc
      _ = sparseDot34 n := branchDot013_17 n
      _ = _ := congrFun branchSparseDot013_17.symm n
  · calc
      _ = sparseDot18 n := branchDot013_18 n
      _ = _ := congrFun branchSparseDot013_18.symm n
  · calc
      _ = sparseDot19 n := branchDot013_19 n
      _ = _ := congrFun branchSparseDot013_19.symm n
  · calc
      _ = sparseDot20 n := branchDot013_20 n
      _ = _ := congrFun branchSparseDot013_20.symm n
  · calc
      _ = sparseDot21 n := branchDot013_21 n
      _ = _ := congrFun branchSparseDot013_21.symm n
  · calc
      _ = sparseDot22 n := branchDot013_22 n
      _ = _ := congrFun branchSparseDot013_22.symm n
  · calc
      _ = sparseDot23 n := branchDot013_23 n
      _ = _ := congrFun branchSparseDot013_23.symm n
  · calc
      _ = sparseDot24 n := branchDot013_24 n
      _ = _ := congrFun branchSparseDot013_24.symm n
  · calc
      _ = sparseDot25 n := branchDot013_25 n
      _ = _ := congrFun branchSparseDot013_25.symm n
  · calc
      _ = sparseDot44 n := branchDot013_26 n
      _ = _ := congrFun branchSparseDot013_26.symm n
  · calc
      _ = sparseDot27 n := branchDot013_27 n
      _ = _ := congrFun branchSparseDot013_27.symm n
  · calc
      _ = sparseDot28 n := branchDot013_28 n
      _ = _ := congrFun branchSparseDot013_28.symm n
  · calc
      _ = sparseDot46 n := branchDot013_29 n
      _ = _ := congrFun branchSparseDot013_29.symm n
  · calc
      _ = sparseDot30 n := branchDot013_30 n
      _ = _ := congrFun branchSparseDot013_30.symm n
  · calc
      _ = sparseDot31 n := branchDot013_31 n
      _ = _ := congrFun branchSparseDot013_31.symm n
  · calc
      _ = sparseDot43 n := branchDot013_32 n
      _ = _ := congrFun branchSparseDot013_32.symm n

def branchIntegerCurvature013 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101981296, 101981296, 44932602, 44932602, 115699695, 115699695, 88123140, 88123140, 289103692, 289103692]

theorem branchIntegerCurvature013_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 13 i)) = branchIntegerCurvature013 := by
  change curvatureNumerators ∘ branchRows 13 = branchIntegerCurvature013
  rw [show branchRows 13 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 32, 33, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature013_entry (i : Fin 42) :
    curvatureNumerators (branchRows 13 i) = branchIntegerCurvature013 i :=
  congrFun branchIntegerCurvature013_eq i

def branchResiduals013 : Fin 33 → Fin 2 → ℕ := ![![1300580532618599, 33000000000000], ![1545342476798598, 33000000000000], ![1582895989501194, 1337580526090041], ![33000000000000, 1023544006888705], ![857910985088990, 33000000000000], ![1054631262734472, 892499725526973], ![723975735294233, 622122527367398], ![33000000000000, 760278655633685], ![1580880611496080, 1130499627291951], ![1025202189527057, 33000000000000], ![33000000000000, 777891858653372], ![485471532168073, 466704601686204], ![989044006888705, 66000000000000], ![33000000000000, 407740121497621], ![466060210205992, 578045837872483], ![922164502487628, 33000000000000], ![66000000000000, 743986816007489], ![446082243433086, 810700129912935], ![622817537800452, 245883132922146], ![631138895246779, 510525028120531], ![1231613937096825, 950842030981077], ![754191434898769, 388586934288278], ![468360717211398, 105616699803590], ![1234336462785768, 950842030981077], ![672912287194709, 230571553353754], ![504597306550354, 223581994926723], ![398970616796057, 852626669416348], ![408760111432613, 550960205719430], ![285791123956719, 309420661383698], ![398970616796057, 950842030981077], ![105616699803590, 554690633861837], ![967408039697935, 651518154550049], ![2026642220335100, 950842030981077]]

theorem branchResiduals013_eq : residualNumerators 13 = branchResiduals013 := rfl

theorem integerCheck013_0_0 :
    integerResidualCheck 13 0 0 (dualNumerators013 0 0) ∧
    integerMassCheck 13 0 0 (dualNumerators013 0 0) := by
  apply integerChecks_of_simple 13 0 0 (dualNumerators013 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1011030237961, 258120108700, 0, 1660206247774, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1607511062796, 565535261271, 1308901425339, 0, 227681483087, 1607511062798, 1485808378804, 481205215181, 818327875519, 1016864670366]) (branchResiduals013 0 0) 18767167
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck013_0_1 :
    integerResidualCheck 13 0 1 (dualNumerators013 0 1) ∧
    integerMassCheck 13 0 1 (dualNumerators013 0 1) := by
  apply integerChecks_of_simple 13 0 1 (dualNumerators013 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals013 0 1) 18767167
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck013_1_0 :
    integerResidualCheck 13 1 0 (dualNumerators013 1 0) ∧
    integerMassCheck 13 1 0 (dualNumerators013 1 0) := by
  apply integerChecks_of_simple 13 1 0 (dualNumerators013 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1197158056821, 305639293618, 0, 1965845541389, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 1903449321293, 669648709827, 1549866490727, 0, 269597002772, 1903449321295, 1759341515999, 569793739799, 968979732271, 1204066591796]) (branchResiduals013 1 0) 22176635
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck013_1_1 :
    integerResidualCheck 13 1 1 (dualNumerators013 1 1) ∧
    integerMassCheck 13 1 1 (dualNumerators013 1 1) := by
  apply integerChecks_of_simple 13 1 1 (dualNumerators013 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals013 1 1) 22176635
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck013_2_0 :
    integerResidualCheck 13 2 0 (dualNumerators013 2 0) ∧
    integerMassCheck 13 2 0 (dualNumerators013 2 0) := by
  apply integerChecks_of_simple 13 2 0 (dualNumerators013 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1197158056822, 305639293619, 0, 1965845541391, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 1903449321295, 669648709827, 1549866490728, 0, 269597002773, 1903449321296, 1759341516001, 569793739799, 968979732272, 1204066591797]) (branchResiduals013 2 0) 22681452
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck013_2_1 :
    integerResidualCheck 13 2 1 (dualNumerators013 2 1) ∧
    integerMassCheck 13 2 1 (dualNumerators013 2 1) := by
  apply integerChecks_of_simple 13 2 1 (dualNumerators013 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1011030237961, 258120108700, 0, 1660206247773, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1607511062795, 565535261271, 1308901425338, 0, 227681483087, 1607511062796, 1485808378803, 481205215180, 818327875518, 1016864670365]) (branchResiduals013 2 1) 22681452
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck013_3_0 :
    integerResidualCheck 13 3 0 (dualNumerators013 3 0) ∧
    integerMassCheck 13 3 0 (dualNumerators013 3 0) := by
  apply integerChecks_of_simple 13 3 0 (dualNumerators013 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals013 3 0) 16360330
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck013_3_1 :
    integerResidualCheck 13 3 1 (dualNumerators013 3 1) ∧
    integerMassCheck 13 3 1 (dualNumerators013 3 1) := by
  apply integerChecks_of_simple 13 3 1 (dualNumerators013 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 796619754801, 203380245200, 0, 1308124173107, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals013 3 1) 16360330
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck013_4_0 :
    integerResidualCheck 13 4 0 (dualNumerators013 4 0) ∧
    integerMassCheck 13 4 0 (dualNumerators013 4 0) := by
  apply integerChecks_of_simple 13 4 0 (dualNumerators013 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 672765518030, 171759757645, 0, 1104743927909, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1069679196818, 376321705057, 870976665588, 0, 151505113461, 1069679196819, 988695101419, 320206323920, 544536410901, 676647899379]) (branchResiduals013 4 0) 13760362
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck013_4_1 :
    integerResidualCheck 13 4 1 (dualNumerators013 4 1) ∧
    integerMassCheck 13 4 1 (dualNumerators013 4 1) := by
  apply integerChecks_of_simple 13 4 1 (dualNumerators013 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals013 4 1) 13760362
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck013_5_0 :
    integerResidualCheck 13 5 0 (dualNumerators013 5 0) ∧
    integerMassCheck 13 5 0 (dualNumerators013 5 0) := by
  apply integerChecks_of_simple 13 5 0 (dualNumerators013 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 796619754801, 203380245201, 0, 1308124173108, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000000, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1266604123796, 445601470905, 1031321016288, 0, 179396778078, 1266604123797, 1170711084557, 379155406172, 644784030255, 801216871620]) (branchResiduals013 5 0) 17641130
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck013_5_1 :
    integerResidualCheck 13 5 1 (dualNumerators013 5 1) ∧
    integerMassCheck 13 5 1 (dualNumerators013 5 1) := by
  apply integerChecks_of_simple 13 5 1 (dualNumerators013 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1069679196817, 376321705056, 870976665588, 0, 151505113461, 1069679196818, 988695101418, 320206323920, 544536410901, 676647899378]) (branchResiduals013 5 1) 17641130
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck013_6_0 :
    integerResidualCheck 13 6 0 (dualNumerators013 6 0) ∧
    integerMassCheck 13 6 0 (dualNumerators013 6 0) := by
  apply integerChecks_of_simple 13 6 0 (dualNumerators013 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 0, 70552396879, 187567711821, 1472638535954, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 1, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 659499318402, 1175693227483, 2719950702, 106626845062, 818327875519, 1016864670366]) (branchResiduals013 6 0) 8962451
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck013_6_1 :
    integerResidualCheck 13 6 1 (dualNumerators013 6 1) ∧
    integerMassCheck 13 6 1 (dualNumerators013 6 1) := by
  apply integerChecks_of_simple 13 6 1 (dualNumerators013 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949782, 1, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals013 6 1) 8962451
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck013_7_0 :
    integerResidualCheck 13 7 0 (dualNumerators013 7 0) ∧
    integerMassCheck 13 7 0 (dualNumerators013 7 0) := by
  apply integerChecks_of_simple 13 7 0 (dualNumerators013 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals013 7 0) 10424794
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck013_7_1 :
    integerResidualCheck 13 7 1 (dualNumerators013 7 1) ∧
    integerMassCheck 13 7 1 (dualNumerators013 7 1) := by
  apply integerChecks_of_simple 13 7 1 (dualNumerators013 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 598579028412, 152819646809, 0, 982922770697, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 951724660649, 334824354914, 774933245365, 0, 134798501387, 951724660649, 879670758001, 284896869900, 484489866137, 602033295899]) (branchResiduals013 7 1) 10424794
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck013_8_0 :
    integerResidualCheck 13 8 0 (dualNumerators013 8 0) ∧
    integerMassCheck 13 8 0 (dualNumerators013 8 0) := by
  apply integerChecks_of_simple 13 8 0 (dualNumerators013 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1197158056824, 305639293618, 0, 1965845541393, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 1903449321297, 669648709828, 1549866490730, 0, 269597002773, 1903449321298, 1759341516002, 569793739800, 968979732273, 1204066591798]) (branchResiduals013 8 0) 22681452
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck013_8_1 :
    integerResidualCheck 13 8 1 (dualNumerators013 8 1) ∧
    integerMassCheck 13 8 1 (dualNumerators013 8 1) := by
  apply integerChecks_of_simple 13 8 1 (dualNumerators013 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590429, 217988955956, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546384, 0, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1357583723455, 477608822428, 1105400337063, 0, 192282767270, 1357583723456, 1254802730706, 406389967006, 691098574663, 858767916063]) (branchResiduals013 8 1) 22681452
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck013_9_0 :
    integerResidualCheck 13 9 0 (dualNumerators013 9 0) ∧
    integerMassCheck 13 9 0 (dualNumerators013 9 0) := by
  apply integerChecks_of_simple 13 9 0 (dualNumerators013 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 887477428322, 296619754801, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 703380245200, 296619754801, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals013 9 0) 16350530
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck013_9_1 :
    integerResidualCheck 13 9 1 (dualNumerators013 9 1) ∧
    integerMassCheck 13 9 1 (dualNumerators013 9 1) := by
  apply integerChecks_of_simple 13 9 1 (dualNumerators013 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals013 9 1) 16350530
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck013_10_0 :
    integerResidualCheck 13 10 0 (dualNumerators013 10 0) ∧
    integerMassCheck 13 10 0 (dualNumerators013 10 0) := by
  apply integerChecks_of_simple 13 10 0 (dualNumerators013 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals013 10 0) 10683139
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck013_10_1 :
    integerResidualCheck 13 10 1 (dualNumerators013 10 1) ∧
    integerMassCheck 13 10 1 (dualNumerators013 10 1) := by
  apply integerChecks_of_simple 13 10 1 (dualNumerators013 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 560661867464, 344525275673, 0, 844525275674, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 419928145920, 344525275674, 155474724327, 844525275674, 0, 0, 1184800741849, 1308901425339, 968259856239, 340641569100, 788396879662, 0, 137140480825, 968259856240, 894954094286, 289846647564, 492907358117, 612492978948]) (branchResiduals013 10 1) 10683139
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck013_11_0 :
    integerResidualCheck 13 11 0 (dualNumerators013 11 0) ∧
    integerMassCheck 13 11 0 (dualNumerators013 11 0) := by
  apply integerChecks_of_simple 13 11 0 (dualNumerators013 11 0)
    (![301584229951, 55520807208, 301584229951, 0, 1, 453219981703, 536656503669, 0, 422847068578, 301584229950, 0, 453219981704, 546780018297, 0, 582744499174, 0, 0, 500692022794, 1015715082378, 857797059952, 467415292132, 702430462570, 467415292132, 553465130761, 453219981704, 0, 0, 546780018297, 0, 46087995504, 702430462570, 776005788302, 574050297812, 201955490491, 467415292132, 0, 81306204478, 574050297812, 530589656322, 171840806248, 292229006395, 363127495896]) (branchResiduals013 11 0) 15120968
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck013_11_1 :
    integerResidualCheck 13 11 1 (dualNumerators013 11 1) ∧
    integerMassCheck 13 11 1 (dualNumerators013 11 1) := by
  apply integerChecks_of_simple 13 11 1 (dualNumerators013 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 548759091280, 193057841557, 446822154676, 0, 77724058423, 548759091281, 507213215908, 164269934257, 279354134309, 347129015395]) (branchResiduals013 11 1) 15120968
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck013_12_0 :
    integerResidualCheck 13 12 0 (dualNumerators013 12 0) ∧
    integerMassCheck 13 12 0 (dualNumerators013 12 0) := by
  apply integerChecks_of_simple 13 12 0 (dualNumerators013 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals013 12 0) 16348076
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck013_12_1 :
    integerResidualCheck 13 12 1 (dualNumerators013 12 1) ∧
    integerMassCheck 13 12 1 (dualNumerators013 12 1) := by
  apply integerChecks_of_simple 13 12 1 (dualNumerators013 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals013 12 1) 16348076
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck013_13_0 :
    integerResidualCheck 13 13 0 (dualNumerators013 13 0) ∧
    integerMassCheck 13 13 0 (dualNumerators013 13 0) := by
  apply integerChecks_of_simple 13 13 0 (dualNumerators013 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals013 13 0) 13962901
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck013_13_1 :
    integerResidualCheck 13 13 1 (dualNumerators013 13 1) ∧
    integerMassCheck 13 13 1 (dualNumerators013 13 1) := by
  apply integerChecks_of_simple 13 13 1 (dualNumerators013 13 1)
    (![271504920046, 49983290985, 271504920046, 0, 1, 408016874475, 483131631732, 0, 380673285087, 271504920045, 408016874475, 0, 0, 16868368268, 0, 0, 450754164561, 0, 914410021623, 772242375590, 420796377646, 632371681400, 420796377646, 498263805438, 408016874475, 0, 0, 16868368268, 500000000001, 16868368269, 632371681400, 698608775208, 516795855788, 181812919420, 420796377646, 0, 73196912683, 516795855789, 477669877634, 154701803767, 263082764736, 326910003735]) (branchResiduals013 13 1) 13962901
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck013_14_0 :
    integerResidualCheck 13 14 0 (dualNumerators013 14 0) ∧
    integerMassCheck 13 14 0 (dualNumerators013 14 0) := by
  apply integerChecks_of_simple 13 14 0 (dualNumerators013 14 0)
    (![288297190339, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 0, 433252253780, 0, 0, 1079760519503, 0, 478632796615, 1, 970965240730, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253780, 0, 0, 566747746222, 0, 671483150164, 741816932837, 548759091280, 193057841557, 446822154676, 0, 77724058423, 548759091281, 507213215908, 164269934257, 279354134309, 347129015395]) (branchResiduals013 14 0) 20161291
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck013_14_1 :
    integerResidualCheck 13 14 1 (dualNumerators013 14 1) ∧
    integerMassCheck 13 14 1 (dualNumerators013 14 1) := by
  apply integerChecks_of_simple 13 14 1 (dualNumerators013 14 1)
    (![362006560060, 66644387979, 362006560061, 0, 1, 544022499300, 644175508976, 0, 507564380116, 362006560060, 544022499300, 0, 0, 355824491024, 0, 1000000000000, 601005552747, 0, 1219213362163, 1029656500786, 561061836861, 843162241867, 561061836861, 664351740584, 544022499300, 0, 0, 355824491024, 0, 355824491025, 843162241867, 931478366944, 689061141051, 242417225893, 561061836861, 0, 97595883576, 689061141051, 636893170178, 206269071689, 350777019648, 435880004980]) (branchResiduals013 14 1) 20161291
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck013_15_0 :
    integerResidualCheck 13 15 0 (dualNumerators013 15 0) ∧
    integerMassCheck 13 15 0 (dualNumerators013 15 0) := by
  apply integerChecks_of_simple 13 15 0 (dualNumerators013 15 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546385, 0, 844525275675, 602334801077, 221089960014, 684097183123, 0, 1184097183122, 1071829546385, 0, 0, 0, 2028622458796, 1713222941252, 933538524389, 1402919220983, 933538524389, 1105400337064, 905187143136, 0, 684097183123, 500000000000, 0, 0, 1402919220983, 1549866490727, 1146513768302, 403352722425, 933538524389, 0, 162387657036, 1146513768303, 1059712622067, 343206598917, 583650214286, 725251211053]) (branchResiduals013 15 0) 12900283
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck013_15_1 :
    integerResidualCheck 13 15 1 (dualNumerators013 15 1) ∧
    integerMassCheck 13 15 1 (dualNumerators013 15 1) := by
  apply integerChecks_of_simple 13 15 1 (dualNumerators013 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals013 15 1) 12900283
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck013_16_0 :
    integerResidualCheck 13 16 0 (dualNumerators013 16 0) ∧
    integerMassCheck 13 16 0 (dualNumerators013 16 0) := by
  apply integerChecks_of_simple 13 16 0 (dualNumerators013 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals013 16 0) 10683060
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck013_16_1 :
    integerResidualCheck 13 16 1 (dualNumerators013 16 1) ∧
    integerMassCheck 13 16 1 (dualNumerators013 16 1) := by
  apply integerChecks_of_simple 13 16 1 (dualNumerators013 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 0, 0, 0, 0, 1184800741849, 1308901425339, 968259856239, 340641569100, 788396879662, 0, 137140480825, 968259856240, 894954094286, 289846647564, 492907358117, 612492978948]) (branchResiduals013 16 1) 10683060
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck013_17_0 :
    integerResidualCheck 13 17 0 (dualNumerators013 17 0) ∧
    integerMassCheck 13 17 0 (dualNumerators013 17 0) := by
  apply integerChecks_of_simple 13 17 0 (dualNumerators013 17 0)
    (![275782051153, 50770698773, 275782051153, 0, 1, 414444535771, 490742607366, 0, 386670191328, 275782051153, 414444535771, 0, 0, 0, 1032887523019, 0, 0, 457855084348, 928815106981, 784407834273, 427425359826, 642333698256, 427425359826, 506113164564, 414444535771, 0, 0, 0, 0, 542144915654, 642333698256, 709614252839, 524937158092, 184677094748, 427425359826, 0, 74350014410, 524937158092, 485194811960, 157138886296, 267227218091, 332059954410]) (branchResiduals013 17 0) 15120968
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck013_17_1 :
    integerResidualCheck 13 17 1 (dualNumerators013 17 1) ∧
    integerMassCheck 13 17 1 (dualNumerators013 17 1) := by
  apply integerChecks_of_simple 13 17 1 (dualNumerators013 17 1)
    (![508686963928, 93647837150, 508686963928, 0, 1, 764453421592, 905187143136, 0, 713222941253, 508686963927, 764453421593, 0, 0, 1000000000000, 905187143136, 0, 844525275674, 0, 1713222941251, 1446860076751, 788396879661, 1184800741848, 788396879661, 933538524388, 764453421592, 1, 0, 1000000000000, 0, 0, 1184800741848, 1308901425338, 968259856239, 340641569100, 788396879661, 0, 137140480824, 968259856239, 894954094285, 289846647563, 492907358117, 612492978947]) (branchResiduals013 17 1) 15120968
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck013_18_0 :
    integerResidualCheck 13 18 0 (dualNumerators013 18 0) ∧
    integerMassCheck 13 18 0 (dualNumerators013 18 0) := by
  apply integerChecks_of_simple 13 18 0 (dualNumerators013 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 562515489548, 74022925577, 0, 476109064652, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 1025720546095, 242676153333, 763999473637, 0, 45472526152, 1025720546096, 863239815324, 123309744339, 477654049462, 593539022787]) (branchResiduals013 18 0) 13565580
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck013_18_1 :
    integerResidualCheck 13 18 1 (dualNumerators013 18 1) ∧
    integerMassCheck 13 18 1 (dualNumerators013 18 1) := by
  apply integerChecks_of_simple 13 18 1 (dualNumerators013 18 1)
    (![538874628613, 99205301184, 538874628613, 0, 1, 173280948973, 205181483568, 0, 64396810428, 45929282541, 82602613712, 90678335261, 0, 583235221374, 205181483568, 0, 0, 492556886114, 154686685730, 130636815909, 835183729590, 268562336295, 71184255953, 84289076957, 173280948973, 1, 90678335261, 492556886113, 0, 0, 268562336295, 763397412564, 0, 118180546476, 71184255953, 0, 99806458592, 1, 84824690714, 183737645581, 44504543900, 55301914693]) (branchResiduals013 18 1) 13565580
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck013_19_0 :
    integerResidualCheck 13 19 0 (dualNumerators013 19 0) ∧
    integerMassCheck 13 19 0 (dualNumerators013 19 0) := by
  apply integerChecks_of_simple 13 19 0 (dualNumerators013 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 216703300504, 217988955956, 0, 1402086139076, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 901168865389, 170024206859, 593870256538, 51346609551, 3480759251, 901168865389, 673714962064, 0, 403390917798, 501258706842]) (branchResiduals013 19 0) 8248658
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck013_19_1 :
    integerResidualCheck 13 19 1 (dualNumerators013 19 1) ∧
    integerMassCheck 13 19 1 (dualNumerators013 19 1) := by
  apply integerChecks_of_simple 13 19 1 (dualNumerators013 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 1, 0, 0, 0, 0, 987477735649, 0, 405068248518, 358931225119, 460183470977, 0, 240148617570, 405068248519, 529741159093, 457736576556, 287707656866, 357509209222]) (branchResiduals013 19 1) 8248658
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck013_20_0 :
    integerResidualCheck 13 20 0 (dualNumerators013 20 0) ∧
    integerMassCheck 13 20 0 (dualNumerators013 20 0) := by
  apply integerChecks_of_simple 13 20 0 (dualNumerators013 20 0)
    (![525362030296, 96717669897, 525362030297, 0, 2, 1982073878105, 2346968095805, 0, 736602820676, 525362030296, 1821502598273, 160571279835, 0, 1032780604873, 2346968095805, 0, 0, 872209325041, 1769383425548, 1494289025233, 814241006257, 3071949885822, 814241006257, 964140481890, 1982073878105, 2, 160571279833, 872209325040, 0, 0, 3071949885822, 1351808005780, 0, 1351808005780, 814241006257, 0, 1141636028738, 1, 970267099056, 2101682786767, 509065159462, 632570869278]) (branchResiduals013 20 0) 35312013
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck013_20_1 :
    integerResidualCheck 13 20 1 (dualNumerators013 20 1) ∧
    integerMassCheck 13 20 1 (dualNumerators013 20 1) := by
  apply integerChecks_of_simple 13 20 1 (dualNumerators013 20 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 1300649428514, 887240892199, 0, 1317842481106, 547079247729, 1300649428515, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals013 20 1) 35312013
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck013_21_0 :
    integerResidualCheck 13 21 0 (dualNumerators013 21 0) ∧
    integerMassCheck 13 21 0 (dualNumerators013 21 0) := by
  apply integerChecks_of_simple 13 21 0 (dualNumerators013 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 604293255477, 704608169863, 757887471419, 892563449519, 583650214286, 725251211053]) (branchResiduals013 21 0) 11182451
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck013_21_1 :
    integerResidualCheck 13 21 1 (dualNumerators013 21 1) ∧
    integerMassCheck 13 21 1 (dualNumerators013 21 1) := by
  apply integerChecks_of_simple 13 21 1 (dualNumerators013 21 1)
    (![113874129702, 20963906509, 113874129702, 0, 1, 11418112698, 13520155082, 0, 159661338854, 113874129702, 0, 11418112698, 207483478989, 1200472654287, 13520155082, 0, 0, 1189054541591, 1567617472129, 323892577801, 176489697786, 17696550257, 176489697786, 208980953998, 11418112698, 0, 218901591686, 1189054541590, 0, 0, 17696550257, 1842875789658, 878795318822, 964080470836, 0, 176489697786, 73266609994, 174187148961, 17696550257, 0, 110341723711, 137112035244]) (branchResiduals013 21 1) 11182451
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck013_22_0 :
    integerResidualCheck 13 22 0 (dualNumerators013 22 0) ∧
    integerMassCheck 13 22 0 (dualNumerators013 22 0) := by
  apply integerChecks_of_simple 13 22 0 (dualNumerators013 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 583695195717, 0, 612220343875, 0, 492945346072, 0, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 583695195717, 0, 0, 0, 801336080718, 763999473637, 104985155316, 659014318321, 0, 460183470977, 599623014547, 45593851542, 64927501002, 736408579717, 287707656866, 357509209222]) (branchResiduals013 22 0) 6465674
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck013_22_1 :
    integerResidualCheck 13 22 1 (dualNumerators013 22 1) ∧
    integerMassCheck 13 22 1 (dualNumerators013 22 1) := by
  apply integerChecks_of_simple 13 22 1 (dualNumerators013 22 1)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 0, 5063622582, 10371186464, 88904172359, 5995821236, 0, 0, 83840549778, 1170080822236, 143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 17855961539, 112085697126, 0, 78268383123, 32491749791, 77247265314, 7847938961, 0, 48933554844, 60805460262]) (branchResiduals013 22 1) 6465674
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck013_23_0 :
    integerResidualCheck 13 23 0 (dualNumerators013 23 0) ∧
    integerMassCheck 13 23 0 (dualNumerators013 23 0) := by
  apply integerChecks_of_simple 13 23 0 (dualNumerators013 23 0)
    (![525362030296, 96717669897, 525362030296, 0, 2, 1982073878105, 2346968095804, 0, 736602820676, 525362030295, 1821502598274, 160571279833, 0, 1032780604872, 2346968095804, 0, 0, 872209325040, 1769383425546, 1494289025232, 814241006256, 3071949885821, 814241006256, 964140481889, 1982073878106, 0, 160571279833, 872209325039, 0, 0, 3071949885821, 1351808005779, 1000000000000, 351808005780, 814241006256, 0, 1141636028738, 0, 970267099055, 2101682786767, 509065159462, 632570869277]) (branchResiduals013 23 0) 35297932
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck013_23_1 :
    integerResidualCheck 13 23 1 (dualNumerators013 23 1) ∧
    integerMassCheck 13 23 1 (dualNumerators013 23 1) := by
  apply integerChecks_of_simple 13 23 1 (dualNumerators013 23 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 547079247729, 1300649428515, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals013 23 1) 35297932
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck013_24_0 :
    integerResidualCheck 13 24 0 (dualNumerators013 24 0) ∧
    integerMassCheck 13 24 0 (dualNumerators013 24 0) := by
  apply integerChecks_of_simple 13 24 0 (dualNumerators013 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 276221246109, 150663467366, 0, 969054410724, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 384946583730, 686246488518, 705016048726, 601815130180, 477654049462, 593539022787]) (branchResiduals013 24 0) 9356857
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck013_24_1 :
    integerResidualCheck 13 24 1 (dualNumerators013 24 1) ∧
    integerMassCheck 13 24 1 (dualNumerators013 24 1) := by
  apply integerChecks_of_simple 13 24 1 (dualNumerators013 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 395480180778, 20824623507, 0, 133942179966, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 587483804282, 282115266095, 48434165160, 99625565721, 0, 0, 66021086067, 82038644814]) (branchResiduals013 24 1) 9356857
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck013_25_0 :
    integerResidualCheck 13 25 0 (dualNumerators013 25 0) ∧
    integerMassCheck 13 25 0 (dualNumerators013 25 0) := by
  apply integerChecks_of_simple 13 25 0 (dualNumerators013 25 0)
    (![31307490826, 5763620872, 31307490826, 0, 1, 17498922567, 20720424919, 0, 627590994654, 447612295109, 373636362947, 136807905692, 0, 879936634611, 604415620636, 0, 0, 743128728921, 1507527629264, 1273145186690, 48522430940, 27120993710, 693739297027, 821454747430, 510444268639, 1, 136807905692, 743128728920, 0, 0, 791120467347, 1151750315250, 639144727059, 512605588192, 48522430940, 0, 333537525435, 639144727060, 0, 27120993710, 433727241876, 538955010618]) (branchResiduals013 25 0) 8671199
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck013_25_1 :
    integerResidualCheck 13 25 1 (dualNumerators013 25 1) ∧
    integerMassCheck 13 25 1 (dualNumerators013 25 1) := by
  apply integerChecks_of_simple 13 25 1 (dualNumerators013 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 0, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals013 25 1) 8671199
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck013_26_0 :
    integerResidualCheck 13 26 0 (dualNumerators013 26 0) ∧
    integerMassCheck 13 26 0 (dualNumerators013 26 0) := by
  apply integerChecks_of_simple 13 26 0 (dualNumerators013 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals013 26 0) 15099566
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck013_26_1 :
    integerResidualCheck 13 26 1 (dualNumerators013 26 1) ∧
    integerMassCheck 13 26 1 (dualNumerators013 26 1) := by
  apply integerChecks_of_simple 13 26 1 (dualNumerators013 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 879744679617, 350168760452, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals013 26 1) 15099566
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck013_27_0 :
    integerResidualCheck 13 27 0 (dualNumerators013 27 0) ∧
    integerMassCheck 13 27 0 (dualNumerators013 27 0) := by
  apply integerChecks_of_simple 13 27 0 (dualNumerators013 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312724, 1, 0, 0, 0, 0, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 436855949686, 304617712691, 340673826058, 423325647580]) (branchResiduals013 27 0) 7338775
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck013_27_1 :
    integerResidualCheck 13 27 1 (dualNumerators013 27 1) ∧
    integerMassCheck 13 27 1 (dualNumerators013 27 1) := by
  apply integerChecks_of_simple 13 27 1 (dualNumerators013 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 234337221023, 181967583262, 0, 1170399780726, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 953483284011, 578454657198, 377837583379, 0, 340277028102, 953483284012, 430830286610, 214386579479, 236224837801, 293536000677]) (branchResiduals013 27 1) 7338775
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck013_28_0 :
    integerResidualCheck 13 28 0 (dualNumerators013 28 0) ∧
    integerMassCheck 13 28 0 (dualNumerators013 28 0) := by
  apply integerChecks_of_simple 13 28 0 (dualNumerators013 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 1, 0, 0, 0, 0, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 374399059503, 471423145846, 287707656866, 357509209222]) (branchResiduals013 28 0) 10335557
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck013_28_1 :
    integerResidualCheck 13 28 1 (dualNumerators013 28 1) ∧
    integerMassCheck 13 28 1 (dualNumerators013 28 1) := by
  apply integerChecks_of_simple 13 28 1 (dualNumerators013 28 1)
    (![70965414109, 13064532837, 70965414109, 0, 1, 500061019298, 592120844340, 0, 99499623476, 70965414109, 0, 7115673227, 105323995459, 617878243177, 8425648624, 0, 0, 610762569951, 1239006666393, 201847170824, 109986917328, 775027817129, 109986917328, 130235198988, 7115673227, 0, 112439668685, 610762569950, 0, 0, 11028343493, 946600440957, 438442294144, 508158146813, 0, 109986917328, 360985704208, 438442294145, 11028343493, 0, 68764047964, 85447084301]) (branchResiduals013 28 1) 10335557
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck013_29_0 :
    integerResidualCheck 13 29 0 (dualNumerators013 29 0) ∧
    integerMassCheck 13 29 0 (dualNumerators013 29 0) := by
  apply integerChecks_of_simple 13 29 0 (dualNumerators013 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals013 29 0) 40352153
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck013_29_1 :
    integerResidualCheck 13 29 1 (dualNumerators013 29 1) ∧
    integerMassCheck 13 29 1 (dualNumerators013 29 1) := by
  apply integerChecks_of_simple 13 29 1 (dualNumerators013 29 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 1547079247729, 300649428515, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals013 29 1) 40352153
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck013_30_0 :
    integerResidualCheck 13 30 0 (dualNumerators013 30 0) ∧
    integerMassCheck 13 30 0 (dualNumerators013 30 0) := by
  apply integerChecks_of_simple 13 30 0 (dualNumerators013 30 0)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 0, 5063622582, 10371186464, 88904172359, 5995821236, 0, 0, 83840549778, 170080822236, 1143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 17855961539, 112085697126, 0, 78268383123, 91883053566, 17855961539, 7847938961, 0, 108324858619, 1414156487]) (branchResiduals013 30 0) 7680628
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck013_30_1 :
    integerResidualCheck 13 30 1 (dualNumerators013 30 1) ∧
    integerMassCheck 13 30 1 (dualNumerators013 30 1) := by
  apply integerChecks_of_simple 13 30 1 (dualNumerators013 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 491724510490, 107456641334, 0, 691151837050, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 669214578381, 235435046259, 544901951702, 0, 94784895256, 669214578382, 621279733097, 307371055990, 281282522283, 482716951355]) (branchResiduals013 30 1) 7680628
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck013_31_0 :
    integerResidualCheck 13 31 0 (dualNumerators013 31 0) ∧
    integerMassCheck 13 31 0 (dualNumerators013 31 0) := by
  apply integerChecks_of_simple 13 31 0 (dualNumerators013 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 940234337176, 92181304950, 0, 592902192609, 1222480453651, 0, 0, 500720887661, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642124, 1, 92181304949, 500720887660, 0, 0, 1600106408231, 776050524992, 0, 776050524992, 634078107472, 938764468189, 655394283555, 1, 827665375816, 772441032416, 655394283556, 0]) (branchResiduals013 31 0) 32891612
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck013_31_1 :
    integerResidualCheck 13 31 1 (dualNumerators013 31 1) ∧
    integerMassCheck 13 31 1 (dualNumerators013 31 1) := by
  apply integerChecks_of_simple 13 31 1 (dualNumerators013 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 274671058114, 217988955956, 0, 1402086139076, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 556963843680, 992902647048, 18993131489, 744564115640, 327950144489, 1221916346239]) (branchResiduals013 31 1) 32891612
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck013_32_0 :
    integerResidualCheck 13 32 0 (dualNumerators013 32 0) ∧
    integerMassCheck 13 32 0 (dualNumerators013 32 0) := by
  apply integerChecks_of_simple 13 32 0 (dualNumerators013 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 1713354977902, 1030113130681, 2028778803022, 0, 505064750776, 2743468108580, 0, 1713354977903, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 315423825121, 1713354977902, 0, 0, 4252009289869, 2655471466972, 364902194330, 2290569272643, 0, 1599482877825, 1877710578357, 364902194331, 262156886566, 3989852403304, 0, 2242612772688]) (branchResiduals013 32 0) 67647473
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck013_32_1 :
    integerResidualCheck 13 32 1 (dualNumerators013 32 1) ∧
    integerMassCheck 13 32 1 (dualNumerators013 32 1) := by
  apply integerChecks_of_simple 13 32 1 (dualNumerators013 32 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 1547079247729, 300649428515, 132139529898, 0, 1823917842058, 23810834186]) (branchResiduals013 32 1) 67647473
    branchSparseDots013 branchIntegerCurvature013 branchDots013
    branchIntegerCurvature013_entry rfl
    (congrFun (congrFun branchResiduals013_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks013 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 13 j s (dualNumerators013 j s) ∧
    integerMassCheck 13 j s (dualNumerators013 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck013_0_0
    · exact integerCheck013_0_1
  · fin_cases s
    · exact integerCheck013_1_0
    · exact integerCheck013_1_1
  · fin_cases s
    · exact integerCheck013_2_0
    · exact integerCheck013_2_1
  · fin_cases s
    · exact integerCheck013_3_0
    · exact integerCheck013_3_1
  · fin_cases s
    · exact integerCheck013_4_0
    · exact integerCheck013_4_1
  · fin_cases s
    · exact integerCheck013_5_0
    · exact integerCheck013_5_1
  · fin_cases s
    · exact integerCheck013_6_0
    · exact integerCheck013_6_1
  · fin_cases s
    · exact integerCheck013_7_0
    · exact integerCheck013_7_1
  · fin_cases s
    · exact integerCheck013_8_0
    · exact integerCheck013_8_1
  · fin_cases s
    · exact integerCheck013_9_0
    · exact integerCheck013_9_1
  · fin_cases s
    · exact integerCheck013_10_0
    · exact integerCheck013_10_1
  · fin_cases s
    · exact integerCheck013_11_0
    · exact integerCheck013_11_1
  · fin_cases s
    · exact integerCheck013_12_0
    · exact integerCheck013_12_1
  · fin_cases s
    · exact integerCheck013_13_0
    · exact integerCheck013_13_1
  · fin_cases s
    · exact integerCheck013_14_0
    · exact integerCheck013_14_1
  · fin_cases s
    · exact integerCheck013_15_0
    · exact integerCheck013_15_1
  · fin_cases s
    · exact integerCheck013_16_0
    · exact integerCheck013_16_1
  · fin_cases s
    · exact integerCheck013_17_0
    · exact integerCheck013_17_1
  · fin_cases s
    · exact integerCheck013_18_0
    · exact integerCheck013_18_1
  · fin_cases s
    · exact integerCheck013_19_0
    · exact integerCheck013_19_1
  · fin_cases s
    · exact integerCheck013_20_0
    · exact integerCheck013_20_1
  · fin_cases s
    · exact integerCheck013_21_0
    · exact integerCheck013_21_1
  · fin_cases s
    · exact integerCheck013_22_0
    · exact integerCheck013_22_1
  · fin_cases s
    · exact integerCheck013_23_0
    · exact integerCheck013_23_1
  · fin_cases s
    · exact integerCheck013_24_0
    · exact integerCheck013_24_1
  · fin_cases s
    · exact integerCheck013_25_0
    · exact integerCheck013_25_1
  · fin_cases s
    · exact integerCheck013_26_0
    · exact integerCheck013_26_1
  · fin_cases s
    · exact integerCheck013_27_0
    · exact integerCheck013_27_1
  · fin_cases s
    · exact integerCheck013_28_0
    · exact integerCheck013_28_1
  · fin_cases s
    · exact integerCheck013_29_0
    · exact integerCheck013_29_1
  · fin_cases s
    · exact integerCheck013_30_0
    · exact integerCheck013_30_1
  · fin_cases s
    · exact integerCheck013_31_0
    · exact integerCheck013_31_1
  · fin_cases s
    · exact integerCheck013_32_0
    · exact integerCheck013_32_1

end ElevenSquare.Tasks.T06
