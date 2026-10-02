import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual125
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
import ElevenSquare.Tasks.T06.SparseColumn33
import ElevenSquare.Tasks.T06.SparseColumn34
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn51
import ElevenSquare.Tasks.T06.SparseColumn54
import ElevenSquare.Tasks.T06.SparseColumn57
import ElevenSquare.Tasks.T06.SparseColumn58

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix125 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral28, roundedGradientLiteral42, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix125_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = branchIntegerMatrix125 := by
  change roundedGradients ∘ branchRows 125 = branchIntegerMatrix125
  rw [show branchRows 125 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 54, 55, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral28_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral42_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix125]

theorem branchColumn125_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 0) i) = _
  rw [branchColumn125_0]
  exact sparseColumn00_sum n

theorem branchColumn125_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 1) i) = _
  rw [branchColumn125_1]
  exact sparseColumn01_sum n

theorem branchColumn125_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 2) i) = _
  rw [branchColumn125_2]
  exact sparseColumn02_sum n

theorem branchColumn125_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 3) i) = _
  rw [branchColumn125_3]
  exact sparseColumn03_sum n

theorem branchColumn125_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 4) i) = _
  rw [branchColumn125_4]
  exact sparseColumn04_sum n

theorem branchColumn125_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 5) i) = _
  rw [branchColumn125_5]
  exact sparseColumn05_sum n

theorem branchColumn125_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 6) i) = _
  rw [branchColumn125_6]
  exact sparseColumn06_sum n

theorem branchColumn125_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 7) i) = _
  rw [branchColumn125_7]
  exact sparseColumn07_sum n

theorem branchColumn125_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 8) i) = _
  rw [branchColumn125_8]
  exact sparseColumn08_sum n

theorem branchColumn125_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 9) i) = _
  rw [branchColumn125_9]
  exact sparseColumn09_sum n

theorem branchColumn125_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 10) i) = _
  rw [branchColumn125_10]
  exact sparseColumn10_sum n

theorem branchColumn125_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 11) i) = _
  rw [branchColumn125_11]
  exact sparseColumn11_sum n

theorem branchColumn125_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 12) = sparseColumn12 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 12) = sparseDot12 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 12) i) = _
  rw [branchColumn125_12]
  exact sparseColumn12_sum n

theorem branchColumn125_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 13) = sparseColumn13 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 13) = sparseDot13 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 13) i) = _
  rw [branchColumn125_13]
  exact sparseColumn13_sum n

theorem branchColumn125_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 14) = sparseColumn33 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 14) = sparseDot33 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 14) i) = _
  rw [branchColumn125_14]
  exact sparseColumn33_sum n

theorem branchColumn125_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 15) = sparseColumn15 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 15) = sparseDot15 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 15) i) = _
  rw [branchColumn125_15]
  exact sparseColumn15_sum n

theorem branchColumn125_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 16) = sparseColumn16 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 16) = sparseDot16 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 16) i) = _
  rw [branchColumn125_16]
  exact sparseColumn16_sum n

theorem branchColumn125_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 17) = sparseColumn34 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 17) = sparseDot34 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 17) i) = _
  rw [branchColumn125_17]
  exact sparseColumn34_sum n

theorem branchColumn125_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 18) i) = _
  rw [branchColumn125_18]
  exact sparseColumn18_sum n

theorem branchColumn125_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 19) i) = _
  rw [branchColumn125_19]
  exact sparseColumn19_sum n

theorem branchColumn125_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 20) = sparseColumn58 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 20) = sparseDot58 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 20) i) = _
  rw [branchColumn125_20]
  exact sparseColumn58_sum n

theorem branchColumn125_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 21) i) = _
  rw [branchColumn125_21]
  exact sparseColumn21_sum n

theorem branchColumn125_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 22) i) = _
  rw [branchColumn125_22]
  exact sparseColumn22_sum n

theorem branchColumn125_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 23) = sparseColumn54 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 23) = sparseDot54 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 23) i) = _
  rw [branchColumn125_23]
  exact sparseColumn54_sum n

theorem branchColumn125_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 24) i) = _
  rw [branchColumn125_24]
  exact sparseColumn24_sum n

theorem branchColumn125_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 25) i) = _
  rw [branchColumn125_25]
  exact sparseColumn25_sum n

theorem branchColumn125_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 26) = sparseColumn57 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 26) = sparseDot57 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 26) i) = _
  rw [branchColumn125_26]
  exact sparseColumn57_sum n

theorem branchColumn125_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 27) i) = _
  rw [branchColumn125_27]
  exact sparseColumn27_sum n

theorem branchColumn125_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 28) i) = _
  rw [branchColumn125_28]
  exact sparseColumn28_sum n

theorem branchColumn125_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 29) = sparseColumn51 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 29) = sparseDot51 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 29) i) = _
  rw [branchColumn125_29]
  exact sparseColumn51_sum n

theorem branchColumn125_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 30) i) = _
  rw [branchColumn125_30]
  exact sparseColumn30_sum n

theorem branchColumn125_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 31) i) = _
  rw [branchColumn125_31]
  exact sparseColumn31_sum n

theorem branchColumn125_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 125 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 125 i)) = _
  rw [branchIntegerMatrix125_eq]
  simp only [branchIntegerMatrix125, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot125_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 125 i) 32) i) = _
  rw [branchColumn125_32]
  exact sparseColumn43_sum n

def branchSparseDots125 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot12, sparseDot13, sparseDot33, sparseDot15, sparseDot16, sparseDot34, sparseDot18, sparseDot19, sparseDot58, sparseDot21, sparseDot22, sparseDot54, sparseDot24, sparseDot25, sparseDot57, sparseDot27, sparseDot28, sparseDot51, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot125_0 :
    branchSparseDots125 0 = sparseDot00 := rfl

private theorem branchSparseDot125_1 :
    branchSparseDots125 1 = sparseDot01 := rfl

private theorem branchSparseDot125_2 :
    branchSparseDots125 2 = sparseDot02 := rfl

private theorem branchSparseDot125_3 :
    branchSparseDots125 3 = sparseDot03 := rfl

private theorem branchSparseDot125_4 :
    branchSparseDots125 4 = sparseDot04 := rfl

private theorem branchSparseDot125_5 :
    branchSparseDots125 5 = sparseDot05 := rfl

private theorem branchSparseDot125_6 :
    branchSparseDots125 6 = sparseDot06 := rfl

private theorem branchSparseDot125_7 :
    branchSparseDots125 7 = sparseDot07 := rfl

private theorem branchSparseDot125_8 :
    branchSparseDots125 8 = sparseDot08 := rfl

private theorem branchSparseDot125_9 :
    branchSparseDots125 9 = sparseDot09 := rfl

private theorem branchSparseDot125_10 :
    branchSparseDots125 10 = sparseDot10 := rfl

private theorem branchSparseDot125_11 :
    branchSparseDots125 11 = sparseDot11 := rfl

private theorem branchSparseDot125_12 :
    branchSparseDots125 12 = sparseDot12 := rfl

private theorem branchSparseDot125_13 :
    branchSparseDots125 13 = sparseDot13 := rfl

private theorem branchSparseDot125_14 :
    branchSparseDots125 14 = sparseDot33 := rfl

private theorem branchSparseDot125_15 :
    branchSparseDots125 15 = sparseDot15 := rfl

private theorem branchSparseDot125_16 :
    branchSparseDots125 16 = sparseDot16 := rfl

private theorem branchSparseDot125_17 :
    branchSparseDots125 17 = sparseDot34 := rfl

private theorem branchSparseDot125_18 :
    branchSparseDots125 18 = sparseDot18 := rfl

private theorem branchSparseDot125_19 :
    branchSparseDots125 19 = sparseDot19 := rfl

private theorem branchSparseDot125_20 :
    branchSparseDots125 20 = sparseDot58 := rfl

private theorem branchSparseDot125_21 :
    branchSparseDots125 21 = sparseDot21 := rfl

private theorem branchSparseDot125_22 :
    branchSparseDots125 22 = sparseDot22 := rfl

private theorem branchSparseDot125_23 :
    branchSparseDots125 23 = sparseDot54 := rfl

private theorem branchSparseDot125_24 :
    branchSparseDots125 24 = sparseDot24 := rfl

private theorem branchSparseDot125_25 :
    branchSparseDots125 25 = sparseDot25 := rfl

private theorem branchSparseDot125_26 :
    branchSparseDots125 26 = sparseDot57 := rfl

private theorem branchSparseDot125_27 :
    branchSparseDots125 27 = sparseDot27 := rfl

private theorem branchSparseDot125_28 :
    branchSparseDots125 28 = sparseDot28 := rfl

private theorem branchSparseDot125_29 :
    branchSparseDots125 29 = sparseDot51 := rfl

private theorem branchSparseDot125_30 :
    branchSparseDots125 30 = sparseDot30 := rfl

private theorem branchSparseDot125_31 :
    branchSparseDots125 31 = sparseDot31 := rfl

private theorem branchSparseDot125_32 :
    branchSparseDots125 32 = sparseDot43 := rfl

theorem branchDots125 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 125 i) k) = branchSparseDots125 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot125_0 n
      _ = _ := congrFun branchSparseDot125_0.symm n
  · calc
      _ = sparseDot01 n := branchDot125_1 n
      _ = _ := congrFun branchSparseDot125_1.symm n
  · calc
      _ = sparseDot02 n := branchDot125_2 n
      _ = _ := congrFun branchSparseDot125_2.symm n
  · calc
      _ = sparseDot03 n := branchDot125_3 n
      _ = _ := congrFun branchSparseDot125_3.symm n
  · calc
      _ = sparseDot04 n := branchDot125_4 n
      _ = _ := congrFun branchSparseDot125_4.symm n
  · calc
      _ = sparseDot05 n := branchDot125_5 n
      _ = _ := congrFun branchSparseDot125_5.symm n
  · calc
      _ = sparseDot06 n := branchDot125_6 n
      _ = _ := congrFun branchSparseDot125_6.symm n
  · calc
      _ = sparseDot07 n := branchDot125_7 n
      _ = _ := congrFun branchSparseDot125_7.symm n
  · calc
      _ = sparseDot08 n := branchDot125_8 n
      _ = _ := congrFun branchSparseDot125_8.symm n
  · calc
      _ = sparseDot09 n := branchDot125_9 n
      _ = _ := congrFun branchSparseDot125_9.symm n
  · calc
      _ = sparseDot10 n := branchDot125_10 n
      _ = _ := congrFun branchSparseDot125_10.symm n
  · calc
      _ = sparseDot11 n := branchDot125_11 n
      _ = _ := congrFun branchSparseDot125_11.symm n
  · calc
      _ = sparseDot12 n := branchDot125_12 n
      _ = _ := congrFun branchSparseDot125_12.symm n
  · calc
      _ = sparseDot13 n := branchDot125_13 n
      _ = _ := congrFun branchSparseDot125_13.symm n
  · calc
      _ = sparseDot33 n := branchDot125_14 n
      _ = _ := congrFun branchSparseDot125_14.symm n
  · calc
      _ = sparseDot15 n := branchDot125_15 n
      _ = _ := congrFun branchSparseDot125_15.symm n
  · calc
      _ = sparseDot16 n := branchDot125_16 n
      _ = _ := congrFun branchSparseDot125_16.symm n
  · calc
      _ = sparseDot34 n := branchDot125_17 n
      _ = _ := congrFun branchSparseDot125_17.symm n
  · calc
      _ = sparseDot18 n := branchDot125_18 n
      _ = _ := congrFun branchSparseDot125_18.symm n
  · calc
      _ = sparseDot19 n := branchDot125_19 n
      _ = _ := congrFun branchSparseDot125_19.symm n
  · calc
      _ = sparseDot58 n := branchDot125_20 n
      _ = _ := congrFun branchSparseDot125_20.symm n
  · calc
      _ = sparseDot21 n := branchDot125_21 n
      _ = _ := congrFun branchSparseDot125_21.symm n
  · calc
      _ = sparseDot22 n := branchDot125_22 n
      _ = _ := congrFun branchSparseDot125_22.symm n
  · calc
      _ = sparseDot54 n := branchDot125_23 n
      _ = _ := congrFun branchSparseDot125_23.symm n
  · calc
      _ = sparseDot24 n := branchDot125_24 n
      _ = _ := congrFun branchSparseDot125_24.symm n
  · calc
      _ = sparseDot25 n := branchDot125_25 n
      _ = _ := congrFun branchSparseDot125_25.symm n
  · calc
      _ = sparseDot57 n := branchDot125_26 n
      _ = _ := congrFun branchSparseDot125_26.symm n
  · calc
      _ = sparseDot27 n := branchDot125_27 n
      _ = _ := congrFun branchSparseDot125_27.symm n
  · calc
      _ = sparseDot28 n := branchDot125_28 n
      _ = _ := congrFun branchSparseDot125_28.symm n
  · calc
      _ = sparseDot51 n := branchDot125_29 n
      _ = _ := congrFun branchSparseDot125_29.symm n
  · calc
      _ = sparseDot30 n := branchDot125_30 n
      _ = _ := congrFun branchSparseDot125_30.symm n
  · calc
      _ = sparseDot31 n := branchDot125_31 n
      _ = _ := congrFun branchSparseDot125_31.symm n
  · calc
      _ = sparseDot43 n := branchDot125_32 n
      _ = _ := congrFun branchSparseDot125_32.symm n

def branchIntegerCurvature125 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101955390, 101955390, 79086693, 79086693, 106371291, 106371291, 88123140, 88123140, 289103692, 289103692]

theorem branchIntegerCurvature125_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 125 i)) = branchIntegerCurvature125 := by
  change curvatureNumerators ∘ branchRows 125 = branchIntegerCurvature125
  rw [show branchRows 125 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 42, 30, 31, 52, 53, 54, 55, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature125_entry (i : Fin 42) :
    curvatureNumerators (branchRows 125 i) = branchIntegerCurvature125 i :=
  congrFun branchIntegerCurvature125_eq i

def branchResiduals125 : Fin 33 → Fin 2 → ℕ := ![![1297715188219138, 33000000000000], ![1545366750505710, 33000000000000], ![1581776144903180, 1338379694326231], ![33000000000000, 1022818911280213], ![855608805843885, 33000000000000], ![1057559663890938, 896839296747321], ![724484936817483, 624798065222648], ![33000000000000, 763286140676350], ![1578947361653221, 1129599753799013], ![1024477093918565, 33000000000000], ![33000000000000, 777405581571520], ![486903807979506, 465633571577520], ![988318911280213, 66000000000000], ![33000000000000, 408765559786158], ![466885892463964, 579269081763534], ![924830525898199, 33000000000000], ![66000000000000, 743500538925637], ![444014198671980, 809920998672425], ![623137587159586, 270501876676365], ![630915644006336, 512540896611240], ![1473697950945612, 855007732308317], ![751789803656361, 374264383628312], ![466722213192178, 90602725914513], ![1474116175544279, 851835656632042], ![671377491101866, 230813982650278], ![509970394700380, 220935526651417], ![398970616796057, 851835656632042], ![410241015825655, 547122209812711], ![286986369167465, 300681493829892], ![398970616796057, 893613900905056], ![99144135565345, 552658979383196], ![966871795108137, 651506017335273], ![2020474656235404, 924079729933424]]

theorem branchResiduals125_eq : residualNumerators 125 = branchResiduals125 := rfl

theorem integerCheck125_0_0 :
    integerResidualCheck 125 0 0 (dualNumerators125 0 0) ∧
    integerMassCheck 125 0 0 (dualNumerators125 0 0) := by
  apply integerChecks_of_simple 125 0 0 (dualNumerators125 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1011030237961, 258120108700, 0, 1660206247774, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 666956468696, 1506089855371, 1308901425339, 0, 601145163368, 1234047382517, 1330333654477, 636679939507, 818327875519, 1016864670366]) (branchResiduals125 0 0) 18767167
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck125_0_1 :
    integerResidualCheck 125 0 1 (dualNumerators125 0 1) ∧
    integerMassCheck 125 0 1 (dualNumerators125 0 1) := by
  apply integerChecks_of_simple 125 0 1 (dualNumerators125 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals125 0 1) 18767167
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck125_1_0 :
    integerResidualCheck 125 1 0 (dualNumerators125 1 0) ∧
    integerMassCheck 125 1 0 (dualNumerators125 1 0) := by
  apply integerChecks_of_simple 125 1 0 (dualNumerators125 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1197158056821, 305639293618, 0, 1965845541389, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 789741275848, 1783356755272, 1549866490727, 0, 711814294591, 1461232029476, 1575244332878, 753890922920, 968979732271, 1204066591796]) (branchResiduals125 1 0) 22176635
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck125_1_1 :
    integerResidualCheck 125 1 1 (dualNumerators125 1 1) ∧
    integerMassCheck 125 1 1 (dualNumerators125 1 1) := by
  apply integerChecks_of_simple 125 1 1 (dualNumerators125 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals125 1 1) 22176635
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck125_2_0 :
    integerResidualCheck 125 2 0 (dualNumerators125 2 0) ∧
    integerMassCheck 125 2 0 (dualNumerators125 2 0) := by
  apply integerChecks_of_simple 125 2 0 (dualNumerators125 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1197158056822, 305639293619, 0, 1965845541391, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 789741275848, 1783356755274, 1549866490728, 0, 711814294592, 1461232029477, 1575244332879, 753890922921, 968979732272, 1204066591797]) (branchResiduals125 2 0) 22681452
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck125_2_1 :
    integerResidualCheck 125 2 1 (dualNumerators125 2 1) ∧
    integerMassCheck 125 2 1 (dualNumerators125 2 1) := by
  apply integerChecks_of_simple 125 2 1 (dualNumerators125 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1011030237961, 258120108700, 0, 1660206247773, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 666956468696, 1506089855370, 1308901425338, 0, 601145163368, 1234047382516, 1330333654476, 636679939507, 818327875518, 1016864670365]) (branchResiduals125 2 1) 22681452
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck125_3_0 :
    integerResidualCheck 125 3 0 (dualNumerators125 3 0) ∧
    integerMassCheck 125 3 0 (dualNumerators125 3 0) := by
  apply integerChecks_of_simple 125 3 0 (dualNumerators125 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals125 3 0) 16360330
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck125_3_1 :
    integerResidualCheck 125 3 1 (dualNumerators125 3 1) ∧
    integerMassCheck 125 3 1 (dualNumerators125 3 1) := by
  apply integerChecks_of_simple 125 3 1 (dualNumerators125 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 796619754801, 203380245200, 0, 1308124173107, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 525514152402, 1186691442298, 1031321016287, 0, 473659535255, 972341366619, 1048208085022, 501658405706, 644784030255, 801216871619]) (branchResiduals125 3 1) 16360330
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck125_4_0 :
    integerResidualCheck 125 4 0 (dualNumerators125 4 0) ∧
    integerMassCheck 125 4 0 (dualNumerators125 4 0) := by
  apply integerChecks_of_simple 125 4 0 (dualNumerators125 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 672765518030, 171759757645, 0, 1104743927909, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 443809984428, 1002190917446, 870976665588, 0, 400017449587, 821166860693, 885238221966, 423663203373, 544536410901, 676647899379]) (branchResiduals125 4 0) 13760362
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck125_4_1 :
    integerResidualCheck 125 4 1 (dualNumerators125 4 1) ∧
    integerMassCheck 125 4 1 (dualNumerators125 4 1) := by
  apply integerChecks_of_simple 125 4 1 (dualNumerators125 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals125 4 1) 13760362
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck125_5_0 :
    integerResidualCheck 125 5 0 (dualNumerators125 5 0) ∧
    integerMassCheck 125 5 0 (dualNumerators125 5 0) := by
  apply integerChecks_of_simple 125 5 0 (dualNumerators125 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 796619754801, 203380245201, 0, 1308124173108, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 525514152403, 1186691442299, 1031321016288, 0, 473659535256, 972341366620, 1048208085022, 501658405707, 644784030255, 801216871620]) (branchResiduals125 5 0) 17641130
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck125_5_1 :
    integerResidualCheck 125 5 1 (dualNumerators125 5 1) ∧
    integerMassCheck 125 5 1 (dualNumerators125 5 1) := by
  apply integerChecks_of_simple 125 5 1 (dualNumerators125 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 443809984428, 1002190917446, 870976665588, 0, 400017449587, 821166860692, 885238221966, 423663203373, 544536410901, 676647899378]) (branchResiduals125 5 1) 17641130
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck125_6_0 :
    integerResidualCheck 125 6 0 (dualNumerators125 6 0) ∧
    integerMassCheck 125 6 0 (dualNumerators125 6 0) := by
  apply integerChecks_of_simple 125 6 0 (dualNumerators125 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 0, 70552396879, 187567711821, 1472638535954, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 1, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 877488274356, 957704271528, 2719950702, 106626845062, 818327875519, 1016864670366]) (branchResiduals125 6 0) 8962451
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck125_6_1 :
    integerResidualCheck 125 6 1 (dualNumerators125 6 1) ∧
    integerMassCheck 125 6 1 (dualNumerators125 6 1) := by
  apply integerChecks_of_simple 125 6 1 (dualNumerators125 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949782, 1, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals125 6 1) 8962451
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck125_7_0 :
    integerResidualCheck 125 7 0 (dualNumerators125 7 0) ∧
    integerMassCheck 125 7 0 (dualNumerators125 7 0) := by
  apply integerChecks_of_simple 125 7 0 (dualNumerators125 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals125 7 0) 10424794
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck125_7_1 :
    integerResidualCheck 125 7 1 (dualNumerators125 7 1) ∧
    integerMassCheck 125 7 1 (dualNumerators125 7 1) := by
  apply integerChecks_of_simple 125 7 1 (dualNumerators125 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 598579028412, 152819646809, 0, 982922770697, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 394870637925, 891678377638, 774933245365, 0, 355907147296, 730616014740, 787622166441, 376945461461, 484489866137, 602033295899]) (branchResiduals125 7 1) 10424794
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck125_8_0 :
    integerResidualCheck 125 8 0 (dualNumerators125 8 0) ∧
    integerMassCheck 125 8 0 (dualNumerators125 8 0) := by
  apply integerChecks_of_simple 125 8 0 (dualNumerators125 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1197158056824, 305639293618, 0, 1965845541393, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 789741275849, 1783356755275, 1549866490730, 0, 711814294592, 1461232029479, 1575244332881, 753890922921, 968979732273, 1204066591798]) (branchResiduals125 8 0) 22681452
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck125_8_1 :
    integerResidualCheck 125 8 1 (dualNumerators125 8 1) ∧
    integerMassCheck 125 8 1 (dualNumerators125 8 1) := by
  apply integerChecks_of_simple 125 8 1 (dualNumerators125 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590429, 217988955956, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546384, 0, 217988955956, 1184097183120, 0, 0, 1661192697711, 1835192545882, 563261595587, 1271930950295, 1105400337063, 0, 507682284813, 1042184205913, 1123500396284, 537692301428, 691098574663, 858767916063]) (branchResiduals125 8 1) 22681452
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck125_9_0 :
    integerResidualCheck 125 9 0 (dualNumerators125 9 0) ∧
    integerMassCheck 125 9 0 (dualNumerators125 9 0) := by
  apply integerChecks_of_simple 125 9 0 (dualNumerators125 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 887477428322, 296619754801, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 703380245200, 296619754801, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 525514152402, 1186691442298, 1031321016287, 0, 473659535255, 972341366619, 1048208085022, 501658405706, 644784030255, 801216871619]) (branchResiduals125 9 0) 16350530
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck125_9_1 :
    integerResidualCheck 125 9 1 (dualNumerators125 9 1) ∧
    integerMassCheck 125 9 1 (dualNumerators125 9 1) := by
  apply integerChecks_of_simple 125 9 1 (dualNumerators125 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals125 9 1) 16350530
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck125_10_0 :
    integerResidualCheck 125 10 0 (dualNumerators125 10 0) ∧
    integerMassCheck 125 10 0 (dualNumerators125 10 0) := by
  apply integerChecks_of_simple 125 10 0 (dualNumerators125 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals125 10 0) 10683139
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck125_10_1 :
    integerResidualCheck 125 10 1 (dualNumerators125 10 1) ∧
    integerMassCheck 125 10 1 (dualNumerators125 10 1) := by
  apply integerChecks_of_simple 125 10 1 (dualNumerators125 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 560661867464, 344525275673, 0, 844525275674, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 419928145920, 344525275674, 155474724327, 844525275674, 0, 0, 1184800741849, 1308901425339, 401731091900, 907170333440, 788396879662, 0, 362090652396, 743309684668, 801306257136, 383494484713, 492907358117, 612492978948]) (branchResiduals125 10 1) 10683139
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck125_11_0 :
    integerResidualCheck 125 11 0 (dualNumerators125 11 0) ∧
    integerMassCheck 125 11 0 (dualNumerators125 11 0) := by
  apply integerChecks_of_simple 125 11 0 (dualNumerators125 11 0)
    (![301584229951, 55520807208, 301584229951, 0, 1, 453219981703, 536656503669, 0, 422847068578, 301584229950, 0, 453219981704, 546780018297, 0, 582744499174, 0, 0, 500692022794, 1015715082378, 857797059952, 467415292132, 702430462570, 467415292132, 553465130761, 453219981704, 0, 0, 546780018297, 0, 46087995504, 702430462570, 776005788302, 238173514537, 537832273766, 467415292132, 0, 214671965902, 440684536389, 475068849115, 227361613456, 292229006395, 363127495896]) (branchResiduals125 11 0) 15120968
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck125_11_1 :
    integerResidualCheck 125 11 1 (dualNumerators125 11 1) ∧
    integerMassCheck 125 11 1 (dualNumerators125 11 1) := by
  apply integerChecks_of_simple 125 11 1 (dualNumerators125 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 227680190921, 514136741916, 446822154676, 0, 205214061173, 421269088530, 454138515265, 217344634900, 279354134309, 347129015395]) (branchResiduals125 11 1) 15120968
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck125_12_0 :
    integerResidualCheck 125 12 0 (dualNumerators125 12 0) ∧
    integerMassCheck 125 12 0 (dualNumerators125 12 0) := by
  apply integerChecks_of_simple 125 12 0 (dualNumerators125 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 525514152402, 1186691442298, 1031321016287, 0, 473659535255, 972341366619, 1048208085022, 501658405706, 644784030255, 801216871619]) (branchResiduals125 12 0) 16348076
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck125_12_1 :
    integerResidualCheck 125 12 1 (dualNumerators125 12 1) ∧
    integerMassCheck 125 12 1 (dualNumerators125 12 1) := by
  apply integerChecks_of_simple 125 12 1 (dualNumerators125 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals125 12 1) 16348076
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck125_13_0 :
    integerResidualCheck 125 13 0 (dualNumerators125 13 0) ∧
    integerMassCheck 125 13 0 (dualNumerators125 13 0) := by
  apply integerChecks_of_simple 125 13 0 (dualNumerators125 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals125 13 0) 13962901
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck125_13_1 :
    integerResidualCheck 125 13 1 (dualNumerators125 13 1) ∧
    integerMassCheck 125 13 1 (dualNumerators125 13 1) := by
  apply integerChecks_of_simple 125 13 1 (dualNumerators125 13 1)
    (![271504920046, 49983290985, 271504920046, 0, 1, 408016874475, 483131631732, 0, 380673285087, 271504920045, 408016874475, 0, 0, 16868368268, 0, 0, 450754164561, 0, 914410021623, 772242375590, 420796377646, 632371681400, 420796377646, 498263805438, 408016874475, 0, 0, 16868368268, 500000000001, 16868368269, 632371681400, 698608775208, 214418641956, 484190133253, 420796377646, 0, 193261083140, 396731685331, 427686586650, 204685094751, 263082764736, 326910003735]) (branchResiduals125 13 1) 13962901
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck125_14_0 :
    integerResidualCheck 125 14 0 (dualNumerators125 14 0) ∧
    integerMassCheck 125 14 0 (dualNumerators125 14 0) := by
  apply integerChecks_of_simple 125 14 0 (dualNumerators125 14 0)
    (![288297190339, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 0, 433252253780, 0, 0, 1079760519503, 0, 478632796615, 1, 970965240730, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253780, 0, 0, 566747746222, 0, 671483150164, 741816932837, 227680190921, 514136741916, 446822154676, 0, 205214061174, 421269088531, 454138515265, 217344634900, 279354134309, 347129015395]) (branchResiduals125 14 0) 20161291
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck125_14_1 :
    integerResidualCheck 125 14 1 (dualNumerators125 14 1) ∧
    integerMassCheck 125 14 1 (dualNumerators125 14 1) := by
  apply integerChecks_of_simple 125 14 1 (dualNumerators125 14 1)
    (![362006560060, 66644387979, 362006560061, 0, 1, 544022499300, 644175508976, 0, 507564380116, 362006560060, 544022499300, 0, 0, 355824491024, 0, 1000000000000, 601005552747, 0, 1219213362163, 1029656500786, 561061836861, 843162241867, 561061836861, 664351740584, 544022499300, 0, 0, 355824491024, 0, 355824491025, 843162241867, 931478366944, 285891522608, 645586844337, 561061836861, 0, 257681444187, 528975580441, 570248782200, 272913459667, 350777019648, 435880004980]) (branchResiduals125 14 1) 20161291
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck125_15_0 :
    integerResidualCheck 125 15 0 (dualNumerators125 15 0) ∧
    integerMassCheck 125 15 0 (dualNumerators125 15 0) := by
  apply integerChecks_of_simple 125 15 0 (dualNumerators125 15 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546385, 0, 844525275675, 602334801077, 221089960014, 684097183123, 0, 1184097183122, 1071829546385, 0, 0, 0, 2028622458796, 1713222941252, 933538524389, 1402919220983, 933538524389, 1105400337064, 905187143136, 0, 684097183123, 500000000000, 0, 0, 1402919220983, 1549866490727, 475688654291, 1074177836437, 933538524389, 0, 428750521537, 880150903803, 948824481893, 454094739091, 583650214286, 725251211053]) (branchResiduals125 15 0) 12900283
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck125_15_1 :
    integerResidualCheck 125 15 1 (dualNumerators125 15 1) ∧
    integerMassCheck 125 15 1 (dualNumerators125 15 1) := by
  apply integerChecks_of_simple 125 15 1 (dualNumerators125 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals125 15 1) 12900283
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck125_16_0 :
    integerResidualCheck 125 16 0 (dualNumerators125 16 0) ∧
    integerMassCheck 125 16 0 (dualNumerators125 16 0) := by
  apply integerChecks_of_simple 125 16 0 (dualNumerators125 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals125 16 0) 10683060
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck125_16_1 :
    integerResidualCheck 125 16 1 (dualNumerators125 16 1) ∧
    integerMassCheck 125 16 1 (dualNumerators125 16 1) := by
  apply integerChecks_of_simple 125 16 1 (dualNumerators125 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 0, 0, 0, 0, 1184800741849, 1308901425339, 401731091900, 907170333440, 788396879662, 0, 362090652396, 743309684668, 801306257136, 383494484713, 492907358117, 612492978948]) (branchResiduals125 16 1) 10683060
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck125_17_0 :
    integerResidualCheck 125 17 0 (dualNumerators125 17 0) ∧
    integerMassCheck 125 17 0 (dualNumerators125 17 0) := by
  apply integerChecks_of_simple 125 17 0 (dualNumerators125 17 0)
    (![275782051153, 50770698773, 275782051153, 0, 1, 414444535771, 490742607366, 0, 386670191328, 275782051153, 414444535771, 0, 0, 0, 1032887523019, 0, 0, 457855084348, 928815106981, 784407834273, 427425359826, 642333698256, 427425359826, 506113164564, 414444535771, 0, 0, 0, 0, 542144915654, 642333698256, 709614252839, 217796468933, 491817783906, 427425359826, 0, 196305606202, 402981566299, 434424113188, 207909585069, 267227218091, 332059954410]) (branchResiduals125 17 0) 15120968
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck125_17_1 :
    integerResidualCheck 125 17 1 (dualNumerators125 17 1) ∧
    integerMassCheck 125 17 1 (dualNumerators125 17 1) := by
  apply integerChecks_of_simple 125 17 1 (dualNumerators125 17 1)
    (![508686963928, 93647837150, 508686963928, 0, 1, 764453421592, 905187143136, 0, 713222941253, 508686963927, 764453421593, 0, 0, 1000000000000, 905187143136, 0, 844525275674, 0, 1713222941251, 1446860076751, 788396879661, 1184800741848, 788396879661, 933538524388, 764453421592, 1, 0, 1000000000000, 0, 0, 1184800741848, 1308901425338, 401731091899, 907170333439, 788396879661, 0, 362090652396, 743309684668, 801306257136, 383494484713, 492907358117, 612492978947]) (branchResiduals125 17 1) 15120968
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck125_18_0 :
    integerResidualCheck 125 18 0 (dualNumerators125 18 0) ∧
    integerMassCheck 125 18 0 (dualNumerators125 18 0) := by
  apply integerChecks_of_simple 125 18 0 (dualNumerators125 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 562515489548, 74022925577, 0, 476109064652, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 301875224851, 966521474577, 763999473637, 0, 263461482107, 807731590141, 772489965679, 214059593984, 477654049462, 593539022787]) (branchResiduals125 18 0) 13565580
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck125_18_1 :
    integerResidualCheck 125 18 1 (dualNumerators125 18 1) ∧
    integerMassCheck 125 18 1 (dualNumerators125 18 1) := by
  apply integerChecks_of_simple 125 18 1 (dualNumerators125 18 1)
    (![552774353318, 101764201348, 552774353318, 0, 1, 194169418432, 229915461414, 0, 83885421775, 59829007246, 99242781131, 94926637302, 0, 610559933212, 229915461414, 0, 0, 515633295912, 201500008915, 170171850577, 856726447141, 300936675152, 92726973504, 109797748126, 194169418432, 1, 94926637302, 515633295911, 0, 0, 300936675152, 799162766836, 134673498195, 19272402554, 92726973504, 0, 130011204269, 0, 98264701746, 202671973406, 57973095424, 72038108846]) (branchResiduals125 18 1) 13565580
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck125_19_0 :
    integerResidualCheck 125 19 0 (dualNumerators125 19 0) ∧
    integerMassCheck 125 19 0 (dualNumerators125 19 0) := by
  apply integerChecks_of_simple 125 19 0 (dualNumerators125 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 216703300504, 217988955956, 0, 1402086139076, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 168672709502, 902520362746, 645216866088, 0, 136231332822, 768418291818, 648421029826, 25293932239, 403390917798, 501258706842]) (branchResiduals125 19 0) 8248658
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck125_19_1 :
    integerResidualCheck 125 19 1 (dualNumerators125 19 1) ∧
    integerMassCheck 125 19 1 (dualNumerators125 19 1) := by
  apply integerChecks_of_simple 125 19 1 (dualNumerators125 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 1, 0, 0, 0, 0, 987477735649, 0, 394588886086, 369410587551, 460183470977, 0, 371450951992, 273765914097, 475079366460, 512398369190, 287707656866, 357509209222]) (branchResiduals125 19 1) 8248658
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck125_20_0 :
    integerResidualCheck 125 20 0 (dualNumerators125 20 0) ∧
    integerMassCheck 125 20 0 (dualNumerators125 20 0) := by
  apply integerChecks_of_simple 125 20 0 (dualNumerators125 20 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476430, 1136168804325, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605064, 2, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 1540462609577, 220447348059, 1060657349048, 0, 1487132967409, 0, 1124000645334, 2318263067540, 663125166110, 824007801299]) (branchResiduals125 20 0) 35312013
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck125_20_1 :
    integerResidualCheck 125 20 1 (dualNumerators125 20 1) ∧
    integerMassCheck 125 20 1 (dualNumerators125 20 1) := by
  apply integerChecks_of_simple 125 20 1 (dualNumerators125 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748478, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals125 20 1) 35312013
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck125_21_0 :
    integerResidualCheck 125 21 0 (dualNumerators125 21 0) ∧
    integerMassCheck 125 21 0 (dualNumerators125 21 0) := by
  apply integerChecks_of_simple 125 21 0 (dualNumerators125 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 759767979803, 549133445537, 757887471419, 892563449519, 583650214286, 725251211053]) (branchResiduals125 21 0) 11182451
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck125_21_1 :
    integerResidualCheck 125 21 1 (dualNumerators125 21 1) ∧
    integerMassCheck 125 21 1 (dualNumerators125 21 1) := by
  apply integerChecks_of_simple 125 21 1 (dualNumerators125 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 917967404853, 905358228364, 3460174706, 161253783489, 102979506989, 127963650709, 0, 0, 102979506989, 127963650709]) (branchResiduals125 21 1) 11182451
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck125_22_0 :
    integerResidualCheck 125 22 0 (dualNumerators125 22 0) ∧
    integerMassCheck 125 22 0 (dualNumerators125 22 0) := by
  apply integerChecks_of_simple 125 22 0 (dualNumerators125 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 583695195717, 0, 612220343875, 0, 492945346072, 0, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 583695195717, 0, 0, 0, 801336080718, 763999473637, 608963496407, 155035977230, 85708482881, 374474988096, 645216866088, 0, 95974191249, 705361889470, 287707656866, 357509209222]) (branchResiduals125 22 0) 6465674
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck125_22_1 :
    integerResidualCheck 125 22 1 (dualNumerators125 22 1) ∧
    integerMassCheck 125 22 1 (dualNumerators125 22 1) := by
  apply integerChecks_of_simple 125 22 1 (dualNumerators125 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 108732662288, 12539033463, 1534493418, 71511669319, 45668611868, 56748400418, 0, 0, 45668611868, 56748400418]) (branchResiduals125 22 1) 6465674
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck125_23_0 :
    integerResidualCheck 125 23 0 (dualNumerators125 23 0) ∧
    integerMassCheck 125 23 0 (dualNumerators125 23 0) := by
  apply integerChecks_of_simple 125 23 0 (dualNumerators125 23 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2011841128638, 209165476428, 0, 1345334280754, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 540462609577, 1220447348059, 1060657349048, 0, 1487132967409, 0, 1124000645334, 2318263067540, 663125166110, 824007801299]) (branchResiduals125 23 0) 35297932
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck125_23_1 :
    integerResidualCheck 125 23 1 (dualNumerators125 23 1) ∧
    integerMassCheck 125 23 1 (dualNumerators125 23 1) := by
  apply integerChecks_of_simple 125 23 1 (dualNumerators125 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1830784228945, 211125748477, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals125 23 1) 35297932
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck125_24_0 :
    integerResidualCheck 125 24 0 (dualNumerators125 24 0) ∧
    integerMassCheck 125 24 0 (dualNumerators125 24 0) := by
  apply integerChecks_of_simple 125 24 0 (dualNumerators125 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 276221246109, 150663467366, 0, 969054410724, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 512185690040, 559007382209, 705016048726, 601815130180, 477654049462, 593539022787]) (branchResiduals125 24 0) 9356857
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck125_24_1 :
    integerResidualCheck 125 24 1 (dualNumerators125 24 1) ∧
    integerMassCheck 125 24 1 (dualNumerators125 24 1) := by
  apply integerChecks_of_simple 125 24 1 (dualNumerators125 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 395480180778, 20824623507, 0, 133942179966, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 690777049383, 178822020994, 66021086067, 82038644814, 0, 0, 66021086067, 82038644814]) (branchResiduals125 24 1) 9356857
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck125_25_0 :
    integerResidualCheck 125 25 0 (dualNumerators125 25 0) ∧
    integerMassCheck 125 25 0 (dualNumerators125 25 0) := by
  apply integerChecks_of_simple 125 25 0 (dualNumerators125 25 0)
    (![34966365041, 6437209308, 34966365041, 0, 1, 22997469043, 27231238312, 0, 632721051475, 451271169324, 378016613693, 137926201423, 0, 887129416173, 610926434029, 0, 0, 749203214752, 1519850467647, 1283552135172, 54193197479, 35643006641, 699410063567, 828169486116, 515942815114, 1, 137926201422, 749203214751, 0, 0, 799642480277, 1161164957288, 492609519496, 668555437793, 54193197479, 0, 457443319543, 523189836115, 0, 35643006641, 437272616834, 543360538824]) (branchResiduals125 25 0) 8671199
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck125_25_1 :
    integerResidualCheck 125 25 1 (dualNumerators125 25 1) ∧
    integerMassCheck 125 25 1 (dualNumerators125 25 1) := by
  apply integerChecks_of_simple 125 25 1 (dualNumerators125 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals125 25 1) 8671199
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck125_26_0 :
    integerResidualCheck 125 26 0 (dualNumerators125 26 0) ∧
    integerMassCheck 125 26 0 (dualNumerators125 26 0) := by
  apply integerChecks_of_simple 125 26 0 (dualNumerators125 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals125 26 0) 15099566
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck125_26_1 :
    integerResidualCheck 125 26 1 (dualNumerators125 26 1) ∧
    integerMassCheck 125 26 1 (dualNumerators125 26 1) := by
  apply integerChecks_of_simple 125 26 1 (dualNumerators125 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 1025837005087, 204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals125 26 1) 15099566
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck125_27_0 :
    integerResidualCheck 125 27 0 (dualNumerators125 27 0) ∧
    integerMassCheck 125 27 0 (dualNumerators125 27 0) := by
  apply integerChecks_of_simple 125 27 0 (dualNumerators125 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312724, 1, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 436855949686, 304617712691, 340673826058, 423325647580]) (branchResiduals125 27 0) 7338775
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck125_27_1 :
    integerResidualCheck 125 27 1 (dualNumerators125 27 1) ∧
    integerMassCheck 125 27 1 (dualNumerators125 27 1) := by
  apply integerChecks_of_simple 125 27 1 (dualNumerators125 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 234337221023, 181967583262, 0, 1170399780726, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 585228946605, 946708994604, 377837583379, 0, 538833784902, 754926527212, 385949753226, 259267112862, 236224837801, 293536000677]) (branchResiduals125 27 1) 7338775
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck125_28_0 :
    integerResidualCheck 125 28 0 (dualNumerators125 28 0) ∧
    integerMassCheck 125 28 0 (dualNumerators125 28 0) := by
  apply integerChecks_of_simple 125 28 0 (dualNumerators125 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 1, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 374399059503, 471423145846, 287707656866, 357509209222]) (branchResiduals125 28 0) 10335557
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck125_28_1 :
    integerResidualCheck 125 28 1 (dualNumerators125 28 1) ∧
    integerMassCheck 125 28 1 (dualNumerators125 28 1) := by
  apply integerChecks_of_simple 125 28 1 (dualNumerators125 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 484442151291, 449974794159, 2156352207, 100492021777, 456143077212, 332995651238, 0, 0, 64175975503, 79745886859]) (branchResiduals125 28 1) 10335557
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck125_29_0 :
    integerResidualCheck 125 29 0 (dualNumerators125 29 0) ∧
    integerMassCheck 125 29 0 (dualNumerators125 29 0) := by
  apply integerChecks_of_simple 125 29 0 (dualNumerators125 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals125 29 0) 40352153
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck125_29_1 :
    integerResidualCheck 125 29 1 (dualNumerators125 29 1) ∧
    integerMassCheck 125 29 1 (dualNumerators125 29 1) := by
  apply integerChecks_of_simple 125 29 1 (dualNumerators125 29 1)
    (![813650000253, 149790673094, 813650000253, 0, 1, 30189853607, 35747720615, 0, 1140807387415, 813650000252, 0, 30189853607, 218493557722, 1381016667527, 35747720615, 0, 0, 1350826813921, 2740317612662, 2314267487267, 1261048870572, 46790242466, 1261048870572, 1493204415423, 30189853607, 1, 248683411329, 1350826813920, 0, 0, 46790242466, 2093601213671, 1831504430445, 262096783226, 72117429420, 1188931441153, 1768099142126, 0, 46790242466, 0, 788410359408, 979688782719]) (branchResiduals125 29 1) 40352153
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck125_30_0 :
    integerResidualCheck 125 30 0 (dualNumerators125 30 0) ∧
    integerMassCheck 125 30 0 (dualNumerators125 30 0) := by
  apply integerChecks_of_simple 125 30 0 (dualNumerators125 30 0)
    (![49325597255, 9080703511, 49325597255, 0, 0, 3298611714, 3905876838, 0, 69158736213, 49325597255, 0, 3298611714, 11777228989, 85189276451, 3905876838, 0, 0, 81890664738, 166125241653, 1140296965504, 76448090321, 5112407761, 76448090321, 90521968404, 3298611714, 0, 15075840703, 81890664738, 0, 0, 5112407761, 126919597181, 108811353134, 18108244048, 6591197296, 69856893026, 104967558241, 2219249557, 5112407761, 0, 107186807798, 0]) (branchResiduals125 30 0) 7680628
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck125_30_1 :
    integerResidualCheck 125 30 1 (dualNumerators125 30 1) ∧
    integerMassCheck 125 30 1 (dualNumerators125 30 1) := by
  apply integerChecks_of_simple 125 30 1 (dualNumerators125 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 491724510490, 107456641334, 0, 691151837050, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 277657182166, 626992442474, 544901951702, 0, 250259619582, 513739854055, 556554858415, 372095930671, 281282522283, 482716951355]) (branchResiduals125 30 1) 7680628
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck125_31_0 :
    integerResidualCheck 125 31 0 (dualNumerators125 31 0) ∧
    integerMassCheck 125 31 0 (dualNumerators125 31 0) := by
  apply integerChecks_of_simple 125 31 0 (dualNumerators125 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 940234337176, 92181304950, 0, 592902192609, 1222480453651, 0, 0, 500720887661, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642124, 1, 92181304949, 500720887660, 0, 0, 1600106408231, 776050524992, 678897187053, 97153337939, 898753891846, 674088683815, 655394283556, 0, 905514817789, 694591590443, 655394283556, 0]) (branchResiduals125 31 0) 32891612
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck125_31_1 :
    integerResidualCheck 125 31 1 (dualNumerators125 31 1) ∧
    integerMassCheck 125 31 1 (dualNumerators125 31 1) := by
  apply integerChecks_of_simple 125 31 1 (dualNumerators125 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 274671058114, 217988955956, 0, 1402086139076, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 741061026801, 808805463926, 18993131489, 744564115640, 327950144489, 1221916346239]) (branchResiduals125 31 1) 32891612
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck125_32_0 :
    integerResidualCheck 125 32 0 (dualNumerators125 32 0) ∧
    integerMassCheck 125 32 0 (dualNumerators125 32 0) := by
  apply integerChecks_of_simple 125 32 0 (dualNumerators125 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 1713354977902, 1030113130681, 2028778803022, 0, 505064750776, 2743468108580, 0, 1713354977903, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 315423825121, 1713354977902, 0, 0, 4252009289869, 2655471466972, 2323034456095, 332437010877, 91471945490, 1508010932335, 2242612772688, 0, 163638085097, 4088371204772, 0, 2242612772688]) (branchResiduals125 32 0) 67647473
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck125_32_1 :
    integerResidualCheck 125 32 1 (dualNumerators125 32 1) ∧
    integerMassCheck 125 32 1 (dualNumerators125 32 1) := by
  apply integerChecks_of_simple 125 32 1 (dualNumerators125 32 1)
    (![830518849052, 152896180641, 830518849053, 0, 1, 55540314888, 65765130409, 0, 1164458966499, 830518849051, 0, 55540314888, 198298879473, 1434372896977, 65765130409, 0, 0, 1378832582090, 2797130742946, 2362247611782, 1287193334063, 86080072929, 1287193334063, 1524162000997, 55540314888, 1, 253839194360, 1378832582089, 0, 0, 86080072929, 2137006415304, 1832109184628, 304897230676, 110979164901, 1176214169163, 1767389357845, 37366574157, 86080072929, 0, 1804755932001, 0]) (branchResiduals125 32 1) 67647473
    branchSparseDots125 branchIntegerCurvature125 branchDots125
    branchIntegerCurvature125_entry rfl
    (congrFun (congrFun branchResiduals125_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks125 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 125 j s (dualNumerators125 j s) ∧
    integerMassCheck 125 j s (dualNumerators125 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck125_0_0
    · exact integerCheck125_0_1
  · fin_cases s
    · exact integerCheck125_1_0
    · exact integerCheck125_1_1
  · fin_cases s
    · exact integerCheck125_2_0
    · exact integerCheck125_2_1
  · fin_cases s
    · exact integerCheck125_3_0
    · exact integerCheck125_3_1
  · fin_cases s
    · exact integerCheck125_4_0
    · exact integerCheck125_4_1
  · fin_cases s
    · exact integerCheck125_5_0
    · exact integerCheck125_5_1
  · fin_cases s
    · exact integerCheck125_6_0
    · exact integerCheck125_6_1
  · fin_cases s
    · exact integerCheck125_7_0
    · exact integerCheck125_7_1
  · fin_cases s
    · exact integerCheck125_8_0
    · exact integerCheck125_8_1
  · fin_cases s
    · exact integerCheck125_9_0
    · exact integerCheck125_9_1
  · fin_cases s
    · exact integerCheck125_10_0
    · exact integerCheck125_10_1
  · fin_cases s
    · exact integerCheck125_11_0
    · exact integerCheck125_11_1
  · fin_cases s
    · exact integerCheck125_12_0
    · exact integerCheck125_12_1
  · fin_cases s
    · exact integerCheck125_13_0
    · exact integerCheck125_13_1
  · fin_cases s
    · exact integerCheck125_14_0
    · exact integerCheck125_14_1
  · fin_cases s
    · exact integerCheck125_15_0
    · exact integerCheck125_15_1
  · fin_cases s
    · exact integerCheck125_16_0
    · exact integerCheck125_16_1
  · fin_cases s
    · exact integerCheck125_17_0
    · exact integerCheck125_17_1
  · fin_cases s
    · exact integerCheck125_18_0
    · exact integerCheck125_18_1
  · fin_cases s
    · exact integerCheck125_19_0
    · exact integerCheck125_19_1
  · fin_cases s
    · exact integerCheck125_20_0
    · exact integerCheck125_20_1
  · fin_cases s
    · exact integerCheck125_21_0
    · exact integerCheck125_21_1
  · fin_cases s
    · exact integerCheck125_22_0
    · exact integerCheck125_22_1
  · fin_cases s
    · exact integerCheck125_23_0
    · exact integerCheck125_23_1
  · fin_cases s
    · exact integerCheck125_24_0
    · exact integerCheck125_24_1
  · fin_cases s
    · exact integerCheck125_25_0
    · exact integerCheck125_25_1
  · fin_cases s
    · exact integerCheck125_26_0
    · exact integerCheck125_26_1
  · fin_cases s
    · exact integerCheck125_27_0
    · exact integerCheck125_27_1
  · fin_cases s
    · exact integerCheck125_28_0
    · exact integerCheck125_28_1
  · fin_cases s
    · exact integerCheck125_29_0
    · exact integerCheck125_29_1
  · fin_cases s
    · exact integerCheck125_30_0
    · exact integerCheck125_30_1
  · fin_cases s
    · exact integerCheck125_31_0
    · exact integerCheck125_31_1
  · fin_cases s
    · exact integerCheck125_32_0
    · exact integerCheck125_32_1

end ElevenSquare.Tasks.T06
