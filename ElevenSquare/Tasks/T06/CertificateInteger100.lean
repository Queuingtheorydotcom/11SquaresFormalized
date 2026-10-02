import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual100
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
import ElevenSquare.Tasks.T06.SparseColumn14
import ElevenSquare.Tasks.T06.SparseColumn15
import ElevenSquare.Tasks.T06.SparseColumn16
import ElevenSquare.Tasks.T06.SparseColumn17
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
import ElevenSquare.Tasks.T06.SparseColumn42
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn53
import ElevenSquare.Tasks.T06.SparseColumn56
import ElevenSquare.Tasks.T06.SparseColumn58

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix100 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral28, roundedGradientLiteral29, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix100_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = branchIntegerMatrix100 := by
  change roundedGradients ∘ branchRows 100 = branchIntegerMatrix100
  rw [show branchRows 100 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 54, 55, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral28_eq, roundedGradientLiteral29_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix100]

theorem branchColumn100_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 0) i) = _
  rw [branchColumn100_0]
  exact sparseColumn00_sum n

theorem branchColumn100_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 1) i) = _
  rw [branchColumn100_1]
  exact sparseColumn01_sum n

theorem branchColumn100_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 2) i) = _
  rw [branchColumn100_2]
  exact sparseColumn02_sum n

theorem branchColumn100_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 3) i) = _
  rw [branchColumn100_3]
  exact sparseColumn03_sum n

theorem branchColumn100_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 4) i) = _
  rw [branchColumn100_4]
  exact sparseColumn04_sum n

theorem branchColumn100_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 5) i) = _
  rw [branchColumn100_5]
  exact sparseColumn05_sum n

theorem branchColumn100_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 6) i) = _
  rw [branchColumn100_6]
  exact sparseColumn06_sum n

theorem branchColumn100_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 7) i) = _
  rw [branchColumn100_7]
  exact sparseColumn07_sum n

theorem branchColumn100_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 8) i) = _
  rw [branchColumn100_8]
  exact sparseColumn08_sum n

theorem branchColumn100_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 9) i) = _
  rw [branchColumn100_9]
  exact sparseColumn09_sum n

theorem branchColumn100_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 10) i) = _
  rw [branchColumn100_10]
  exact sparseColumn10_sum n

theorem branchColumn100_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 11) i) = _
  rw [branchColumn100_11]
  exact sparseColumn11_sum n

theorem branchColumn100_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 12) = sparseColumn12 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 12) = sparseDot12 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 12) i) = _
  rw [branchColumn100_12]
  exact sparseColumn12_sum n

theorem branchColumn100_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 13) = sparseColumn13 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 13) = sparseDot13 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 13) i) = _
  rw [branchColumn100_13]
  exact sparseColumn13_sum n

theorem branchColumn100_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 14) = sparseColumn14 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 14) = sparseDot14 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 14) i) = _
  rw [branchColumn100_14]
  exact sparseColumn14_sum n

theorem branchColumn100_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 15) = sparseColumn15 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 15) = sparseDot15 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 15) i) = _
  rw [branchColumn100_15]
  exact sparseColumn15_sum n

theorem branchColumn100_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 16) = sparseColumn16 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 16) = sparseDot16 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 16) i) = _
  rw [branchColumn100_16]
  exact sparseColumn16_sum n

theorem branchColumn100_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 17) i) = _
  rw [branchColumn100_17]
  exact sparseColumn17_sum n

theorem branchColumn100_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 18) i) = _
  rw [branchColumn100_18]
  exact sparseColumn18_sum n

theorem branchColumn100_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 19) i) = _
  rw [branchColumn100_19]
  exact sparseColumn19_sum n

theorem branchColumn100_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 20) = sparseColumn58 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 20) = sparseDot58 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 20) i) = _
  rw [branchColumn100_20]
  exact sparseColumn58_sum n

theorem branchColumn100_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 21) i) = _
  rw [branchColumn100_21]
  exact sparseColumn21_sum n

theorem branchColumn100_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 22) i) = _
  rw [branchColumn100_22]
  exact sparseColumn22_sum n

theorem branchColumn100_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 23) = sparseColumn53 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 23) = sparseDot53 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 23) i) = _
  rw [branchColumn100_23]
  exact sparseColumn53_sum n

theorem branchColumn100_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 24) i) = _
  rw [branchColumn100_24]
  exact sparseColumn24_sum n

theorem branchColumn100_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 25) i) = _
  rw [branchColumn100_25]
  exact sparseColumn25_sum n

theorem branchColumn100_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 26) = sparseColumn56 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 26) = sparseDot56 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 26) i) = _
  rw [branchColumn100_26]
  exact sparseColumn56_sum n

theorem branchColumn100_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 27) i) = _
  rw [branchColumn100_27]
  exact sparseColumn27_sum n

theorem branchColumn100_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 28) i) = _
  rw [branchColumn100_28]
  exact sparseColumn28_sum n

theorem branchColumn100_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 29) = sparseColumn42 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 29) = sparseDot42 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 29) i) = _
  rw [branchColumn100_29]
  exact sparseColumn42_sum n

theorem branchColumn100_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 30) i) = _
  rw [branchColumn100_30]
  exact sparseColumn30_sum n

theorem branchColumn100_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 31) i) = _
  rw [branchColumn100_31]
  exact sparseColumn31_sum n

theorem branchColumn100_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 100 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 100 i)) = _
  rw [branchIntegerMatrix100_eq]
  simp only [branchIntegerMatrix100, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot100_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 100 i) 32) i) = _
  rw [branchColumn100_32]
  exact sparseColumn43_sum n

def branchSparseDots100 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot12, sparseDot13, sparseDot14, sparseDot15, sparseDot16, sparseDot17, sparseDot18, sparseDot19, sparseDot58, sparseDot21, sparseDot22, sparseDot53, sparseDot24, sparseDot25, sparseDot56, sparseDot27, sparseDot28, sparseDot42, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot100_0 :
    branchSparseDots100 0 = sparseDot00 := rfl

private theorem branchSparseDot100_1 :
    branchSparseDots100 1 = sparseDot01 := rfl

private theorem branchSparseDot100_2 :
    branchSparseDots100 2 = sparseDot02 := rfl

private theorem branchSparseDot100_3 :
    branchSparseDots100 3 = sparseDot03 := rfl

private theorem branchSparseDot100_4 :
    branchSparseDots100 4 = sparseDot04 := rfl

private theorem branchSparseDot100_5 :
    branchSparseDots100 5 = sparseDot05 := rfl

private theorem branchSparseDot100_6 :
    branchSparseDots100 6 = sparseDot06 := rfl

private theorem branchSparseDot100_7 :
    branchSparseDots100 7 = sparseDot07 := rfl

private theorem branchSparseDot100_8 :
    branchSparseDots100 8 = sparseDot08 := rfl

private theorem branchSparseDot100_9 :
    branchSparseDots100 9 = sparseDot09 := rfl

private theorem branchSparseDot100_10 :
    branchSparseDots100 10 = sparseDot10 := rfl

private theorem branchSparseDot100_11 :
    branchSparseDots100 11 = sparseDot11 := rfl

private theorem branchSparseDot100_12 :
    branchSparseDots100 12 = sparseDot12 := rfl

private theorem branchSparseDot100_13 :
    branchSparseDots100 13 = sparseDot13 := rfl

private theorem branchSparseDot100_14 :
    branchSparseDots100 14 = sparseDot14 := rfl

private theorem branchSparseDot100_15 :
    branchSparseDots100 15 = sparseDot15 := rfl

private theorem branchSparseDot100_16 :
    branchSparseDots100 16 = sparseDot16 := rfl

private theorem branchSparseDot100_17 :
    branchSparseDots100 17 = sparseDot17 := rfl

private theorem branchSparseDot100_18 :
    branchSparseDots100 18 = sparseDot18 := rfl

private theorem branchSparseDot100_19 :
    branchSparseDots100 19 = sparseDot19 := rfl

private theorem branchSparseDot100_20 :
    branchSparseDots100 20 = sparseDot58 := rfl

private theorem branchSparseDot100_21 :
    branchSparseDots100 21 = sparseDot21 := rfl

private theorem branchSparseDot100_22 :
    branchSparseDots100 22 = sparseDot22 := rfl

private theorem branchSparseDot100_23 :
    branchSparseDots100 23 = sparseDot53 := rfl

private theorem branchSparseDot100_24 :
    branchSparseDots100 24 = sparseDot24 := rfl

private theorem branchSparseDot100_25 :
    branchSparseDots100 25 = sparseDot25 := rfl

private theorem branchSparseDot100_26 :
    branchSparseDots100 26 = sparseDot56 := rfl

private theorem branchSparseDot100_27 :
    branchSparseDots100 27 = sparseDot27 := rfl

private theorem branchSparseDot100_28 :
    branchSparseDots100 28 = sparseDot28 := rfl

private theorem branchSparseDot100_29 :
    branchSparseDots100 29 = sparseDot42 := rfl

private theorem branchSparseDot100_30 :
    branchSparseDots100 30 = sparseDot30 := rfl

private theorem branchSparseDot100_31 :
    branchSparseDots100 31 = sparseDot31 := rfl

private theorem branchSparseDot100_32 :
    branchSparseDots100 32 = sparseDot43 := rfl

theorem branchDots100 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 100 i) k) = branchSparseDots100 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot100_0 n
      _ = _ := congrFun branchSparseDot100_0.symm n
  · calc
      _ = sparseDot01 n := branchDot100_1 n
      _ = _ := congrFun branchSparseDot100_1.symm n
  · calc
      _ = sparseDot02 n := branchDot100_2 n
      _ = _ := congrFun branchSparseDot100_2.symm n
  · calc
      _ = sparseDot03 n := branchDot100_3 n
      _ = _ := congrFun branchSparseDot100_3.symm n
  · calc
      _ = sparseDot04 n := branchDot100_4 n
      _ = _ := congrFun branchSparseDot100_4.symm n
  · calc
      _ = sparseDot05 n := branchDot100_5 n
      _ = _ := congrFun branchSparseDot100_5.symm n
  · calc
      _ = sparseDot06 n := branchDot100_6 n
      _ = _ := congrFun branchSparseDot100_6.symm n
  · calc
      _ = sparseDot07 n := branchDot100_7 n
      _ = _ := congrFun branchSparseDot100_7.symm n
  · calc
      _ = sparseDot08 n := branchDot100_8 n
      _ = _ := congrFun branchSparseDot100_8.symm n
  · calc
      _ = sparseDot09 n := branchDot100_9 n
      _ = _ := congrFun branchSparseDot100_9.symm n
  · calc
      _ = sparseDot10 n := branchDot100_10 n
      _ = _ := congrFun branchSparseDot100_10.symm n
  · calc
      _ = sparseDot11 n := branchDot100_11 n
      _ = _ := congrFun branchSparseDot100_11.symm n
  · calc
      _ = sparseDot12 n := branchDot100_12 n
      _ = _ := congrFun branchSparseDot100_12.symm n
  · calc
      _ = sparseDot13 n := branchDot100_13 n
      _ = _ := congrFun branchSparseDot100_13.symm n
  · calc
      _ = sparseDot14 n := branchDot100_14 n
      _ = _ := congrFun branchSparseDot100_14.symm n
  · calc
      _ = sparseDot15 n := branchDot100_15 n
      _ = _ := congrFun branchSparseDot100_15.symm n
  · calc
      _ = sparseDot16 n := branchDot100_16 n
      _ = _ := congrFun branchSparseDot100_16.symm n
  · calc
      _ = sparseDot17 n := branchDot100_17 n
      _ = _ := congrFun branchSparseDot100_17.symm n
  · calc
      _ = sparseDot18 n := branchDot100_18 n
      _ = _ := congrFun branchSparseDot100_18.symm n
  · calc
      _ = sparseDot19 n := branchDot100_19 n
      _ = _ := congrFun branchSparseDot100_19.symm n
  · calc
      _ = sparseDot58 n := branchDot100_20 n
      _ = _ := congrFun branchSparseDot100_20.symm n
  · calc
      _ = sparseDot21 n := branchDot100_21 n
      _ = _ := congrFun branchSparseDot100_21.symm n
  · calc
      _ = sparseDot22 n := branchDot100_22 n
      _ = _ := congrFun branchSparseDot100_22.symm n
  · calc
      _ = sparseDot53 n := branchDot100_23 n
      _ = _ := congrFun branchSparseDot100_23.symm n
  · calc
      _ = sparseDot24 n := branchDot100_24 n
      _ = _ := congrFun branchSparseDot100_24.symm n
  · calc
      _ = sparseDot25 n := branchDot100_25 n
      _ = _ := congrFun branchSparseDot100_25.symm n
  · calc
      _ = sparseDot56 n := branchDot100_26 n
      _ = _ := congrFun branchSparseDot100_26.symm n
  · calc
      _ = sparseDot27 n := branchDot100_27 n
      _ = _ := congrFun branchSparseDot100_27.symm n
  · calc
      _ = sparseDot28 n := branchDot100_28 n
      _ = _ := congrFun branchSparseDot100_28.symm n
  · calc
      _ = sparseDot42 n := branchDot100_29 n
      _ = _ := congrFun branchSparseDot100_29.symm n
  · calc
      _ = sparseDot30 n := branchDot100_30 n
      _ = _ := congrFun branchSparseDot100_30.symm n
  · calc
      _ = sparseDot31 n := branchDot100_31 n
      _ = _ := congrFun branchSparseDot100_31.symm n
  · calc
      _ = sparseDot43 n := branchDot100_32 n
      _ = _ := congrFun branchSparseDot100_32.symm n

def branchIntegerCurvature100 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101955390, 101955390, 79086693, 79086693, 115699695, 115699695, 48290998, 48290998, 289103692, 289103692]

theorem branchIntegerCurvature100_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 100 i)) = branchIntegerCurvature100 := by
  change curvatureNumerators ∘ branchRows 100 = branchIntegerCurvature100
  rw [show branchRows 100 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 54, 55, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature100_entry (i : Fin 42) :
    curvatureNumerators (branchRows 100 i) = branchIntegerCurvature100 i :=
  congrFun branchIntegerCurvature100_eq i

def branchResiduals100 : Fin 33 → Fin 2 → ℕ := ![![1299974688071347, 33000000000000], ![1547568338714486, 33000000000000], ![1581546938652594, 1336280787543454], ![33000000000000, 1023162669606423], ![860834505619167, 33000000000000], ![1053929828911293, 897235670319759], ![721937899644338, 627277238175170], ![33000000000000, 759532674910487], ![1578358284965222, 1128902210052645], ![1024820852244775, 33000000000000], ![33000000000000, 777654409233734], ![510458243519219, 462667529964949], ![988662669606423, 66000000000000], ![33000000000000, 421444125592376], ![317079671020325, 897235670319759], ![925147146077577, 33000000000000], ![66000000000000, 743749366587851], ![955321131055507, 812401816661120], ![624770008705590, 258523427845872], ![631812607869006, 512941060933229], ![1317658320728709, 855179812138451], ![751705438750409, 374327679103908], ![470168679552591, 91598195142583], ![1319322606090492, 851835656632042], ![669577966760531, 230813982650278], ![507160306129505, 220935526651417], ![396300992921948, 851835656632042], ![409767323504074, 547562078551805], ![285734838804341, 300295031691792], ![396300992921948, 851835656632042], ![99835888223889, 550199886352837], ![968566935441686, 651244168333321], ![2020721170384396, 921030022434922]]

theorem branchResiduals100_eq : residualNumerators 100 = branchResiduals100 := rfl

theorem integerCheck100_0_0 :
    integerResidualCheck 100 0 0 (dualNumerators100 0 0) ∧
    integerMassCheck 100 0 0 (dualNumerators100 0 0) := by
  apply integerChecks_of_simple 100 0 0 (dualNumerators100 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1011030237961, 258120108700, 0, 1660206247774, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1975857894035, 197188430033, 0, 1308901425339, 1692057632752, 143134913133, 1896652816305, 70360777679, 818327875519, 1016864670366]) (branchResiduals100 0 0) 18767167
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck100_0_1 :
    integerResidualCheck 100 0 1 (dualNumerators100 0 1) ∧
    integerMassCheck 100 0 1 (dualNumerators100 0 1) := by
  apply integerChecks_of_simple 100 0 1 (dualNumerators100 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals100 0 1) 18767167
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck100_1_0 :
    integerResidualCheck 100 1 0 (dualNumerators100 1 0) ∧
    integerMassCheck 100 1 0 (dualNumerators100 1 0) := by
  apply integerChecks_of_simple 100 1 0 (dualNumerators100 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1197158056821, 305639293618, 0, 1965845541389, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 2339607766574, 233490264546, 0, 1549866490727, 2003560676621, 169485647447, 2245821257146, 83313998652, 968979732271, 1204066591796]) (branchResiduals100 1 0) 22176635
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck100_1_1 :
    integerResidualCheck 100 1 1 (dualNumerators100 1 1) ∧
    integerMassCheck 100 1 1 (dualNumerators100 1 1) := by
  apply integerChecks_of_simple 100 1 1 (dualNumerators100 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals100 1 1) 22176635
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck100_2_0 :
    integerResidualCheck 100 2 0 (dualNumerators100 2 0) ∧
    integerMassCheck 100 2 0 (dualNumerators100 2 0) := by
  apply integerChecks_of_simple 100 2 0 (dualNumerators100 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1197158056822, 305639293619, 0, 1965845541391, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 2339607766576, 233490264546, 0, 1549866490728, 2003560676622, 169485647447, 2245821257148, 83313998652, 968979732272, 1204066591797]) (branchResiduals100 2 0) 22681452
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck100_2_1 :
    integerResidualCheck 100 2 1 (dualNumerators100 2 1) ∧
    integerMassCheck 100 2 1 (dualNumerators100 2 1) := by
  apply integerChecks_of_simple 100 2 1 (dualNumerators100 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1011030237961, 258120108700, 0, 1660206247773, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1975857894033, 197188430032, 0, 1308901425338, 1692057632751, 143134913133, 1896652816304, 70360777679, 818327875518, 1016864670365]) (branchResiduals100 2 1) 22681452
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck100_3_0 :
    integerResidualCheck 100 3 0 (dualNumerators100 3 0) ∧
    integerMassCheck 100 3 0 (dualNumerators100 3 0) := by
  apply integerChecks_of_simple 100 3 0 (dualNumerators100 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals100 3 0) 16360330
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck100_3_1 :
    integerResidualCheck 100 3 1 (dualNumerators100 3 1) ∧
    integerMassCheck 100 3 1 (dualNumerators100 3 1) := by
  apply integerChecks_of_simple 100 3 1 (dualNumerators100 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 796619754801, 203380245200, 0, 1308124173107, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1556835168689, 155370426011, 0, 1031321016287, 1333220793899, 112780107975, 1494427213684, 55439277044, 644784030255, 801216871619]) (branchResiduals100 3 1) 16360330
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck100_4_0 :
    integerResidualCheck 100 4 0 (dualNumerators100 4 0) ∧
    integerMassCheck 100 4 0 (dualNumerators100 4 0) := by
  apply integerChecks_of_simple 100 4 0 (dualNumerators100 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 672765518030, 171759757645, 0, 1104743927909, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1314786650016, 131214251859, 0, 870976665588, 1125938658502, 95245651778, 1262081554611, 46819870729, 544536410901, 676647899379]) (branchResiduals100 4 0) 13760362
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck100_4_1 :
    integerResidualCheck 100 4 1 (dualNumerators100 4 1) ∧
    integerMassCheck 100 4 1 (dualNumerators100 4 1) := by
  apply integerChecks_of_simple 100 4 1 (dualNumerators100 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals100 4 1) 13760362
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck100_5_0 :
    integerResidualCheck 100 5 0 (dualNumerators100 5 0) ∧
    integerMassCheck 100 5 0 (dualNumerators100 5 0) := by
  apply integerChecks_of_simple 100 5 0 (dualNumerators100 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 796619754801, 203380245201, 0, 1308124173108, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1556835168690, 155370426011, 0, 1031321016288, 1333220793900, 112780107975, 1494427213685, 55439277044, 644784030255, 801216871620]) (branchResiduals100 5 0) 17641130
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck100_5_1 :
    integerResidualCheck 100 5 1 (dualNumerators100 5 1) ∧
    integerMassCheck 100 5 1 (dualNumerators100 5 1) := by
  apply integerChecks_of_simple 100 5 1 (dualNumerators100 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1314786650015, 131214251859, 0, 870976665588, 1125938658501, 95245651778, 1262081554610, 46819870729, 544536410901, 676647899378]) (branchResiduals100 5 1) 17641130
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck100_6_0 :
    integerResidualCheck 100 6 0 (dualNumerators100 6 0) ∧
    integerMassCheck 100 6 0 (dualNumerators100 6 0) := by
  apply integerChecks_of_simple 100 6 0 (dualNumerators100 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 0, 70552396879, 187567711821, 1472638535954, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 1, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 659499318402, 1175693227483, 103906894360, 5439901403, 818327875519, 1016864670366]) (branchResiduals100 6 0) 8962451
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck100_6_1 :
    integerResidualCheck 100 6 1 (dualNumerators100 6 1) ∧
    integerMassCheck 100 6 1 (dualNumerators100 6 1) := by
  apply integerChecks_of_simple 100 6 1 (dualNumerators100 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 1, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949782, 1, 0, 1, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 760187607595, 1097479190627, 0, 0]) (branchResiduals100 6 1) 8962451
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck100_7_0 :
    integerResidualCheck 100 7 0 (dualNumerators100 7 0) ∧
    integerMassCheck 100 7 0 (dualNumerators100 7 0) := by
  apply integerChecks_of_simple 100 7 0 (dualNumerators100 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals100 7 0) 10424794
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck100_7_1 :
    integerResidualCheck 100 7 1 (dualNumerators100 7 1) ∧
    integerMassCheck 100 7 1 (dualNumerators100 7 1) := by
  apply integerChecks_of_simple 100 7 1 (dualNumerators100 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 598579028412, 152819646810, 0, 982922770697, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675220, 1, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 1169803883289, 116745132273, 0, 774933245365, 1001780338312, 84742823724, 1122910628575, 41656999326, 484489866137, 602033295899]) (branchResiduals100 7 1) 10424794
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck100_8_0 :
    integerResidualCheck 100 8 0 (dualNumerators100 8 0) ∧
    integerMassCheck 100 8 0 (dualNumerators100 8 0) := by
  apply integerChecks_of_simple 100 8 0 (dualNumerators100 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1197158056823, 305639293619, 0, 1965845541393, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350440, 2, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 2339607766578, 233490264546, 0, 1549866490730, 2003560676624, 169485647447, 2245821257150, 83313998652, 968979732273, 1204066591798]) (branchResiduals100 8 0) 22681452
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck100_8_1 :
    integerResidualCheck 100 8 1 (dualNumerators100 8 1) ∧
    integerMassCheck 100 8 1 (dualNumerators100 8 1) := by
  apply integerChecks_of_simple 100 8 1 (dualNumerators100 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1668661932650, 166530613233, 0, 1105400337063, 1428985438754, 120881051972, 1601771242546, 59421455166, 691098574663, 858767916063]) (branchResiduals100 8 1) 22681452
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck100_9_0 :
    integerResidualCheck 100 9 0 (dualNumerators100 9 0) ∧
    integerMassCheck 100 9 0 (dualNumerators100 9 0) := by
  apply integerChecks_of_simple 100 9 0 (dualNumerators100 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 887477428322, 296619754801, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 703380245200, 296619754801, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1556835168689, 155370426011, 0, 1031321016287, 1333220793899, 112780107975, 1494427213684, 55439277044, 644784030255, 801216871619]) (branchResiduals100 9 0) 16350530
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck100_9_1 :
    integerResidualCheck 100 9 1 (dualNumerators100 9 1) ∧
    integerMassCheck 100 9 1 (dualNumerators100 9 1) := by
  apply integerChecks_of_simple 100 9 1 (dualNumerators100 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals100 9 1) 16350530
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck100_10_0 :
    integerResidualCheck 100 10 0 (dualNumerators100 10 0) ∧
    integerMassCheck 100 10 0 (dualNumerators100 10 0) := by
  apply integerChecks_of_simple 100 10 0 (dualNumerators100 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals100 10 0) 10683139
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck100_10_1 :
    integerResidualCheck 100 10 1 (dualNumerators100 10 1) ∧
    integerMassCheck 100 10 1 (dualNumerators100 10 1) := by
  apply integerChecks_of_simple 100 10 1 (dualNumerators100 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 560661867464, 344525275673, 0, 844525275674, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 419928145920, 344525275674, 155474724327, 844525275674, 0, 0, 1184800741849, 1308901425339, 1190127971561, 118773453779, 0, 788396879662, 1019185197635, 86215139429, 1142419996822, 42380745027, 492907358117, 612492978948]) (branchResiduals100 10 1) 10683139
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck100_11_0 :
    integerResidualCheck 100 11 0 (dualNumerators100 11 0) ∧
    integerMassCheck 100 11 0 (dualNumerators100 11 0) := by
  apply integerChecks_of_simple 100 11 0 (dualNumerators100 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268434, 0, 562584914689, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 1, 0, 736368196709, 813498294019, 739679135332, 73819158688, 0, 489998333105, 633436104137, 53583766880, 710028043730, 26340152980, 306347970271, 380671900746]) (branchResiduals100 11 0) 15120968
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck100_11_1 :
    integerResidualCheck 100 11 1 (dualNumerators100 11 1) ∧
    integerMassCheck 100 11 1 (dualNumerators100 11 1) := by
  apply integerChecks_of_simple 100 11 1 (dualNumerators100 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 674502345597, 67314587240, 0, 446822154676, 577620913742, 48862235962, 647463958437, 24019191727, 279354134309, 347129015395]) (branchResiduals100 11 1) 15120968
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck100_12_0 :
    integerResidualCheck 100 12 0 (dualNumerators100 12 0) ∧
    integerMassCheck 100 12 0 (dualNumerators100 12 0) := by
  apply integerChecks_of_simple 100 12 0 (dualNumerators100 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1556835168689, 155370426011, 0, 1031321016287, 1333220793899, 112780107975, 1494427213684, 55439277044, 644784030255, 801216871619]) (branchResiduals100 12 0) 16348076
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck100_12_1 :
    integerResidualCheck 100 12 1 (dualNumerators100 12 1) ∧
    integerMassCheck 100 12 1 (dualNumerators100 12 1) := by
  apply integerChecks_of_simple 100 12 1 (dualNumerators100 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals100 12 1) 16348076
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck100_13_0 :
    integerResidualCheck 100 13 0 (dualNumerators100 13 0) ∧
    integerMassCheck 100 13 0 (dualNumerators100 13 0) := by
  apply integerChecks_of_simple 100 13 0 (dualNumerators100 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals100 13 0) 13962901
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck100_13_1 :
    integerResidualCheck 100 13 1 (dualNumerators100 13 1) ∧
    integerMassCheck 100 13 1 (dualNumerators100 13 1) := by
  apply integerChecks_of_simple 100 13 1 (dualNumerators100 13 1)
    (![280984417303, 51728439727, 280984417303, 0, 1, 422262637837, 500000000000, 0, 393964356797, 280984417303, 422262637837, 0, 0, 52371963954, 0, 0, 414120121179, 52371963954, 946336320750, 799204942162, 435488332794, 654450712669, 435488332794, 515660508144, 422262637837, 0, 0, 52371963954, 500000000001, 0, 654450712669, 723000450937, 657393325008, 65607125930, 0, 435488332794, 562969329251, 47622825889, 631040777305, 23409935365, 272268205451, 338323949689]) (branchResiduals100 13 1) 13962901
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck100_14_0 :
    integerResidualCheck 100 14 0 (dualNumerators100 14 0) ∧
    integerMassCheck 100 14 0 (dualNumerators100 14 0) := by
  apply integerChecks_of_simple 100 14 0 (dualNumerators100 14 0)
    (![194975514542, 35894443005, 194975514542, 0, 1, 293008686654, 346950760497, 0, 273372466399, 194975514542, 0, 293008686654, 0, 0, 730242506439, 0, 0, 323699567405, 656664212341, 554569524952, 302186016501, 454124344937, 302186016501, 357817610917, 0, 293008686654, 0, 0, 59592178538, 323699567405, 454124344937, 501691112584, 456166228114, 45524884471, 0, 302186016501, 390645273840, 33045551319, 437880155181, 16244189756, 188927321881, 234763503278]) (branchResiduals100 14 0) 20161291
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck100_14_1 :
    integerResidualCheck 100 14 1 (dualNumerators100 14 1) ∧
    integerMassCheck 100 14 1 (dualNumerators100 14 1) := by
  apply integerChecks_of_simple 100 14 1 (dualNumerators100 14 1)
    (![561968834605, 103456879454, 561968834605, 0, 1, 844525275673, 1000000000000, 0, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 0, 1000000000000, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1314786650015, 131214251859, 0, 870976665588, 1125938658501, 95245651778, 1262081554610, 46819870729, 544536410901, 676647899378]) (branchResiduals100 14 1) 20161291
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck100_15_0 :
    integerResidualCheck 100 15 0 (dualNumerators100 15 0) ∧
    integerMassCheck 100 15 0 (dualNumerators100 15 0) := by
  apply integerChecks_of_simple 100 15 0 (dualNumerators100 15 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546385, 0, 844525275675, 602334801077, 221089960013, 684097183123, 0, 1184097183122, 1071829546385, 0, 0, 0, 2028622458796, 1713222941252, 933538524389, 1402919220983, 933538524389, 1105400337064, 905187143136, 1, 684097183123, 500000000000, 0, 0, 1402919220983, 1549866490727, 1409227178679, 140639312049, 0, 933538524389, 1206814321599, 102087103741, 1352736300179, 50182920805, 583650214286, 725251211053]) (branchResiduals100 15 0) 12900283
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck100_15_1 :
    integerResidualCheck 100 15 1 (dualNumerators100 15 1) ∧
    integerMassCheck 100 15 1 (dualNumerators100 15 1) := by
  apply integerChecks_of_simple 100 15 1 (dualNumerators100 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals100 15 1) 12900283
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck100_16_0 :
    integerResidualCheck 100 16 0 (dualNumerators100 16 0) ∧
    integerMassCheck 100 16 0 (dualNumerators100 16 0) := by
  apply integerChecks_of_simple 100 16 0 (dualNumerators100 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals100 16 0) 10683060
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck100_16_1 :
    integerResidualCheck 100 16 1 (dualNumerators100 16 1) ∧
    integerMassCheck 100 16 1 (dualNumerators100 16 1) := by
  apply integerChecks_of_simple 100 16 1 (dualNumerators100 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 0, 0, 0, 0, 1184800741849, 1308901425339, 1190127971561, 118773453779, 0, 788396879662, 1019185197635, 86215139429, 1142419996822, 42380745027, 492907358117, 612492978948]) (branchResiduals100 16 1) 10683060
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck100_17_0 :
    integerResidualCheck 100 17 0 (dualNumerators100 17 0) ∧
    integerMassCheck 100 17 0 (dualNumerators100 17 0) := by
  apply integerChecks_of_simple 100 17 0 (dualNumerators100 17 0)
    (![602334801078, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546386, 0, 844525275676, 602334801077, 0, 905187143137, 278910039987, 905187143136, 1071829546386, 0, 0, 1000000000001, 2028622458797, 1713222941254, 933538524390, 1402919220984, 933538524390, 1105400337065, 905187143136, 1, 1184097183123, 0, 0, 0, 1402919220984, 1549866490728, 1409227178680, 140639312049, 0, 933538524390, 1206814321600, 102087103741, 1352736300180, 50182920805, 583650214286, 725251211054]) (branchResiduals100 17 0) 15120968
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck100_17_1 :
    integerResidualCheck 100 17 1 (dualNumerators100 17 1) ∧
    integerMassCheck 100 17 1 (dualNumerators100 17 1) := by
  apply integerChecks_of_simple 100 17 1 (dualNumerators100 17 1)
    (![508686963928, 93647837150, 508686963928, 0, 1, 764453421592, 905187143136, 0, 713222941253, 508686963927, 764453421593, 0, 0, 1000000000000, 905187143136, 0, 844525275674, 0, 1713222941251, 1446860076751, 788396879661, 1184800741848, 788396879661, 933538524388, 764453421592, 1, 0, 1000000000000, 0, 0, 1184800741848, 1308901425338, 1190127971560, 118773453779, 0, 788396879661, 1019185197635, 86215139429, 1142419996822, 42380745027, 492907358117, 612492978947]) (branchResiduals100 17 1) 15120968
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck100_18_0 :
    integerResidualCheck 100 18 0 (dualNumerators100 18 0) ∧
    integerMassCheck 100 18 0 (dualNumerators100 18 0) := by
  apply integerChecks_of_simple 100 18 0 (dualNumerators100 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 562515489548, 74022925577, 0, 476109064652, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 1065874698487, 202522000941, 0, 763999473637, 900221849434, 170971222815, 953519106044, 33030453619, 477654049462, 593539022787]) (branchResiduals100 18 0) 13565580
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck100_18_1 :
    integerResidualCheck 100 18 1 (dualNumerators100 18 1) ∧
    integerMassCheck 100 18 1 (dualNumerators100 18 1) := by
  apply integerChecks_of_simple 100 18 1 (dualNumerators100 18 1)
    (![543792441172, 100110656623, 543792441172, 0, 1, 180671424657, 213932525007, 0, 71292007252, 50847095100, 88490012639, 92181412018, 0, 592902881267, 213932525007, 0, 0, 500721469249, 171249542446, 144624567043, 842805682483, 280016586907, 78806208846, 93314209907, 180671424657, 1, 92181412018, 500721469249, 0, 0, 280016586907, 776051426377, 127580111437, 3254448853, 78806208846, 0, 110493093096, 0, 188935308970, 91081277938, 49269804597, 61223288500]) (branchResiduals100 18 1) 13565580
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck100_19_0 :
    integerResidualCheck 100 19 0 (dualNumerators100 19 0) ∧
    integerMassCheck 100 19 0 (dualNumerators100 19 0) := by
  apply integerChecks_of_simple 100 19 0 (dualNumerators100 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 216703300504, 217988955956, 0, 1402086139076, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 813889575590, 257303496658, 0, 645216866088, 673991557577, 230658067064, 653752451905, 19962510160, 403390917798, 501258706842]) (branchResiduals100 19 0) 8248658
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck100_19_1 :
    integerResidualCheck 100 19 1 (dualNumerators100 19 1) ∧
    integerMassCheck 100 19 1 (dualNumerators100 19 1) := by
  apply integerChecks_of_simple 100 19 1 (dualNumerators100 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 1, 0, 0, 0, 0, 987477735649, 0, 744995341971, 19004131667, 109777015092, 350406455885, 645216866088, 0, 838241775552, 149235960098, 287707656866, 357509209222]) (branchResiduals100 19 1) 8248658
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck100_20_0 :
    integerResidualCheck 100 20 0 (dualNumerators100 20 0) ∧
    integerMassCheck 100 20 0 (dualNumerators100 20 0) := by
  apply integerChecks_of_simple 100 20 0 (dualNumerators100 20 0)
    (![581614421966, 107073576748, 581614421967, 0, 2, 2066609823263, 2447066870339, 0, 815473519327, 581614421966, 1888845602176, 177764221089, 0, 1143364118230, 2447066870339, 0, 0, 965599897144, 1958837637556, 1654287895857, 901424703129, 3202969314485, 901424703129, 1067374451772, 2066609823263, 2, 177764221088, 965599897143, 0, 0, 3202969314485, 1496550924032, 1459324915655, 37226008378, 901424703129, 0, 1263875081678, 0, 2161136251736, 1041833062749, 563572586882, 700302494796]) (branchResiduals100 20 0) 35312013
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck100_20_1 :
    integerResidualCheck 100 20 1 (dualNumerators100 20 1) ∧
    integerMassCheck 100 20 1 (dualNumerators100 20 1) := by
  apply integerChecks_of_simple 100 20 1 (dualNumerators100 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748478, 25837005087, 1204076434982, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals100 20 1) 35312013
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck100_21_0 :
    integerResidualCheck 100 21 0 (dualNumerators100 21 0) ∧
    integerMassCheck 100 21 0 (dualNumerators100 21 0) := by
  apply integerChecks_of_simple 100 21 0 (dualNumerators100 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 604293255477, 704608169863, 851509250277, 798941670661, 583650214286, 725251211053]) (branchResiduals100 21 0) 11182451
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck100_21_1 :
    integerResidualCheck 100 21 1 (dualNumerators100 21 1) ∧
    integerMassCheck 100 21 1 (dualNumerators100 21 1) := by
  apply integerChecks_of_simple 100 21 1 (dualNumerators100 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 917967404853, 905358228364, 3460174706, 161253783489, 75547476522, 155395681176, 0, 0, 102979506989, 127963650709]) (branchResiduals100 21 1) 11182451
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck100_22_0 :
    integerResidualCheck 100 22 0 (dualNumerators100 22 0) ∧
    integerMassCheck 100 22 0 (dualNumerators100 22 0) := by
  apply integerChecks_of_simple 100 22 0 (dualNumerators100 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 583695195717, 0, 612220343874, 0, 492945346072, 1, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554683, 1, 583695195717, 0, 0, 0, 801336080718, 763999473637, 234488508312, 529510965326, 460183470977, 0, 194101336204, 451115529884, 310954038967, 490382041752, 287707656866, 357509209222]) (branchResiduals100 22 0) 6465674
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck100_22_1 :
    integerResidualCheck 100 22 1 (dualNumerators100 22 1) ∧
    integerMassCheck 100 22 1 (dualNumerators100 22 1) := by
  apply integerChecks_of_simple 100 22 1 (dualNumerators100 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 108732662288, 12539033463, 1534493418, 71511669319, 33503252091, 68913760194, 0, 0, 45668611868, 56748400418]) (branchResiduals100 22 1) 6465674
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck100_23_0 :
    integerResidualCheck 100 23 0 (dualNumerators100 23 0) ∧
    integerMassCheck 100 23 0 (dualNumerators100 23 0) := by
  apply integerChecks_of_simple 100 23 0 (dualNumerators100 23 0)
    (![581614421966, 107073576748, 581614421967, 0, 2, 2066609823263, 2447066870339, 0, 815473519327, 581614421966, 1888845602178, 177764221088, 0, 1143364118230, 2447066870339, 0, 0, 965599897144, 1958837637556, 1654287895857, 901424703129, 3202969314485, 901424703129, 1067374451772, 2066609823265, 0, 177764221088, 965599897143, 0, 0, 3202969314485, 1496550924032, 459324915655, 1037226008378, 901424703129, 0, 1263875081678, 0, 2161136251736, 1041833062749, 563572586882, 700302494796]) (branchResiduals100 23 0) 35297932
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck100_23_1 :
    integerResidualCheck 100 23 1 (dualNumerators100 23 1) ∧
    integerMassCheck 100 23 1 (dualNumerators100 23 1) := by
  apply integerChecks_of_simple 100 23 1 (dualNumerators100 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1830784228945, 211125748477, 25837005087, 1204076434982, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals100 23 1) 35297932
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck100_24_0 :
    integerResidualCheck 100 24 0 (dualNumerators100 24 0) ∧
    integerMassCheck 100 24 0 (dualNumerators100 24 0) := by
  apply integerChecks_of_simple 100 24 0 (dualNumerators100 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 276221246109, 150663467366, 0, 969054410724, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 384946583730, 686246488518, 569308312247, 737522866658, 477654049462, 593539022787]) (branchResiduals100 24 0) 9356857
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck100_24_1 :
    integerResidualCheck 100 24 1 (dualNumerators100 24 1) ∧
    integerMassCheck 100 24 1 (dualNumerators100 24 1) := by
  apply integerChecks_of_simple 100 24 1 (dualNumerators100 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 395480180778, 20824623507, 0, 133942179966, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 690777049383, 178822020994, 48434165160, 99625565721, 0, 0, 66021086067, 82038644814]) (branchResiduals100 24 1) 9356857
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck100_25_0 :
    integerResidualCheck 100 25 0 (dualNumerators100 25 0) ∧
    integerMassCheck 100 25 0 (dualNumerators100 25 0) := by
  apply integerChecks_of_simple 100 25 0 (dualNumerators100 25 0)
    (![34423495944, 6337268637, 34423495944, 0, 1, 22181646803, 26265225496, 0, 631959902239, 450728300227, 377366713580, 137760279295, 0, 886062219380, 609960421212, 0, 0, 748301940086, 1518022121617, 1282008050738, 53351822857, 34378591088, 698568688945, 827173216796, 515126992874, 1, 137760279295, 748301940085, 0, 0, 798378064725, 1159768101884, 492180793363, 667587308522, 53351822857, 0, 340714859712, 638738616250, 34378591088, 0, 436746587681, 542706888281]) (branchResiduals100 25 0) 8671199
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck100_25_1 :
    integerResidualCheck 100 25 1 (dualNumerators100 25 1) ∧
    integerMassCheck 100 25 1 (dualNumerators100 25 1) := by
  apply integerChecks_of_simple 100 25 1 (dualNumerators100 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 415529968297, 599898615461, 0, 0]) (branchResiduals100 25 1) 8671199
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck100_26_0 :
    integerResidualCheck 100 26 0 (dualNumerators100 26 0) ∧
    integerMassCheck 100 26 0 (dualNumerators100 26 0) := by
  apply integerChecks_of_simple 100 26 0 (dualNumerators100 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0]) (branchResiduals100 26 0) 15099566
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck100_26_1 :
    integerResidualCheck 100 26 1 (dualNumerators100 26 1) ∧
    integerMassCheck 100 26 1 (dualNumerators100 26 1) := by
  apply integerChecks_of_simple 100 26 1 (dualNumerators100 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 1025837005087, 204076434982, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals100 26 1) 15099566
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck100_27_0 :
    integerResidualCheck 100 27 0 (dualNumerators100 27 0) ∧
    integerMassCheck 100 27 0 (dualNumerators100 27 0) := by
  apply integerChecks_of_simple 100 27 0 (dualNumerators100 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312724, 1, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 286173900105, 455299762271, 340673826058, 423325647580]) (branchResiduals100 27 0) 7338775
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck100_27_1 :
    integerResidualCheck 100 27 1 (dualNumerators100 27 1) ∧
    integerMassCheck 100 27 1 (dualNumerators100 27 1) := by
  apply integerChecks_of_simple 100 27 1 (dualNumerators100 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 234337221023, 181967583262, 0, 1170399780726, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 963066529984, 568871411225, 0, 377837583379, 762995144865, 530765167250, 621055226706, 24161639382, 236224837801, 293536000677]) (branchResiduals100 27 1) 7338775
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck100_28_0 :
    integerResidualCheck 100 28 0 (dualNumerators100 28 0) ∧
    integerMassCheck 100 28 0 (dualNumerators100 28 0) := by
  apply integerChecks_of_simple 100 28 0 (dualNumerators100 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 1, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 450383711774, 395438493575, 287707656866, 357509209222]) (branchResiduals100 28 0) 10335557
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck100_28_1 :
    integerResidualCheck 100 28 1 (dualNumerators100 28 1) ∧
    integerMassCheck 100 28 1 (dualNumerators100 28 1) := by
  apply integerChecks_of_simple 100 28 1 (dualNumerators100 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 484442151291, 449974794159, 2156352207, 100492021777, 362407121329, 426731607121, 0, 0, 64175975503, 79745886859]) (branchResiduals100 28 1) 10335557
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck100_29_0 :
    integerResidualCheck 100 29 0 (dualNumerators100 29 0) ∧
    integerMassCheck 100 29 0 (dualNumerators100 29 0) := by
  apply integerChecks_of_simple 100 29 0 (dualNumerators100 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0]) (branchResiduals100 29 0) 40352153
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck100_29_1 :
    integerResidualCheck 100 29 1 (dualNumerators100 29 1) ∧
    integerMassCheck 100 29 1 (dualNumerators100 29 1) := by
  apply integerChecks_of_simple 100 29 1 (dualNumerators100 29 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1830784228945, 211125748477, 25837005087, 1204076434982, 1564110399358, 160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals100 29 1) 40352153
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck100_30_0 :
    integerResidualCheck 100 30 0 (dualNumerators100 30 0) ∧
    integerMassCheck 100 30 0 (dualNumerators100 30 0) := by
  apply integerChecks_of_simple 100 30 0 (dualNumerators100 30 0)
    (![49325597255, 9080703511, 49325597255, 0, 0, 3298611714, 3905876838, 0, 69158736213, 49325597255, 0, 3298611714, 11777228989, 85189276451, 3905876838, 0, 0, 81890664738, 166125241653, 1140296965504, 76448090321, 5112407761, 76448090321, 90521968404, 3298611714, 0, 15075840703, 81890664738, 0, 0, 5112407761, 126919597181, 114050929660, 12868667522, 1351620770, 75096469552, 97475206242, 9711601556, 5112407761, 0, 107186807798, 0]) (branchResiduals100 30 0) 7680628
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck100_30_1 :
    integerResidualCheck 100 30 1 (dualNumerators100 30 1) ∧
    integerMassCheck 100 30 1 (dualNumerators100 30 1) := by
  apply integerChecks_of_simple 100 30 1 (dualNumerators100 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714054, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 822559133868, 82090490772, 0, 544901951702, 704411721639, 59587751998, 893898125793, 34752663293, 281282522283, 482716951355]) (branchResiduals100 30 1) 7680628
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck100_31_0 :
    integerResidualCheck 100 31 0 (dualNumerators100 31 0) ∧
    integerMassCheck 100 31 0 (dualNumerators100 31 0) := by
  apply integerChecks_of_simple 100 31 0 (dualNumerators100 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 940234337176, 92181304950, 0, 592902192609, 1222480453651, 0, 0, 500720887661, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642124, 1, 92181304949, 500720887660, 0, 0, 1600106408231, 776050524992, 756746629027, 19303895966, 820904449873, 751938125789, 655394283556, 0, 732639129519, 867467278713, 655394283556, 0]) (branchResiduals100 31 0) 32891612
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck100_31_1 :
    integerResidualCheck 100 31 1 (dualNumerators100 31 1) ∧
    integerMassCheck 100 31 1 (dualNumerators100 31 1) := by
  apply integerChecks_of_simple 100 31 1 (dualNumerators100 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 274671058114, 217988955956, 0, 1402086139076, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 556963843680, 992902647048, 725570984152, 37986262977, 327950144489, 1221916346239]) (branchResiduals100 31 1) 32891612
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck100_32_0 :
    integerResidualCheck 100 32 0 (dualNumerators100 32 0) ∧
    integerMassCheck 100 32 0 (dualNumerators100 32 0) := by
  apply integerChecks_of_simple 100 32 0 (dualNumerators100 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 1713354977902, 1030113130681, 2028778803022, 0, 505064750776, 2743468108580, 0, 1713354977903, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 315423825121, 1713354977902, 0, 0, 4252009289869, 2655471466972, 2414506401585, 240965065387, 0, 1599482877825, 2067701325315, 174911447373, 4074076396250, 177932893619, 0, 2242612772688]) (branchResiduals100 32 0) 67647473
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck100_32_1 :
    integerResidualCheck 100 32 1 (dualNumerators100 32 1) ∧
    integerMassCheck 100 32 1 (dualNumerators100 32 1) := by
  apply integerChecks_of_simple 100 32 1 (dualNumerators100 32 1)
    (![830518849052, 152896180641, 830518849053, 0, 1, 55540314888, 65765130409, 0, 1164458966499, 830518849051, 0, 55540314888, 198298879473, 1434372896977, 65765130409, 0, 0, 1378832582090, 2797130742946, 2362247611782, 1287193334063, 86080072929, 1287193334063, 1524162000997, 55540314888, 1, 253839194360, 1378832582089, 0, 0, 86080072929, 2137006415304, 1920330459346, 216675955958, 22757890183, 1264435443881, 1641237016970, 163518915031, 86080072929, 0, 1804755932001, 0]) (branchResiduals100 32 1) 67647473
    branchSparseDots100 branchIntegerCurvature100 branchDots100
    branchIntegerCurvature100_entry rfl
    (congrFun (congrFun branchResiduals100_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks100 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 100 j s (dualNumerators100 j s) ∧
    integerMassCheck 100 j s (dualNumerators100 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck100_0_0
    · exact integerCheck100_0_1
  · fin_cases s
    · exact integerCheck100_1_0
    · exact integerCheck100_1_1
  · fin_cases s
    · exact integerCheck100_2_0
    · exact integerCheck100_2_1
  · fin_cases s
    · exact integerCheck100_3_0
    · exact integerCheck100_3_1
  · fin_cases s
    · exact integerCheck100_4_0
    · exact integerCheck100_4_1
  · fin_cases s
    · exact integerCheck100_5_0
    · exact integerCheck100_5_1
  · fin_cases s
    · exact integerCheck100_6_0
    · exact integerCheck100_6_1
  · fin_cases s
    · exact integerCheck100_7_0
    · exact integerCheck100_7_1
  · fin_cases s
    · exact integerCheck100_8_0
    · exact integerCheck100_8_1
  · fin_cases s
    · exact integerCheck100_9_0
    · exact integerCheck100_9_1
  · fin_cases s
    · exact integerCheck100_10_0
    · exact integerCheck100_10_1
  · fin_cases s
    · exact integerCheck100_11_0
    · exact integerCheck100_11_1
  · fin_cases s
    · exact integerCheck100_12_0
    · exact integerCheck100_12_1
  · fin_cases s
    · exact integerCheck100_13_0
    · exact integerCheck100_13_1
  · fin_cases s
    · exact integerCheck100_14_0
    · exact integerCheck100_14_1
  · fin_cases s
    · exact integerCheck100_15_0
    · exact integerCheck100_15_1
  · fin_cases s
    · exact integerCheck100_16_0
    · exact integerCheck100_16_1
  · fin_cases s
    · exact integerCheck100_17_0
    · exact integerCheck100_17_1
  · fin_cases s
    · exact integerCheck100_18_0
    · exact integerCheck100_18_1
  · fin_cases s
    · exact integerCheck100_19_0
    · exact integerCheck100_19_1
  · fin_cases s
    · exact integerCheck100_20_0
    · exact integerCheck100_20_1
  · fin_cases s
    · exact integerCheck100_21_0
    · exact integerCheck100_21_1
  · fin_cases s
    · exact integerCheck100_22_0
    · exact integerCheck100_22_1
  · fin_cases s
    · exact integerCheck100_23_0
    · exact integerCheck100_23_1
  · fin_cases s
    · exact integerCheck100_24_0
    · exact integerCheck100_24_1
  · fin_cases s
    · exact integerCheck100_25_0
    · exact integerCheck100_25_1
  · fin_cases s
    · exact integerCheck100_26_0
    · exact integerCheck100_26_1
  · fin_cases s
    · exact integerCheck100_27_0
    · exact integerCheck100_27_1
  · fin_cases s
    · exact integerCheck100_28_0
    · exact integerCheck100_28_1
  · fin_cases s
    · exact integerCheck100_29_0
    · exact integerCheck100_29_1
  · fin_cases s
    · exact integerCheck100_30_0
    · exact integerCheck100_30_1
  · fin_cases s
    · exact integerCheck100_31_0
    · exact integerCheck100_31_1
  · fin_cases s
    · exact integerCheck100_32_0
    · exact integerCheck100_32_1

end ElevenSquare.Tasks.T06
