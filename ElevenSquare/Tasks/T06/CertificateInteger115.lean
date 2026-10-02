import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual115
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
import ElevenSquare.Tasks.T06.SparseColumn32
import ElevenSquare.Tasks.T06.SparseColumn35
import ElevenSquare.Tasks.T06.SparseColumn36
import ElevenSquare.Tasks.T06.SparseColumn38
import ElevenSquare.Tasks.T06.SparseColumn39
import ElevenSquare.Tasks.T06.SparseColumn41
import ElevenSquare.Tasks.T06.SparseColumn48
import ElevenSquare.Tasks.T06.SparseColumn54
import ElevenSquare.Tasks.T06.SparseColumn56
import ElevenSquare.Tasks.T06.SparseColumn58

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix115 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix115_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = branchIntegerMatrix115 := by
  change roundedGradients ∘ branchRows 115 = branchIntegerMatrix115
  rw [show branchRows 115 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix115]

theorem branchColumn115_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 0) i) = _
  rw [branchColumn115_0]
  exact sparseColumn00_sum n

theorem branchColumn115_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 1) i) = _
  rw [branchColumn115_1]
  exact sparseColumn01_sum n

theorem branchColumn115_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 2) i) = _
  rw [branchColumn115_2]
  exact sparseColumn02_sum n

theorem branchColumn115_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 3) i) = _
  rw [branchColumn115_3]
  exact sparseColumn03_sum n

theorem branchColumn115_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 4) i) = _
  rw [branchColumn115_4]
  exact sparseColumn04_sum n

theorem branchColumn115_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 5) i) = _
  rw [branchColumn115_5]
  exact sparseColumn05_sum n

theorem branchColumn115_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 6) i) = _
  rw [branchColumn115_6]
  exact sparseColumn06_sum n

theorem branchColumn115_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 7) i) = _
  rw [branchColumn115_7]
  exact sparseColumn07_sum n

theorem branchColumn115_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 8) i) = _
  rw [branchColumn115_8]
  exact sparseColumn08_sum n

theorem branchColumn115_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 9) i) = _
  rw [branchColumn115_9]
  exact sparseColumn09_sum n

theorem branchColumn115_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 10) i) = _
  rw [branchColumn115_10]
  exact sparseColumn10_sum n

theorem branchColumn115_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 11) i) = _
  rw [branchColumn115_11]
  exact sparseColumn11_sum n

theorem branchColumn115_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 12) i) = _
  rw [branchColumn115_12]
  exact sparseColumn35_sum n

theorem branchColumn115_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 13) i) = _
  rw [branchColumn115_13]
  exact sparseColumn36_sum n

theorem branchColumn115_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 14) i) = _
  rw [branchColumn115_14]
  exact sparseColumn41_sum n

theorem branchColumn115_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 15) i) = _
  rw [branchColumn115_15]
  exact sparseColumn38_sum n

theorem branchColumn115_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 16) i) = _
  rw [branchColumn115_16]
  exact sparseColumn39_sum n

theorem branchColumn115_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 17) i) = _
  rw [branchColumn115_17]
  exact sparseColumn17_sum n

theorem branchColumn115_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 18) i) = _
  rw [branchColumn115_18]
  exact sparseColumn18_sum n

theorem branchColumn115_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 19) i) = _
  rw [branchColumn115_19]
  exact sparseColumn19_sum n

theorem branchColumn115_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 20) = sparseColumn58 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 20) = sparseDot58 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 20) i) = _
  rw [branchColumn115_20]
  exact sparseColumn58_sum n

theorem branchColumn115_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 21) i) = _
  rw [branchColumn115_21]
  exact sparseColumn21_sum n

theorem branchColumn115_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 22) i) = _
  rw [branchColumn115_22]
  exact sparseColumn22_sum n

theorem branchColumn115_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 23) = sparseColumn54 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 23) = sparseDot54 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 23) i) = _
  rw [branchColumn115_23]
  exact sparseColumn54_sum n

theorem branchColumn115_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 24) i) = _
  rw [branchColumn115_24]
  exact sparseColumn24_sum n

theorem branchColumn115_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 25) i) = _
  rw [branchColumn115_25]
  exact sparseColumn25_sum n

theorem branchColumn115_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 26) = sparseColumn56 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 26) = sparseDot56 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 26) i) = _
  rw [branchColumn115_26]
  exact sparseColumn56_sum n

theorem branchColumn115_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 27) i) = _
  rw [branchColumn115_27]
  exact sparseColumn27_sum n

theorem branchColumn115_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 28) i) = _
  rw [branchColumn115_28]
  exact sparseColumn28_sum n

theorem branchColumn115_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 29) = sparseColumn48 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 29) = sparseDot48 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 29) i) = _
  rw [branchColumn115_29]
  exact sparseColumn48_sum n

theorem branchColumn115_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 30) i) = _
  rw [branchColumn115_30]
  exact sparseColumn30_sum n

theorem branchColumn115_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 31) i) = _
  rw [branchColumn115_31]
  exact sparseColumn31_sum n

theorem branchColumn115_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 115 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 115 i)) = _
  rw [branchIntegerMatrix115_eq]
  simp only [branchIntegerMatrix115, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot115_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 115 i) 32) i) = _
  rw [branchColumn115_32]
  exact sparseColumn32_sum n

def branchSparseDots115 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot58, sparseDot21, sparseDot22, sparseDot54, sparseDot24, sparseDot25, sparseDot56, sparseDot27, sparseDot28, sparseDot48, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot115_0 :
    branchSparseDots115 0 = sparseDot00 := rfl

private theorem branchSparseDot115_1 :
    branchSparseDots115 1 = sparseDot01 := rfl

private theorem branchSparseDot115_2 :
    branchSparseDots115 2 = sparseDot02 := rfl

private theorem branchSparseDot115_3 :
    branchSparseDots115 3 = sparseDot03 := rfl

private theorem branchSparseDot115_4 :
    branchSparseDots115 4 = sparseDot04 := rfl

private theorem branchSparseDot115_5 :
    branchSparseDots115 5 = sparseDot05 := rfl

private theorem branchSparseDot115_6 :
    branchSparseDots115 6 = sparseDot06 := rfl

private theorem branchSparseDot115_7 :
    branchSparseDots115 7 = sparseDot07 := rfl

private theorem branchSparseDot115_8 :
    branchSparseDots115 8 = sparseDot08 := rfl

private theorem branchSparseDot115_9 :
    branchSparseDots115 9 = sparseDot09 := rfl

private theorem branchSparseDot115_10 :
    branchSparseDots115 10 = sparseDot10 := rfl

private theorem branchSparseDot115_11 :
    branchSparseDots115 11 = sparseDot11 := rfl

private theorem branchSparseDot115_12 :
    branchSparseDots115 12 = sparseDot35 := rfl

private theorem branchSparseDot115_13 :
    branchSparseDots115 13 = sparseDot36 := rfl

private theorem branchSparseDot115_14 :
    branchSparseDots115 14 = sparseDot41 := rfl

private theorem branchSparseDot115_15 :
    branchSparseDots115 15 = sparseDot38 := rfl

private theorem branchSparseDot115_16 :
    branchSparseDots115 16 = sparseDot39 := rfl

private theorem branchSparseDot115_17 :
    branchSparseDots115 17 = sparseDot17 := rfl

private theorem branchSparseDot115_18 :
    branchSparseDots115 18 = sparseDot18 := rfl

private theorem branchSparseDot115_19 :
    branchSparseDots115 19 = sparseDot19 := rfl

private theorem branchSparseDot115_20 :
    branchSparseDots115 20 = sparseDot58 := rfl

private theorem branchSparseDot115_21 :
    branchSparseDots115 21 = sparseDot21 := rfl

private theorem branchSparseDot115_22 :
    branchSparseDots115 22 = sparseDot22 := rfl

private theorem branchSparseDot115_23 :
    branchSparseDots115 23 = sparseDot54 := rfl

private theorem branchSparseDot115_24 :
    branchSparseDots115 24 = sparseDot24 := rfl

private theorem branchSparseDot115_25 :
    branchSparseDots115 25 = sparseDot25 := rfl

private theorem branchSparseDot115_26 :
    branchSparseDots115 26 = sparseDot56 := rfl

private theorem branchSparseDot115_27 :
    branchSparseDots115 27 = sparseDot27 := rfl

private theorem branchSparseDot115_28 :
    branchSparseDots115 28 = sparseDot28 := rfl

private theorem branchSparseDot115_29 :
    branchSparseDots115 29 = sparseDot48 := rfl

private theorem branchSparseDot115_30 :
    branchSparseDots115 30 = sparseDot30 := rfl

private theorem branchSparseDot115_31 :
    branchSparseDots115 31 = sparseDot31 := rfl

private theorem branchSparseDot115_32 :
    branchSparseDots115 32 = sparseDot32 := rfl

theorem branchDots115 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 115 i) k) = branchSparseDots115 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot115_0 n
      _ = _ := congrFun branchSparseDot115_0.symm n
  · calc
      _ = sparseDot01 n := branchDot115_1 n
      _ = _ := congrFun branchSparseDot115_1.symm n
  · calc
      _ = sparseDot02 n := branchDot115_2 n
      _ = _ := congrFun branchSparseDot115_2.symm n
  · calc
      _ = sparseDot03 n := branchDot115_3 n
      _ = _ := congrFun branchSparseDot115_3.symm n
  · calc
      _ = sparseDot04 n := branchDot115_4 n
      _ = _ := congrFun branchSparseDot115_4.symm n
  · calc
      _ = sparseDot05 n := branchDot115_5 n
      _ = _ := congrFun branchSparseDot115_5.symm n
  · calc
      _ = sparseDot06 n := branchDot115_6 n
      _ = _ := congrFun branchSparseDot115_6.symm n
  · calc
      _ = sparseDot07 n := branchDot115_7 n
      _ = _ := congrFun branchSparseDot115_7.symm n
  · calc
      _ = sparseDot08 n := branchDot115_8 n
      _ = _ := congrFun branchSparseDot115_8.symm n
  · calc
      _ = sparseDot09 n := branchDot115_9 n
      _ = _ := congrFun branchSparseDot115_9.symm n
  · calc
      _ = sparseDot10 n := branchDot115_10 n
      _ = _ := congrFun branchSparseDot115_10.symm n
  · calc
      _ = sparseDot11 n := branchDot115_11 n
      _ = _ := congrFun branchSparseDot115_11.symm n
  · calc
      _ = sparseDot35 n := branchDot115_12 n
      _ = _ := congrFun branchSparseDot115_12.symm n
  · calc
      _ = sparseDot36 n := branchDot115_13 n
      _ = _ := congrFun branchSparseDot115_13.symm n
  · calc
      _ = sparseDot41 n := branchDot115_14 n
      _ = _ := congrFun branchSparseDot115_14.symm n
  · calc
      _ = sparseDot38 n := branchDot115_15 n
      _ = _ := congrFun branchSparseDot115_15.symm n
  · calc
      _ = sparseDot39 n := branchDot115_16 n
      _ = _ := congrFun branchSparseDot115_16.symm n
  · calc
      _ = sparseDot17 n := branchDot115_17 n
      _ = _ := congrFun branchSparseDot115_17.symm n
  · calc
      _ = sparseDot18 n := branchDot115_18 n
      _ = _ := congrFun branchSparseDot115_18.symm n
  · calc
      _ = sparseDot19 n := branchDot115_19 n
      _ = _ := congrFun branchSparseDot115_19.symm n
  · calc
      _ = sparseDot58 n := branchDot115_20 n
      _ = _ := congrFun branchSparseDot115_20.symm n
  · calc
      _ = sparseDot21 n := branchDot115_21 n
      _ = _ := congrFun branchSparseDot115_21.symm n
  · calc
      _ = sparseDot22 n := branchDot115_22 n
      _ = _ := congrFun branchSparseDot115_22.symm n
  · calc
      _ = sparseDot54 n := branchDot115_23 n
      _ = _ := congrFun branchSparseDot115_23.symm n
  · calc
      _ = sparseDot24 n := branchDot115_24 n
      _ = _ := congrFun branchSparseDot115_24.symm n
  · calc
      _ = sparseDot25 n := branchDot115_25 n
      _ = _ := congrFun branchSparseDot115_25.symm n
  · calc
      _ = sparseDot56 n := branchDot115_26 n
      _ = _ := congrFun branchSparseDot115_26.symm n
  · calc
      _ = sparseDot27 n := branchDot115_27 n
      _ = _ := congrFun branchSparseDot115_27.symm n
  · calc
      _ = sparseDot28 n := branchDot115_28 n
      _ = _ := congrFun branchSparseDot115_28.symm n
  · calc
      _ = sparseDot48 n := branchDot115_29 n
      _ = _ := congrFun branchSparseDot115_29.symm n
  · calc
      _ = sparseDot30 n := branchDot115_30 n
      _ = _ := congrFun branchSparseDot115_30.symm n
  · calc
      _ = sparseDot31 n := branchDot115_31 n
      _ = _ := congrFun branchSparseDot115_31.symm n
  · calc
      _ = sparseDot32 n := branchDot115_32 n
      _ = _ := congrFun branchSparseDot115_32.symm n

def branchIntegerCurvature115 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101955390, 101955390, 79086693, 79086693, 106371291, 106371291, 48290998, 48290998, 204734428, 204734428]

theorem branchIntegerCurvature115_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 115 i)) = branchIntegerCurvature115 := by
  change curvatureNumerators ∘ branchRows 115 = branchIntegerCurvature115
  rw [show branchRows 115 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature115_entry (i : Fin 42) :
    curvatureNumerators (branchRows 115 i) = branchIntegerCurvature115 i :=
  congrFun branchIntegerCurvature115_eq i

def branchResiduals115 : Fin 33 → Fin 2 → ℕ := ![![1302007150786888, 33000000000000], ![1546830891322960, 33000000000000], ![1583623970800476, 1336560055716508], ![33000000000000, 1024331311443958], ![860323282512716, 33000000000000], ![1053812612435464, 896204395602618], ![720686095128156, 624777238175104], ![33000000000000, 762970896739546], ![1577837324875186, 1128411143185979], ![1025812043689577, 33000000000000], ![33000000000000, 777652167735970], ![507222460245702, 463924212764311], ![990410356255075, 66000000000000], ![33000000000000, 862758930921171], ![1054312612435497, 487191189803987], ![472301526890092, 33000000000000], ![66000000000000, 744141164530545], ![660866167743994, 462876591170177], ![621242870497913, 267959291177275], ![629632743419687, 508600501518558], ![1477700438628792, 854809793236492], ![751321880462813, 374930863842880], ![470648931664499, 90706651221511], ![1477700438628792, 854809793236492], ![666677807455220, 230374054719026], ![506058049045585, 218713669397988], ![396136216194598, 854809793236492], ![408541179298282, 545859315217724], ![283938357332490, 301267805415724], ![396136216194598, 891662691436227], ![216031779062564, 550724103778260], ![1679604272728010, 648436709070965], ![1330357274743913, 2887684082098833]]

theorem branchResiduals115_eq : residualNumerators 115 = branchResiduals115 := rfl

theorem integerCheck115_0_0 :
    integerResidualCheck 115 0 0 (dualNumerators115 0 0) ∧
    integerMassCheck 115 0 0 (dualNumerators115 0 0) := by
  apply integerChecks_of_simple 115 0 0 (dualNumerators115 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1901003851212, 272042472855, 74854042823, 1234047382517, 1835192545884, 0, 1821798773483, 145214820501, 1430871029972, 404321515913]) (branchResiduals115 0 0) 18767167
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck115_0_1 :
    integerResidualCheck 115 0 1 (dualNumerators115 0 1) ∧
    integerMassCheck 115 0 1 (dualNumerators115 0 1) := by
  apply integerChecks_of_simple 115 0 1 (dualNumerators115 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals115 0 1) 18767167
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck115_1_0 :
    integerResidualCheck 115 1 0 (dualNumerators115 1 0) ∧
    integerMassCheck 115 1 0 (dualNumerators115 1 0) := by
  apply integerChecks_of_simple 115 1 0 (dualNumerators115 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 2250973305323, 322124725797, 88634461252, 1461232029476, 2173046324067, 0, 2157186795895, 171948459903, 1694290356000, 478755968067]) (branchResiduals115 1 0) 22176635
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck115_1_1 :
    integerResidualCheck 115 1 1 (dualNumerators115 1 1) ∧
    integerMassCheck 115 1 1 (dualNumerators115 1 1) := by
  apply integerChecks_of_simple 115 1 1 (dualNumerators115 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals115 1 1) 22176635
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck115_2_0 :
    integerResidualCheck 115 2 0 (dualNumerators115 2 0) ∧
    integerMassCheck 115 2 0 (dualNumerators115 2 0) := by
  apply integerChecks_of_simple 115 2 0 (dualNumerators115 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 2250973305325, 322124725797, 88634461252, 1461232029477, 2173046324068, 0, 2157186795897, 171948459903, 1694290356001, 478755968068]) (branchResiduals115 2 0) 22681452
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck115_2_1 :
    integerResidualCheck 115 2 1 (dualNumerators115 2 1) ∧
    integerMassCheck 115 2 1 (dualNumerators115 2 1) := by
  apply integerChecks_of_simple 115 2 1 (dualNumerators115 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1901003851211, 272042472855, 74854042823, 1234047382516, 1835192545883, 0, 1821798773482, 145214820501, 1430871029971, 404321515912]) (branchResiduals115 2 1) 22681452
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck115_3_0 :
    integerResidualCheck 115 3 0 (dualNumerators115 3 0) ∧
    integerMassCheck 115 3 0 (dualNumerators115 3 0) := by
  apply integerChecks_of_simple 115 3 0 (dualNumerators115 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals115 3 0) 16360330
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck115_3_1 :
    integerResidualCheck 115 3 1 (dualNumerators115 3 1) ∧
    integerMassCheck 115 3 1 (dualNumerators115 3 1) := by
  apply integerChecks_of_simple 115 3 1 (dualNumerators115 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000001, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000001, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1497855519021, 214350075679, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 1127424369963, 318576531911]) (branchResiduals115 3 1) 16360330
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck115_4_0 :
    integerResidualCheck 115 4 0 (dualNumerators115 4 0) ∧
    integerMassCheck 115 4 0 (dualNumerators115 4 0) := by
  apply integerChecks_of_simple 115 4 0 (dualNumerators115 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1264976845121, 181024056754, 49809804896, 821166860693, 1221184310279, 0, 1212271749715, 96629675624, 952138376845, 269045933435]) (branchResiduals115 4 0) 13760362
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck115_4_1 :
    integerResidualCheck 115 4 1 (dualNumerators115 4 1) ∧
    integerMassCheck 115 4 1 (dualNumerators115 4 1) := by
  apply integerChecks_of_simple 115 4 1 (dualNumerators115 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals115 4 1) 13760362
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck115_5_0 :
    integerResidualCheck 115 5 0 (dualNumerators115 5 0) ∧
    integerMassCheck 115 5 0 (dualNumerators115 5 0) := by
  apply integerChecks_of_simple 115 5 0 (dualNumerators115 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1497855519022, 214350075679, 58979649669, 972341366620, 1446000901875, 0, 1435447564017, 114418926712, 1127424369964, 318576531911]) (branchResiduals115 5 0) 17641130
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck115_5_1 :
    integerResidualCheck 115 5 1 (dualNumerators115 5 1) ∧
    integerMassCheck 115 5 1 (dualNumerators115 5 1) := by
  apply integerChecks_of_simple 115 5 1 (dualNumerators115 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1264976845120, 181024056754, 49809804896, 821166860692, 1221184310279, 0, 1212271749715, 96629675624, 952138376844, 269045933435]) (branchResiduals115 5 1) 17641130
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck115_6_0 :
    integerResidualCheck 115 6 0 (dualNumerators115 6 0) ∧
    integerMassCheck 115 6 0 (dualNumerators115 6 0) := by
  apply integerChecks_of_simple 115 6 0 (dualNumerators115 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 877488274356, 957704271528, 103906894360, 5439901403, 1430871029972, 404321515913]) (branchResiduals115 6 0) 8962451
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck115_6_1 :
    integerResidualCheck 115 6 1 (dualNumerators115 6 1) ∧
    integerMassCheck 115 6 1 (dualNumerators115 6 1) := by
  apply integerChecks_of_simple 115 6 1 (dualNumerators115 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 760187607595, 1097479190627, 0, 0]) (branchResiduals115 6 1) 8962451
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck115_7_0 :
    integerResidualCheck 115 7 0 (dualNumerators115 7 0) ∧
    integerMassCheck 115 7 0 (dualNumerators115 7 0) := by
  apply integerChecks_of_simple 115 7 0 (dualNumerators115 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals115 7 0) 10424794
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck115_7_1 :
    integerResidualCheck 115 7 1 (dualNumerators115 7 1) ∧
    integerMassCheck 115 7 1 (dualNumerators115 7 1) := by
  apply integerChecks_of_simple 115 7 1 (dualNumerators115 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 1125486652664, 161062362899, 44317230626, 730616014740, 1086523162035, 0, 1078593397950, 85974229952, 847145178002, 239377984034]) (branchResiduals115 7 1) 10424794
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck115_8_0 :
    integerResidualCheck 115 8 0 (dualNumerators115 8 0) ∧
    integerMassCheck 115 8 0 (dualNumerators115 8 0) := by
  apply integerChecks_of_simple 115 8 0 (dualNumerators115 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 2250973305327, 322124725797, 88634461252, 1461232029479, 2173046324070, 0, 2157186795899, 171948459903, 1694290356003, 478755968068]) (branchResiduals115 8 0) 22681452
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck115_8_1 :
    integerResidualCheck 115 8 1 (dualNumerators115 8 1) ∧
    integerMassCheck 115 8 1 (dualNumerators115 8 1) := by
  apply integerChecks_of_simple 115 8 1 (dualNumerators115 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1605445801500, 229746744383, 63216131150, 1042184205913, 1549866490725, 0, 1538555111396, 122637586316, 1208406751039, 341459739686]) (branchResiduals115 8 1) 22681452
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck115_9_0 :
    integerResidualCheck 115 9 0 (dualNumerators115 9 0) ∧
    integerMassCheck 115 9 0 (dualNumerators115 9 0) := by
  apply integerChecks_of_simple 115 9 0 (dualNumerators115 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 1497855519021, 214350075679, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 1127424369963, 318576531911]) (branchResiduals115 9 0) 16350530
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck115_9_1 :
    integerResidualCheck 115 9 1 (dualNumerators115 9 1) ∧
    integerMassCheck 115 9 1 (dualNumerators115 9 1) := by
  apply integerChecks_of_simple 115 9 1 (dualNumerators115 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals115 9 1) 16350530
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck115_10_0 :
    integerResidualCheck 115 10 0 (dualNumerators115 10 0) ∧
    integerMassCheck 115 10 0 (dualNumerators115 10 0) := by
  apply integerChecks_of_simple 115 10 0 (dualNumerators115 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals115 10 0) 10683139
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck115_10_1 :
    integerResidualCheck 115 10 1 (dualNumerators115 10 1) ∧
    integerMassCheck 115 10 1 (dualNumerators115 10 1) := by
  apply integerChecks_of_simple 115 10 1 (dualNumerators115 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 1145040776568, 163860648772, 45087194994, 743309684668, 1105400337064, 0, 1097332801829, 87467940020, 861863417206, 243536919859]) (branchResiduals115 10 1) 10683139
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck115_11_0 :
    integerResidualCheck 115 11 0 (dualNumerators115 11 0) ∧
    integerMassCheck 115 11 0 (dualNumerators115 11 0) := by
  apply integerChecks_of_simple 115 11 0 (dualNumerators115 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 711656890494, 101841403525, 28022244838, 461976088268, 687019871017, 0, 682005798892, 54362397817, 535658687508, 151361183509]) (branchResiduals115 11 0) 15120968
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck115_11_1 :
    integerResidualCheck 115 11 1 (dualNumerators115 11 1) ∧
    integerMassCheck 115 11 1 (dualNumerators115 11 1) := by
  apply integerChecks_of_simple 115 11 1 (dualNumerators115 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 648949279451, 92867653386, 25553066146, 421269088530, 626483149703, 0, 621910892291, 49572257873, 488459149252, 138024000452]) (branchResiduals115 11 1) 15120968
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck115_12_0 :
    integerResidualCheck 115 12 0 (dualNumerators115 12 0) ∧
    integerMassCheck 115 12 0 (dualNumerators115 12 0) := by
  apply integerChecks_of_simple 115 12 0 (dualNumerators115 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1497855519021, 214350075679, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 1127424369963, 318576531911]) (branchResiduals115 12 0) 16348076
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck115_12_1 :
    integerResidualCheck 115 12 1 (dualNumerators115 12 1) ∧
    integerMassCheck 115 12 1 (dualNumerators115 12 1) := by
  apply integerChecks_of_simple 115 12 1 (dualNumerators115 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals115 12 1) 16348076
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck115_13_0 :
    integerResidualCheck 115 13 0 (dualNumerators115 13 0) ∧
    integerMassCheck 115 13 0 (dualNumerators115 13 0) := by
  apply integerChecks_of_simple 115 13 0 (dualNumerators115 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals115 13 0) 13962901
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck115_13_1 :
    integerResidualCheck 115 13 1 (dualNumerators115 13 1) ∧
    integerMassCheck 115 13 1 (dualNumerators115 13 1) := by
  apply integerChecks_of_simple 115 13 1 (dualNumerators115 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000001, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1264976845121, 181024056754, 49809804896, 821166860693, 1221184310279, 0, 1212271749715, 96629675624, 952138376845, 269045933435]) (branchResiduals115 13 1) 13962901
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck115_14_0 :
    integerResidualCheck 115 14 0 (dualNumerators115 14 0) ∧
    integerMassCheck 115 14 0 (dualNumerators115 14 0) := by
  apply integerChecks_of_simple 115 14 0 (dualNumerators115 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000001, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1497855519022, 214350075679, 58979649669, 972341366620, 1446000901875, 0, 1435447564017, 114418926712, 1127424369964, 318576531911]) (branchResiduals115 14 0) 20161291
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck115_14_1 :
    integerResidualCheck 115 14 1 (dualNumerators115 14 1) ∧
    integerMassCheck 115 14 1 (dualNumerators115 14 1) := by
  apply integerChecks_of_simple 115 14 1 (dualNumerators115 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 685800765001, 98141271980, 27004132474, 445191438428, 662058864893, 0, 657226965498, 52387287341, 516196980004, 145861884889]) (branchResiduals115 14 1) 20161291
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck115_15_0 :
    integerResidualCheck 115 15 0 (dualNumerators115 15 0) ∧
    integerMassCheck 115 15 0 (dualNumerators115 15 0) := by
  apply integerChecks_of_simple 115 15 0 (dualNumerators115 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 711656890494, 101841403525, 28022244838, 461976088267, 687019871016, 0, 682005798892, 54362397817, 535658687508, 151361183509]) (branchResiduals115 15 0) 12900283
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck115_15_1 :
    integerResidualCheck 115 15 1 (dualNumerators115 15 1) ∧
    integerMassCheck 115 15 1 (dualNumerators115 15 1) := by
  apply integerChecks_of_simple 115 15 1 (dualNumerators115 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals115 15 1) 12900283
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck115_16_0 :
    integerResidualCheck 115 16 0 (dualNumerators115 16 0) ∧
    integerMassCheck 115 16 0 (dualNumerators115 16 0) := by
  apply integerChecks_of_simple 115 16 0 (dualNumerators115 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals115 16 0) 10683060
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck115_16_1 :
    integerResidualCheck 115 16 1 (dualNumerators115 16 1) ∧
    integerMassCheck 115 16 1 (dualNumerators115 16 1) := by
  apply integerChecks_of_simple 115 16 1 (dualNumerators115 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 1145040776568, 163860648772, 45087194994, 743309684668, 1105400337064, 0, 1097332801829, 87467940020, 861863417206, 243536919859]) (branchResiduals115 16 1) 10683060
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck115_17_0 :
    integerResidualCheck 115 17 0 (dualNumerators115 17 0) ∧
    integerMassCheck 115 17 0 (dualNumerators115 17 0) := by
  apply integerChecks_of_simple 115 17 0 (dualNumerators115 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 933392233473, 133572760085, 36753309138, 605916838014, 901078905318, 0, 894502567701, 71300426643, 702557180842, 198521724476]) (branchResiduals115 17 0) 15120968
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck115_17_1 :
    integerResidualCheck 115 17 1 (dualNumerators115 17 1) ∧
    integerMassCheck 115 17 1 (dualNumerators115 17 1) := by
  apply integerChecks_of_simple 115 17 1 (dualNumerators115 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 648949279451, 92867653386, 25553066146, 421269088530, 626483149703, 0, 621910892291, 49572257873, 488459149252, 138024000452]) (branchResiduals115 17 1) 15120968
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck115_18_0 :
    integerResidualCheck 115 18 0 (dualNumerators115 18 0) ∧
    integerMassCheck 115 18 0 (dualNumerators115 18 0) := by
  apply integerChecks_of_simple 115 18 0 (dualNumerators115 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 1065874698487, 202522000941, 0, 763999473637, 1027460955744, 43732116505, 953519106044, 33030453619, 835192545885, 236000526363]) (branchResiduals115 18 0) 13565580
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck115_18_1 :
    integerResidualCheck 115 18 1 (dualNumerators115 18 1) ∧
    integerMassCheck 115 18 1 (dualNumerators115 18 1) := by
  apply integerChecks_of_simple 115 18 1 (dualNumerators115 18 1)
    (![552774353318, 101764201348, 552774353318, 0, 1, 194169418432, 229915461414, 0, 83885421775, 59829007246, 194169418432, 0, 94926637302, 515633295911, 229915461414, 0, 0, 515633295912, 201500008915, 170171850577, 856726447141, 300936675152, 92726973504, 109797748126, 194169418432, 0, 94926637302, 515633295911, 0, 0, 300936675152, 799162766836, 134673498195, 19272402554, 92726973504, 0, 130011204269, 0, 195186313540, 105750361613, 101367709986, 28643494283]) (branchResiduals115 18 1) 13565580
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck115_19_0 :
    integerResidualCheck 115 19 0 (dualNumerators115 19 0) ∧
    integerMassCheck 115 19 0 (dualNumerators115 19 0) := by
  apply integerChecks_of_simple 115 19 0 (dualNumerators115 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 813889575590, 257303496658, 0, 645216866088, 781448198910, 123201425731, 653752451905, 19962510160, 705341215054, 199308409586]) (branchResiduals115 19 0) 8248658
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck115_19_1 :
    integerResidualCheck 115 19 1 (dualNumerators115 19 1) ∧
    integerMassCheck 115 19 1 (dualNumerators115 19 1) := by
  apply integerChecks_of_simple 115 19 1 (dualNumerators115 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 668354800182, 95644673455, 186417556881, 273765914097, 645216866088, 0, 761601233763, 225876501886, 503065535987, 142151330101]) (branchResiduals115 19 1) 8248658
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck115_20_0 :
    integerResidualCheck 115 20 0 (dualNumerators115 20 0) ∧
    integerMassCheck 115 20 0 (dualNumerators115 20 0) := by
  apply integerChecks_of_simple 115 20 0 (dualNumerators115 20 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 1540462609577, 220447348059, 1060657349048, 0, 1487132967409, 0, 2232638358246, 1209625354629, 1159494400494, 327638566915]) (branchResiduals115 20 0) 35312013
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck115_20_1 :
    integerResidualCheck 115 20 1 (dualNumerators115 20 1) ∧
    integerMassCheck 115 20 1 (dualNumerators115 20 1) := by
  apply integerChecks_of_simple 115 20 1 (dualNumerators115 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals115 20 1) 35312013
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck115_21_0 :
    integerResidualCheck 115 21 0 (dualNumerators115 21 0) ∧
    integerMassCheck 115 21 0 (dualNumerators115 21 0) := by
  apply integerChecks_of_simple 115 21 0 (dualNumerators115 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 759767979803, 549133445537, 851509250277, 798941670661, 1020530044549, 288371380791]) (branchResiduals115 21 0) 11182451
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck115_21_1 :
    integerResidualCheck 115 21 1 (dualNumerators115 21 1) ∧
    integerMassCheck 115 21 1 (dualNumerators115 21 1) := by
  apply integerChecks_of_simple 115 21 1 (dualNumerators115 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 917967404853, 905358228364, 3460174706, 161253783489, 102979506989, 127963650709, 0, 0, 180062781238, 50880376460]) (branchResiduals115 21 1) 11182451
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck115_22_0 :
    integerResidualCheck 115 22 0 (dualNumerators115 22 0) ∧
    integerMassCheck 115 22 0 (dualNumerators115 22 0) := by
  apply integerChecks_of_simple 115 22 0 (dualNumerators115 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 234488508312, 529510965326, 460183470977, 0, 270741877993, 374474988096, 310954038967, 490382041752, 503065535987, 142151330101]) (branchResiduals115 22 0) 6465674
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck115_22_1 :
    integerResidualCheck 115 22 1 (dualNumerators115 22 1) ∧
    integerMassCheck 115 22 1 (dualNumerators115 22 1) := by
  apply integerChecks_of_simple 115 22 1 (dualNumerators115 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 108732662288, 12539033463, 1534493418, 71511669319, 45668611868, 56748400418, 0, 0, 79852948501, 22564063785]) (branchResiduals115 22 1) 6465674
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck115_23_0 :
    integerResidualCheck 115 23 0 (dualNumerators115 23 0) ∧
    integerMassCheck 115 23 0 (dualNumerators115 23 0) := by
  apply integerChecks_of_simple 115 23 0 (dualNumerators115 23 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 540462609577, 1220447348059, 1060657349048, 0, 1487132967409, 0, 2232638358246, 1209625354629, 1159494400494, 327638566915]) (branchResiduals115 23 0) 35297932
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck115_23_1 :
    integerResidualCheck 115 23 1 (dualNumerators115 23 1) ∧
    integerMassCheck 115 23 1 (dualNumerators115 23 1) := by
  apply integerChecks_of_simple 115 23 1 (dualNumerators115 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1830784228945, 211125748477, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals115 23 1) 35297932
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck115_24_0 :
    integerResidualCheck 115 24 0 (dualNumerators115 24 0) ∧
    integerMassCheck 115 24 0 (dualNumerators115 24 0) := by
  apply integerChecks_of_simple 115 24 0 (dualNumerators115 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 512185690040, 559007382209, 569308312247, 737522866658, 835192545885, 236000526363]) (branchResiduals115 24 0) 9356857
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck115_24_1 :
    integerResidualCheck 115 24 1 (dualNumerators115 24 1) ∧
    integerMassCheck 115 24 1 (dualNumerators115 24 1) := by
  apply integerChecks_of_simple 115 24 1 (dualNumerators115 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 690777049383, 178822020994, 66021086067, 82038644814, 0, 0, 115439864933, 32619865948]) (branchResiduals115 24 1) 9356857
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck115_25_0 :
    integerResidualCheck 115 25 0 (dualNumerators115 25 0) ∧
    integerMassCheck 115 25 0 (dualNumerators115 25 0) := by
  apply integerChecks_of_simple 115 25 0 (dualNumerators115 25 0)
    (![34423495944, 6337268637, 34423495944, 0, 1, 22181646803, 26265225496, 0, 631959902239, 450728300227, 515126992874, 0, 137760279295, 748301940085, 609960421212, 0, 0, 748301940086, 1518022121617, 1282008050738, 53351822857, 34378591088, 698568688945, 827173216796, 515126992874, 0, 137760279295, 748301940085, 0, 0, 798378064725, 1159768101884, 492180793363, 667587308522, 53351822857, 0, 457056897559, 522396578403, 34378591088, 0, 763664612251, 215788863711]) (branchResiduals115 25 0) 8671199
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck115_25_1 :
    integerResidualCheck 115 25 1 (dualNumerators115 25 1) ∧
    integerMassCheck 115 25 1 (dualNumerators115 25 1) := by
  apply integerChecks_of_simple 115 25 1 (dualNumerators115 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 415529968297, 599898615461, 0, 0]) (branchResiduals115 25 1) 8671199
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck115_26_0 :
    integerResidualCheck 115 26 0 (dualNumerators115 26 0) ∧
    integerMassCheck 115 26 0 (dualNumerators115 26 0) := by
  apply integerChecks_of_simple 115 26 0 (dualNumerators115 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0]) (branchResiduals115 26 0) 15099566
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck115_26_1 :
    integerResidualCheck 115 26 1 (dualNumerators115 26 1) ∧
    integerMassCheck 115 26 1 (dualNumerators115 26 1) := by
  apply integerChecks_of_simple 115 26 1 (dualNumerators115 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 1025837005087, 204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals115 26 1) 15099566
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck115_27_0 :
    integerResidualCheck 115 27 0 (dualNumerators115 27 0) ∧
    integerMassCheck 115 27 0 (dualNumerators115 27 0) := by
  apply integerChecks_of_simple 115 27 0 (dualNumerators115 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 286173900105, 455299762271, 595678484088, 168320989550]) (branchResiduals115 27 0) 7338775
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck115_27_1 :
    integerResidualCheck 115 27 1 (dualNumerators115 27 1) ∧
    integerMassCheck 115 27 1 (dualNumerators115 27 1) := by
  apply integerChecks_of_simple 115 27 1 (dualNumerators115 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 963066529984, 568871411225, 0, 377837583379, 916671368281, 377088943834, 621055226706, 24161639382, 413046270426, 116714568052]) (branchResiduals115 27 1) 7338775
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck115_28_0 :
    integerResidualCheck 115 28 0 (dualNumerators115 28 0) ∧
    integerMassCheck 115 28 0 (dualNumerators115 28 0) := by
  apply integerChecks_of_simple 115 28 0 (dualNumerators115 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 450383711774, 395438493575, 503065535987, 142151330101]) (branchResiduals115 28 0) 10335557
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck115_28_1 :
    integerResidualCheck 115 28 1 (dualNumerators115 28 1) ∧
    integerMassCheck 115 28 1 (dualNumerators115 28 1) := by
  apply integerChecks_of_simple 115 28 1 (dualNumerators115 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 484442151291, 449974794159, 2156352207, 100492021777, 456143077212, 332995651238, 0, 0, 112213633330, 31708229033]) (branchResiduals115 28 1) 10335557
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck115_29_0 :
    integerResidualCheck 115 29 0 (dualNumerators115 29 0) ∧
    integerMassCheck 115 29 0 (dualNumerators115 29 0) := by
  apply integerChecks_of_simple 115 29 0 (dualNumerators115 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0]) (branchResiduals115 29 0) 40352153
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck115_29_1 :
    integerResidualCheck 115 29 1 (dualNumerators115 29 1) ∧
    integerMassCheck 115 29 1 (dualNumerators115 29 1) := by
  apply integerChecks_of_simple 115 29 1 (dualNumerators115 29 1)
    (![814189538844, 149890000629, 814189538844, 0, 1, 31000670773, 36707806937, 0, 1141563866996, 814189538843, 31000670773, 0, 248848315523, 1351722559260, 36707806937, 0, 0, 1351722559261, 2742134741776, 2315802098733, 1261885083355, 48046900821, 1261885083355, 1494194572624, 31000670773, 0, 248848315523, 1351722559260, 0, 0, 48046900821, 2094989499358, 1832718917411, 262270581947, 72165251132, 1189719832223, 1769271584479, 0, 0, 48046900821, 1379473483620, 389798100860]) (branchResiduals115 29 1) 40352153
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck115_30_0 :
    integerResidualCheck 115 30 0 (dualNumerators115 30 0) ∧
    integerMassCheck 115 30 0 (dualNumerators115 30 0) := by
  apply integerChecks_of_simple 115 30 0 (dualNumerators115 30 0)
    (![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 115599349926, 0, 37915592376, 205954223378, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 0, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 279240883212, 39960666226, 10995405936, 181270795848, 269573776534, 0, 163293901896, 15869656905, 269573776534, 0]) (branchResiduals115 30 0) 7680628
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck115_30_1 :
    integerResidualCheck 115 30 1 (dualNumerators115 30 1) ∧
    integerMassCheck 115 30 1 (dualNumerators115 30 1) := by
  apply integerChecks_of_simple 115 30 1 (dualNumerators115 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 791397036221, 113252588419, 31162097647, 513739854055, 763999473637, 0, 862736028146, 65914760940, 536287180313, 227712293325]) (branchResiduals115 30 1) 7680628
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck115_31_0 :
    integerResidualCheck 115 31 0 (dualNumerators115 31 0) ∧
    integerMassCheck 115 31 0 (dualNumerators115 31 0) := by
  apply integerChecks_of_simple 115 31 0 (dualNumerators115 31 0)
    (![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1719079079316, 0, 1491143233587, 0, 2035556695381, 0, 1259308150413, 1, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079316, 0, 1491143233587, 0, 0, 0, 2664343059941, 1951759503826, 1707419806160, 244339697667, 939253060812, 1341759948741, 1648310233018, 0, 1640459045760, 1023884014182, 1648310233018, 0]) (branchResiduals115 31 0) 32891612
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck115_31_1 :
    integerResidualCheck 115 31 1 (dualNumerators115 31 1) ∧
    integerMassCheck 115 31 1 (dualNumerators115 31 1) := by
  apply integerChecks_of_simple 115 31 1 (dualNumerators115 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 741061026801, 808805463926, 725570984152, 37986262977, 845258320866, 704608169862]) (branchResiduals115 31 1) 32891612
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck115_32_0 :
    integerResidualCheck 115 32 0 (dualNumerators115 32 0) ∧
    integerMassCheck 115 32 0 (dualNumerators115 32 0) := by
  apply integerChecks_of_simple 115 32 0 (dualNumerators115 32 0)
    (![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 0, 2079538667399, 1160276651773, 0, 382837210862, 2079538667397, 979882959195, 1, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 1160276651773, 0, 0, 0, 3223007296772, 1518687763292, 1328564078378, 190123684914, 52313619645, 862444872157, 1282570201956, 0, 3029568551736, 193438745037, 0, 1282570201956]) (branchResiduals115 32 0) 67647473
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck115_32_1 :
    integerResidualCheck 115 32 1 (dualNumerators115 32 1) ∧
    integerMassCheck 115 32 1 (dualNumerators115 32 1) := by
  apply integerChecks_of_simple 115 32 1 (dualNumerators115 32 1)
    (![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1946401957496, 0, 638403098871, 3467750500273, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957496, 0, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 4701713305868, 672836992711, 185134947997, 3052143736978, 4538943572529, 0, 2749458111138, 267205060270, 4538943572529, 0]) (branchResiduals115 32 1) 67647473
    branchSparseDots115 branchIntegerCurvature115 branchDots115
    branchIntegerCurvature115_entry rfl
    (congrFun (congrFun branchResiduals115_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks115 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 115 j s (dualNumerators115 j s) ∧
    integerMassCheck 115 j s (dualNumerators115 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck115_0_0
    · exact integerCheck115_0_1
  · fin_cases s
    · exact integerCheck115_1_0
    · exact integerCheck115_1_1
  · fin_cases s
    · exact integerCheck115_2_0
    · exact integerCheck115_2_1
  · fin_cases s
    · exact integerCheck115_3_0
    · exact integerCheck115_3_1
  · fin_cases s
    · exact integerCheck115_4_0
    · exact integerCheck115_4_1
  · fin_cases s
    · exact integerCheck115_5_0
    · exact integerCheck115_5_1
  · fin_cases s
    · exact integerCheck115_6_0
    · exact integerCheck115_6_1
  · fin_cases s
    · exact integerCheck115_7_0
    · exact integerCheck115_7_1
  · fin_cases s
    · exact integerCheck115_8_0
    · exact integerCheck115_8_1
  · fin_cases s
    · exact integerCheck115_9_0
    · exact integerCheck115_9_1
  · fin_cases s
    · exact integerCheck115_10_0
    · exact integerCheck115_10_1
  · fin_cases s
    · exact integerCheck115_11_0
    · exact integerCheck115_11_1
  · fin_cases s
    · exact integerCheck115_12_0
    · exact integerCheck115_12_1
  · fin_cases s
    · exact integerCheck115_13_0
    · exact integerCheck115_13_1
  · fin_cases s
    · exact integerCheck115_14_0
    · exact integerCheck115_14_1
  · fin_cases s
    · exact integerCheck115_15_0
    · exact integerCheck115_15_1
  · fin_cases s
    · exact integerCheck115_16_0
    · exact integerCheck115_16_1
  · fin_cases s
    · exact integerCheck115_17_0
    · exact integerCheck115_17_1
  · fin_cases s
    · exact integerCheck115_18_0
    · exact integerCheck115_18_1
  · fin_cases s
    · exact integerCheck115_19_0
    · exact integerCheck115_19_1
  · fin_cases s
    · exact integerCheck115_20_0
    · exact integerCheck115_20_1
  · fin_cases s
    · exact integerCheck115_21_0
    · exact integerCheck115_21_1
  · fin_cases s
    · exact integerCheck115_22_0
    · exact integerCheck115_22_1
  · fin_cases s
    · exact integerCheck115_23_0
    · exact integerCheck115_23_1
  · fin_cases s
    · exact integerCheck115_24_0
    · exact integerCheck115_24_1
  · fin_cases s
    · exact integerCheck115_25_0
    · exact integerCheck115_25_1
  · fin_cases s
    · exact integerCheck115_26_0
    · exact integerCheck115_26_1
  · fin_cases s
    · exact integerCheck115_27_0
    · exact integerCheck115_27_1
  · fin_cases s
    · exact integerCheck115_28_0
    · exact integerCheck115_28_1
  · fin_cases s
    · exact integerCheck115_29_0
    · exact integerCheck115_29_1
  · fin_cases s
    · exact integerCheck115_30_0
    · exact integerCheck115_30_1
  · fin_cases s
    · exact integerCheck115_31_0
    · exact integerCheck115_31_1
  · fin_cases s
    · exact integerCheck115_32_0
    · exact integerCheck115_32_1

end ElevenSquare.Tasks.T06
