import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual107
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
import ElevenSquare.Tasks.T06.SparseColumn45
import ElevenSquare.Tasks.T06.SparseColumn53
import ElevenSquare.Tasks.T06.SparseColumn57
import ElevenSquare.Tasks.T06.SparseColumn58

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix107 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix107_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = branchIntegerMatrix107 := by
  change roundedGradients ∘ branchRows 107 = branchIntegerMatrix107
  rw [show branchRows 107 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix107]

theorem branchColumn107_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 0) i) = _
  rw [branchColumn107_0]
  exact sparseColumn00_sum n

theorem branchColumn107_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 1) i) = _
  rw [branchColumn107_1]
  exact sparseColumn01_sum n

theorem branchColumn107_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 2) i) = _
  rw [branchColumn107_2]
  exact sparseColumn02_sum n

theorem branchColumn107_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 3) i) = _
  rw [branchColumn107_3]
  exact sparseColumn03_sum n

theorem branchColumn107_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 4) i) = _
  rw [branchColumn107_4]
  exact sparseColumn04_sum n

theorem branchColumn107_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 5) i) = _
  rw [branchColumn107_5]
  exact sparseColumn05_sum n

theorem branchColumn107_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 6) i) = _
  rw [branchColumn107_6]
  exact sparseColumn06_sum n

theorem branchColumn107_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 7) i) = _
  rw [branchColumn107_7]
  exact sparseColumn07_sum n

theorem branchColumn107_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 8) i) = _
  rw [branchColumn107_8]
  exact sparseColumn08_sum n

theorem branchColumn107_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 9) i) = _
  rw [branchColumn107_9]
  exact sparseColumn09_sum n

theorem branchColumn107_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 10) i) = _
  rw [branchColumn107_10]
  exact sparseColumn10_sum n

theorem branchColumn107_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 11) i) = _
  rw [branchColumn107_11]
  exact sparseColumn11_sum n

theorem branchColumn107_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 12) i) = _
  rw [branchColumn107_12]
  exact sparseColumn35_sum n

theorem branchColumn107_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 13) i) = _
  rw [branchColumn107_13]
  exact sparseColumn36_sum n

theorem branchColumn107_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 14) i) = _
  rw [branchColumn107_14]
  exact sparseColumn41_sum n

theorem branchColumn107_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 15) i) = _
  rw [branchColumn107_15]
  exact sparseColumn38_sum n

theorem branchColumn107_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 16) i) = _
  rw [branchColumn107_16]
  exact sparseColumn39_sum n

theorem branchColumn107_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 17) i) = _
  rw [branchColumn107_17]
  exact sparseColumn17_sum n

theorem branchColumn107_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 18) i) = _
  rw [branchColumn107_18]
  exact sparseColumn18_sum n

theorem branchColumn107_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 19) i) = _
  rw [branchColumn107_19]
  exact sparseColumn19_sum n

theorem branchColumn107_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 20) = sparseColumn58 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 20) = sparseDot58 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 20) i) = _
  rw [branchColumn107_20]
  exact sparseColumn58_sum n

theorem branchColumn107_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 21) i) = _
  rw [branchColumn107_21]
  exact sparseColumn21_sum n

theorem branchColumn107_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 22) i) = _
  rw [branchColumn107_22]
  exact sparseColumn22_sum n

theorem branchColumn107_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 23) = sparseColumn53 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 23) = sparseDot53 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 23) i) = _
  rw [branchColumn107_23]
  exact sparseColumn53_sum n

theorem branchColumn107_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 24) i) = _
  rw [branchColumn107_24]
  exact sparseColumn24_sum n

theorem branchColumn107_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 25) i) = _
  rw [branchColumn107_25]
  exact sparseColumn25_sum n

theorem branchColumn107_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 26) = sparseColumn57 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 26) = sparseDot57 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 26) i) = _
  rw [branchColumn107_26]
  exact sparseColumn57_sum n

theorem branchColumn107_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 27) i) = _
  rw [branchColumn107_27]
  exact sparseColumn27_sum n

theorem branchColumn107_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 28) i) = _
  rw [branchColumn107_28]
  exact sparseColumn28_sum n

theorem branchColumn107_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 29) = sparseColumn45 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 29) = sparseDot45 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 29) i) = _
  rw [branchColumn107_29]
  exact sparseColumn45_sum n

theorem branchColumn107_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 30) i) = _
  rw [branchColumn107_30]
  exact sparseColumn30_sum n

theorem branchColumn107_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 31) i) = _
  rw [branchColumn107_31]
  exact sparseColumn31_sum n

theorem branchColumn107_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 107 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 107 i)) = _
  rw [branchIntegerMatrix107_eq]
  simp only [branchIntegerMatrix107, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot107_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 107 i) 32) i) = _
  rw [branchColumn107_32]
  exact sparseColumn32_sum n

def branchSparseDots107 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot58, sparseDot21, sparseDot22, sparseDot53, sparseDot24, sparseDot25, sparseDot57, sparseDot27, sparseDot28, sparseDot45, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot107_0 :
    branchSparseDots107 0 = sparseDot00 := rfl

private theorem branchSparseDot107_1 :
    branchSparseDots107 1 = sparseDot01 := rfl

private theorem branchSparseDot107_2 :
    branchSparseDots107 2 = sparseDot02 := rfl

private theorem branchSparseDot107_3 :
    branchSparseDots107 3 = sparseDot03 := rfl

private theorem branchSparseDot107_4 :
    branchSparseDots107 4 = sparseDot04 := rfl

private theorem branchSparseDot107_5 :
    branchSparseDots107 5 = sparseDot05 := rfl

private theorem branchSparseDot107_6 :
    branchSparseDots107 6 = sparseDot06 := rfl

private theorem branchSparseDot107_7 :
    branchSparseDots107 7 = sparseDot07 := rfl

private theorem branchSparseDot107_8 :
    branchSparseDots107 8 = sparseDot08 := rfl

private theorem branchSparseDot107_9 :
    branchSparseDots107 9 = sparseDot09 := rfl

private theorem branchSparseDot107_10 :
    branchSparseDots107 10 = sparseDot10 := rfl

private theorem branchSparseDot107_11 :
    branchSparseDots107 11 = sparseDot11 := rfl

private theorem branchSparseDot107_12 :
    branchSparseDots107 12 = sparseDot35 := rfl

private theorem branchSparseDot107_13 :
    branchSparseDots107 13 = sparseDot36 := rfl

private theorem branchSparseDot107_14 :
    branchSparseDots107 14 = sparseDot41 := rfl

private theorem branchSparseDot107_15 :
    branchSparseDots107 15 = sparseDot38 := rfl

private theorem branchSparseDot107_16 :
    branchSparseDots107 16 = sparseDot39 := rfl

private theorem branchSparseDot107_17 :
    branchSparseDots107 17 = sparseDot17 := rfl

private theorem branchSparseDot107_18 :
    branchSparseDots107 18 = sparseDot18 := rfl

private theorem branchSparseDot107_19 :
    branchSparseDots107 19 = sparseDot19 := rfl

private theorem branchSparseDot107_20 :
    branchSparseDots107 20 = sparseDot58 := rfl

private theorem branchSparseDot107_21 :
    branchSparseDots107 21 = sparseDot21 := rfl

private theorem branchSparseDot107_22 :
    branchSparseDots107 22 = sparseDot22 := rfl

private theorem branchSparseDot107_23 :
    branchSparseDots107 23 = sparseDot53 := rfl

private theorem branchSparseDot107_24 :
    branchSparseDots107 24 = sparseDot24 := rfl

private theorem branchSparseDot107_25 :
    branchSparseDots107 25 = sparseDot25 := rfl

private theorem branchSparseDot107_26 :
    branchSparseDots107 26 = sparseDot57 := rfl

private theorem branchSparseDot107_27 :
    branchSparseDots107 27 = sparseDot27 := rfl

private theorem branchSparseDot107_28 :
    branchSparseDots107 28 = sparseDot28 := rfl

private theorem branchSparseDot107_29 :
    branchSparseDots107 29 = sparseDot45 := rfl

private theorem branchSparseDot107_30 :
    branchSparseDots107 30 = sparseDot30 := rfl

private theorem branchSparseDot107_31 :
    branchSparseDots107 31 = sparseDot31 := rfl

private theorem branchSparseDot107_32 :
    branchSparseDots107 32 = sparseDot32 := rfl

theorem branchDots107 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 107 i) k) = branchSparseDots107 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot107_0 n
      _ = _ := congrFun branchSparseDot107_0.symm n
  · calc
      _ = sparseDot01 n := branchDot107_1 n
      _ = _ := congrFun branchSparseDot107_1.symm n
  · calc
      _ = sparseDot02 n := branchDot107_2 n
      _ = _ := congrFun branchSparseDot107_2.symm n
  · calc
      _ = sparseDot03 n := branchDot107_3 n
      _ = _ := congrFun branchSparseDot107_3.symm n
  · calc
      _ = sparseDot04 n := branchDot107_4 n
      _ = _ := congrFun branchSparseDot107_4.symm n
  · calc
      _ = sparseDot05 n := branchDot107_5 n
      _ = _ := congrFun branchSparseDot107_5.symm n
  · calc
      _ = sparseDot06 n := branchDot107_6 n
      _ = _ := congrFun branchSparseDot107_6.symm n
  · calc
      _ = sparseDot07 n := branchDot107_7 n
      _ = _ := congrFun branchSparseDot107_7.symm n
  · calc
      _ = sparseDot08 n := branchDot107_8 n
      _ = _ := congrFun branchSparseDot107_8.symm n
  · calc
      _ = sparseDot09 n := branchDot107_9 n
      _ = _ := congrFun branchSparseDot107_9.symm n
  · calc
      _ = sparseDot10 n := branchDot107_10 n
      _ = _ := congrFun branchSparseDot107_10.symm n
  · calc
      _ = sparseDot11 n := branchDot107_11 n
      _ = _ := congrFun branchSparseDot107_11.symm n
  · calc
      _ = sparseDot35 n := branchDot107_12 n
      _ = _ := congrFun branchSparseDot107_12.symm n
  · calc
      _ = sparseDot36 n := branchDot107_13 n
      _ = _ := congrFun branchSparseDot107_13.symm n
  · calc
      _ = sparseDot41 n := branchDot107_14 n
      _ = _ := congrFun branchSparseDot107_14.symm n
  · calc
      _ = sparseDot38 n := branchDot107_15 n
      _ = _ := congrFun branchSparseDot107_15.symm n
  · calc
      _ = sparseDot39 n := branchDot107_16 n
      _ = _ := congrFun branchSparseDot107_16.symm n
  · calc
      _ = sparseDot17 n := branchDot107_17 n
      _ = _ := congrFun branchSparseDot107_17.symm n
  · calc
      _ = sparseDot18 n := branchDot107_18 n
      _ = _ := congrFun branchSparseDot107_18.symm n
  · calc
      _ = sparseDot19 n := branchDot107_19 n
      _ = _ := congrFun branchSparseDot107_19.symm n
  · calc
      _ = sparseDot58 n := branchDot107_20 n
      _ = _ := congrFun branchSparseDot107_20.symm n
  · calc
      _ = sparseDot21 n := branchDot107_21 n
      _ = _ := congrFun branchSparseDot107_21.symm n
  · calc
      _ = sparseDot22 n := branchDot107_22 n
      _ = _ := congrFun branchSparseDot107_22.symm n
  · calc
      _ = sparseDot53 n := branchDot107_23 n
      _ = _ := congrFun branchSparseDot107_23.symm n
  · calc
      _ = sparseDot24 n := branchDot107_24 n
      _ = _ := congrFun branchSparseDot107_24.symm n
  · calc
      _ = sparseDot25 n := branchDot107_25 n
      _ = _ := congrFun branchSparseDot107_25.symm n
  · calc
      _ = sparseDot57 n := branchDot107_26 n
      _ = _ := congrFun branchSparseDot107_26.symm n
  · calc
      _ = sparseDot27 n := branchDot107_27 n
      _ = _ := congrFun branchSparseDot107_27.symm n
  · calc
      _ = sparseDot28 n := branchDot107_28 n
      _ = _ := congrFun branchSparseDot107_28.symm n
  · calc
      _ = sparseDot45 n := branchDot107_29 n
      _ = _ := congrFun branchSparseDot107_29.symm n
  · calc
      _ = sparseDot30 n := branchDot107_30 n
      _ = _ := congrFun branchSparseDot107_30.symm n
  · calc
      _ = sparseDot31 n := branchDot107_31 n
      _ = _ := congrFun branchSparseDot107_31.symm n
  · calc
      _ = sparseDot32 n := branchDot107_32 n
      _ = _ := congrFun branchSparseDot107_32.symm n

def branchIntegerCurvature107 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101955390, 101955390, 79086693, 79086693, 115699695, 115699695, 88123140, 88123140, 204734428, 204734428]

theorem branchIntegerCurvature107_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 107 i)) = branchIntegerCurvature107 := by
  change curvatureNumerators ∘ branchRows 107 = branchIntegerCurvature107
  rw [show branchRows 107 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 36, 37, 48, 49, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature107_entry (i : Fin 42) :
    curvatureNumerators (branchRows 107 i) = branchIntegerCurvature107 i :=
  congrFun branchIntegerCurvature107_eq i

def branchResiduals107 : Fin 33 → Fin 2 → ℕ := ![![1298735016087098, 33000000000000], ![1546553850602052, 33000000000000], ![1581981138251036, 1336126080448118], ![33000000000000, 1024756374489120], ![855342269530085, 33000000000000], ![1055416670995617, 895937802994960], ![721495409792647, 624798065222648], ![33000000000000, 763274544708426], ![1577995001510790, 1126932082865210], ![1026237106734739, 33000000000000], ![33000000000000, 777652167735970], ![505818575141711, 465692607595900], ![990835419300237, 66000000000000], ![33000000000000, 857768286373165], ![1055376933199217, 484221612920125], ![471170285733672, 33000000000000], ![66000000000000, 744141164530545], ![659538719672133, 464860785005858], ![619769708087911, 254068241852025], ![628662340371737, 509026320746573], ![1320409717612494, 854809793236492], ![751125873877165, 374930863842880], ![470345765638443, 91702120449581], ![1320409717612494, 854809793236492], ![667751412752385, 230277296677688], ![508406837852209, 218713669397988], ![398805840068707, 854809793236492], ![409060239811991, 545925696460108], ![285044621435502, 301267805415724], ![398805840068707, 854809793236492], ![215049553328539, 550954788710644], ![1680772096123362, 648440653830429], ![1329675004376849, 2883366277765113]]

theorem branchResiduals107_eq : residualNumerators 107 = branchResiduals107 := rfl

theorem integerCheck107_0_0 :
    integerResidualCheck 107 0 0 (dualNumerators107 0 0) ∧
    integerMassCheck 107 0 0 (dualNumerators107 0 0) := by
  apply integerChecks_of_simple 107 0 0 (dualNumerators107 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 666956468696, 1506089855371, 1308901425339, 0, 383156207414, 1452036338471, 1330333654477, 636679939507, 1430871029972, 404321515913]) (branchResiduals107 0 0) 18767167
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck107_0_1 :
    integerResidualCheck 107 0 1 (dualNumerators107 0 1) ∧
    integerMassCheck 107 0 1 (dualNumerators107 0 1) := by
  apply integerChecks_of_simple 107 0 1 (dualNumerators107 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals107 0 1) 18767167
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck107_1_0 :
    integerResidualCheck 107 1 0 (dualNumerators107 1 0) ∧
    integerMassCheck 107 1 0 (dualNumerators107 1 0) := by
  apply integerChecks_of_simple 107 1 0 (dualNumerators107 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 789741275848, 1783356755272, 1549866490727, 0, 453694185894, 1719352138174, 1575244332878, 753890922920, 1694290356000, 478755968067]) (branchResiduals107 1 0) 22176635
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck107_1_1 :
    integerResidualCheck 107 1 1 (dualNumerators107 1 1) ∧
    integerMassCheck 107 1 1 (dualNumerators107 1 1) := by
  apply integerChecks_of_simple 107 1 1 (dualNumerators107 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals107 1 1) 22176635
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck107_2_0 :
    integerResidualCheck 107 2 0 (dualNumerators107 2 0) ∧
    integerMassCheck 107 2 0 (dualNumerators107 2 0) := by
  apply integerChecks_of_simple 107 2 0 (dualNumerators107 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 789741275848, 1783356755274, 1549866490728, 0, 453694185894, 1719352138175, 1575244332879, 753890922921, 1694290356001, 478755968068]) (branchResiduals107 2 0) 22681452
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck107_2_1 :
    integerResidualCheck 107 2 1 (dualNumerators107 2 1) ∧
    integerMassCheck 107 2 1 (dualNumerators107 2 1) := by
  apply integerChecks_of_simple 107 2 1 (dualNumerators107 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 666956468696, 1506089855370, 1308901425338, 0, 383156207413, 1452036338470, 1330333654476, 636679939507, 1430871029971, 404321515912]) (branchResiduals107 2 1) 22681452
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck107_3_0 :
    integerResidualCheck 107 3 0 (dualNumerators107 3 0) ∧
    integerMassCheck 107 3 0 (dualNumerators107 3 0) := by
  apply integerChecks_of_simple 107 3 0 (dualNumerators107 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals107 3 0) 16360330
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck107_3_1 :
    integerResidualCheck 107 3 1 (dualNumerators107 3 1) ∧
    integerMassCheck 107 3 1 (dualNumerators107 3 1) := by
  apply integerChecks_of_simple 107 3 1 (dualNumerators107 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000001, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000001, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 525514152402, 1186691442298, 1031321016287, 0, 301899777613, 1144101124262, 1048208085022, 501658405706, 1127424369963, 318576531911]) (branchResiduals107 3 1) 16360330
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck107_4_0 :
    integerResidualCheck 107 4 0 (dualNumerators107 4 0) ∧
    integerMassCheck 107 4 0 (dualNumerators107 4 0) := by
  apply integerChecks_of_simple 107 4 0 (dualNumerators107 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 443809984428, 1002190917446, 870976665588, 0, 254961992914, 966222317366, 885238221966, 423663203373, 952138376845, 269045933435]) (branchResiduals107 4 0) 13760362
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck107_4_1 :
    integerResidualCheck 107 4 1 (dualNumerators107 4 1) ∧
    integerMassCheck 107 4 1 (dualNumerators107 4 1) := by
  apply integerChecks_of_simple 107 4 1 (dualNumerators107 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals107 4 1) 13760362
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck107_5_0 :
    integerResidualCheck 107 5 0 (dualNumerators107 5 0) ∧
    integerMassCheck 107 5 0 (dualNumerators107 5 0) := by
  apply integerChecks_of_simple 107 5 0 (dualNumerators107 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 525514152403, 1186691442299, 1031321016288, 0, 301899777613, 1144101124263, 1048208085022, 501658405707, 1127424369964, 318576531911]) (branchResiduals107 5 0) 17641130
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck107_5_1 :
    integerResidualCheck 107 5 1 (dualNumerators107 5 1) ∧
    integerMassCheck 107 5 1 (dualNumerators107 5 1) := by
  apply integerChecks_of_simple 107 5 1 (dualNumerators107 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 443809984428, 1002190917446, 870976665588, 0, 254961992914, 966222317365, 885238221966, 423663203373, 952138376844, 269045933435]) (branchResiduals107 5 1) 17641130
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck107_6_0 :
    integerResidualCheck 107 6 0 (dualNumerators107 6 0) ∧
    integerMassCheck 107 6 0 (dualNumerators107 6 0) := by
  apply integerChecks_of_simple 107 6 0 (dualNumerators107 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 659499318402, 1175693227483, 2719950702, 106626845062, 1430871029972, 404321515913]) (branchResiduals107 6 0) 8962451
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck107_6_1 :
    integerResidualCheck 107 6 1 (dualNumerators107 6 1) ∧
    integerMassCheck 107 6 1 (dualNumerators107 6 1) := by
  apply integerChecks_of_simple 107 6 1 (dualNumerators107 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals107 6 1) 8962451
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck107_7_0 :
    integerResidualCheck 107 7 0 (dualNumerators107 7 0) ∧
    integerMassCheck 107 7 0 (dualNumerators107 7 0) := by
  apply integerChecks_of_simple 107 7 0 (dualNumerators107 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals107 7 0) 10424794
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck107_7_1 :
    integerResidualCheck 107 7 1 (dualNumerators107 7 1) ∧
    integerMassCheck 107 7 1 (dualNumerators107 7 1) := by
  apply integerChecks_of_simple 107 7 1 (dualNumerators107 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 394870637925, 891678377638, 774933245365, 0, 226847092948, 859676069088, 787622166441, 376945461461, 847145178002, 239377984034]) (branchResiduals107 7 1) 10424794
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck107_8_0 :
    integerResidualCheck 107 8 0 (dualNumerators107 8 0) ∧
    integerMassCheck 107 8 0 (dualNumerators107 8 0) := by
  apply integerChecks_of_simple 107 8 0 (dualNumerators107 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 789741275849, 1783356755275, 1549866490730, 0, 453694185895, 1719352138176, 1575244332881, 753890922921, 1694290356003, 478755968068]) (branchResiduals107 8 0) 22681452
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck107_8_1 :
    integerResidualCheck 107 8 1 (dualNumerators107 8 1) ∧
    integerMassCheck 107 8 1 (dualNumerators107 8 1) := by
  apply integerChecks_of_simple 107 8 1 (dualNumerators107 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 563261595587, 1271930950295, 1105400337063, 0, 323585101692, 1226281389034, 1123500396284, 537692301428, 1208406751039, 341459739686]) (branchResiduals107 8 1) 22681452
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck107_9_0 :
    integerResidualCheck 107 9 0 (dualNumerators107 9 0) ∧
    integerMassCheck 107 9 0 (dualNumerators107 9 0) := by
  apply integerChecks_of_simple 107 9 0 (dualNumerators107 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 525514152402, 1186691442298, 1031321016287, 0, 301899777613, 1144101124262, 1048208085022, 501658405706, 1127424369963, 318576531911]) (branchResiduals107 9 0) 16350530
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck107_9_1 :
    integerResidualCheck 107 9 1 (dualNumerators107 9 1) ∧
    integerMassCheck 107 9 1 (dualNumerators107 9 1) := by
  apply integerChecks_of_simple 107 9 1 (dualNumerators107 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals107 9 1) 16350530
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck107_10_0 :
    integerResidualCheck 107 10 0 (dualNumerators107 10 0) ∧
    integerMassCheck 107 10 0 (dualNumerators107 10 0) := by
  apply integerChecks_of_simple 107 10 0 (dualNumerators107 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals107 10 0) 10683139
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck107_10_1 :
    integerResidualCheck 107 10 1 (dualNumerators107 10 1) ∧
    integerMassCheck 107 10 1 (dualNumerators107 10 1) := by
  apply integerChecks_of_simple 107 10 1 (dualNumerators107 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 401731091900, 907170333440, 788396879662, 0, 230788317974, 874612019090, 801306257136, 383494484713, 861863417206, 243536919859]) (branchResiduals107 10 1) 10683139
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck107_11_0 :
    integerResidualCheck 107 11 0 (dualNumerators107 11 0) ∧
    integerMassCheck 107 11 0 (dualNumerators107 11 0) := by
  apply integerChecks_of_simple 107 11 0 (dualNumerators107 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 249680802227, 563817491793, 489998333105, 0, 143437771032, 543582099985, 498021669583, 238346527126, 535658687508, 151361183509]) (branchResiduals107 11 0) 15120968
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck107_11_1 :
    integerResidualCheck 107 11 1 (dualNumerators107 11 1) ∧
    integerMassCheck 107 11 1 (dualNumerators107 11 1) := by
  apply integerChecks_of_simple 107 11 1 (dualNumerators107 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 227680190921, 514136741916, 446822154676, 0, 130798759066, 495684390638, 454138515265, 217344634900, 488459149252, 138024000452]) (branchResiduals107 11 1) 15120968
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck107_12_0 :
    integerResidualCheck 107 12 0 (dualNumerators107 12 0) ∧
    integerMassCheck 107 12 0 (dualNumerators107 12 0) := by
  apply integerChecks_of_simple 107 12 0 (dualNumerators107 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 525514152402, 1186691442298, 1031321016287, 0, 301899777613, 1144101124262, 1048208085022, 501658405706, 1127424369963, 318576531911]) (branchResiduals107 12 0) 16348076
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck107_12_1 :
    integerResidualCheck 107 12 1 (dualNumerators107 12 1) ∧
    integerMassCheck 107 12 1 (dualNumerators107 12 1) := by
  apply integerChecks_of_simple 107 12 1 (dualNumerators107 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals107 12 1) 16348076
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck107_13_0 :
    integerResidualCheck 107 13 0 (dualNumerators107 13 0) ∧
    integerMassCheck 107 13 0 (dualNumerators107 13 0) := by
  apply integerChecks_of_simple 107 13 0 (dualNumerators107 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals107 13 0) 13962901
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck107_13_1 :
    integerResidualCheck 107 13 1 (dualNumerators107 13 1) ∧
    integerMassCheck 107 13 1 (dualNumerators107 13 1) := by
  apply integerChecks_of_simple 107 13 1 (dualNumerators107 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 443809984428, 1002190917446, 870976665588, 0, 254961992914, 966222317366, 885238221966, 423663203373, 952138376845, 269045933435]) (branchResiduals107 13 1) 13962901
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck107_14_0 :
    integerResidualCheck 107 14 0 (dualNumerators107 14 0) ∧
    integerMassCheck 107 14 0 (dualNumerators107 14 0) := by
  apply integerChecks_of_simple 107 14 0 (dualNumerators107 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 525514152403, 1186691442299, 1031321016288, 0, 301899777613, 1144101124263, 1048208085022, 501658405707, 1127424369964, 318576531911]) (branchResiduals107 14 0) 20161291
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck107_14_1 :
    integerResidualCheck 107 14 1 (dualNumerators107 14 1) ∧
    integerMassCheck 107 14 1 (dualNumerators107 14 1) := by
  apply integerChecks_of_simple 107 14 1 (dualNumerators107 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 240609326574, 543332710407, 472195570901, 0, 138226348143, 523832516750, 479927401181, 229686851658, 516196980004, 145861884889]) (branchResiduals107 14 1) 20161291
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck107_15_0 :
    integerResidualCheck 107 15 0 (dualNumerators107 15 0) ∧
    integerMassCheck 107 15 0 (dualNumerators107 15 0) := by
  apply integerChecks_of_simple 107 15 0 (dualNumerators107 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 249680802227, 563817491792, 489998333105, 0, 143437771032, 543582099985, 498021669583, 238346527126, 535658687508, 151361183509]) (branchResiduals107 15 0) 12900283
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck107_15_1 :
    integerResidualCheck 107 15 1 (dualNumerators107 15 1) ∧
    integerMassCheck 107 15 1 (dualNumerators107 15 1) := by
  apply integerChecks_of_simple 107 15 1 (dualNumerators107 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals107 15 1) 12900283
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck107_16_0 :
    integerResidualCheck 107 16 0 (dualNumerators107 16 0) ∧
    integerMassCheck 107 16 0 (dualNumerators107 16 0) := by
  apply integerChecks_of_simple 107 16 0 (dualNumerators107 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals107 16 0) 10683060
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck107_16_1 :
    integerResidualCheck 107 16 1 (dualNumerators107 16 1) ∧
    integerMassCheck 107 16 1 (dualNumerators107 16 1) := by
  apply integerChecks_of_simple 107 16 1 (dualNumerators107 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 401731091900, 907170333440, 788396879662, 0, 230788317974, 874612019090, 801306257136, 383494484713, 861863417206, 243536919859]) (branchResiduals107 16 1) 10683060
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck107_17_0 :
    integerResidualCheck 107 17 0 (dualNumerators107 17 0) ∧
    integerMassCheck 107 17 0 (dualNumerators107 17 0) := by
  apply integerChecks_of_simple 107 17 0 (dualNumerators107 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 327475395459, 739489598098, 642670147151, 0, 188129565324, 712949339995, 653193364245, 312609630099, 702557180842, 198521724476]) (branchResiduals107 17 0) 15120968
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck107_17_1 :
    integerResidualCheck 107 17 1 (dualNumerators107 17 1) ∧
    integerMassCheck 107 17 1 (dualNumerators107 17 1) := by
  apply integerChecks_of_simple 107 17 1 (dualNumerators107 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 227680190921, 514136741916, 446822154676, 0, 130798759066, 495684390637, 454138515265, 217344634900, 488459149252, 138024000452]) (branchResiduals107 17 1) 15120968
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck107_18_0 :
    integerResidualCheck 107 18 0 (dualNumerators107 18 0) ∧
    integerMassCheck 107 18 0 (dualNumerators107 18 0) := by
  apply integerChecks_of_simple 107 18 0 (dualNumerators107 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 301875224851, 966521474577, 763999473637, 0, 136222375797, 934970696451, 772489965679, 214059593984, 835192545885, 236000526363]) (branchResiduals107 18 0) 13565580
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck107_18_1 :
    integerResidualCheck 107 18 1 (dualNumerators107 18 1) ∧
    integerMassCheck 107 18 1 (dualNumerators107 18 1) := by
  apply integerChecks_of_simple 107 18 1 (dualNumerators107 18 1)
    (![543792441172, 100110656623, 543792441172, 0, 1, 180671424657, 213932525007, 0, 71292007252, 50847095100, 180671424657, 0, 92181412018, 500721469249, 213932525007, 0, 0, 500721469249, 171249542446, 144624567043, 842805682483, 280016586907, 78806208846, 93314209907, 180671424657, 0, 92181412018, 500721469249, 0, 0, 280016586907, 776051426377, 127580111437, 3254448853, 78806208846, 0, 110493093096, 0, 84115995539, 195900591369, 86149742858, 24343350238]) (branchResiduals107 18 1) 13565580
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck107_19_0 :
    integerResidualCheck 107 19 0 (dualNumerators107 19 0) ∧
    integerMassCheck 107 19 0 (dualNumerators107 19 0) := by
  apply integerChecks_of_simple 107 19 0 (dualNumerators107 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 168672709502, 902520362746, 645216866088, 0, 28774691489, 875874933151, 648421029826, 25293932239, 705341215054, 199308409586]) (branchResiduals107 19 0) 8248658
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck107_19_1 :
    integerResidualCheck 107 19 1 (dualNumerators107 19 1) ∧
    integerMassCheck 107 19 1 (dualNumerators107 19 1) := by
  apply integerChecks_of_simple 107 19 1 (dualNumerators107 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 394588886086, 369410587551, 460183470977, 0, 294810410203, 350406455885, 475079366460, 512398369190, 503065535987, 142151330101]) (branchResiduals107 19 1) 8248658
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck107_20_0 :
    integerResidualCheck 107 20 0 (dualNumerators107 20 0) ∧
    integerMassCheck 107 20 0 (dualNumerators107 20 0) := by
  apply integerChecks_of_simple 107 20 0 (dualNumerators107 20 0)
    (![581614421966, 107073576748, 581614421967, 0, 2, 2066609823263, 2447066870339, 0, 815473519327, 581614421966, 2066609823265, 0, 177764221088, 965599897143, 2447066870339, 0, 0, 965599897144, 1958837637556, 1654287895857, 901424703129, 3202969314485, 901424703129, 1067374451772, 2066609823265, 0, 177764221088, 965599897143, 0, 0, 3202969314485, 1496550924032, 1459324915655, 37226008378, 901424703129, 0, 1263875081678, 0, 962160690349, 2240808624136, 985423706048, 278451375631]) (branchResiduals107 20 0) 35312013
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck107_20_1 :
    integerResidualCheck 107 20 1 (dualNumerators107 20 1) ∧
    integerMassCheck 107 20 1 (dualNumerators107 20 1) := by
  apply integerChecks_of_simple 107 20 1 (dualNumerators107 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 25837005087, 1204076434982, 564110399358, 1160334187225, 0, 0, 1344522571906, 379922014678]) (branchResiduals107 20 1) 35312013
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck107_21_0 :
    integerResidualCheck 107 21 0 (dualNumerators107 21 0) ∧
    integerMassCheck 107 21 0 (dualNumerators107 21 0) := by
  apply integerChecks_of_simple 107 21 0 (dualNumerators107 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 604293255477, 704608169863, 757887471419, 892563449519, 1020530044549, 288371380791]) (branchResiduals107 21 0) 11182451
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck107_21_1 :
    integerResidualCheck 107 21 1 (dualNumerators107 21 1) ∧
    integerMassCheck 107 21 1 (dualNumerators107 21 1) := by
  apply integerChecks_of_simple 107 21 1 (dualNumerators107 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 917967404853, 905358228364, 3460174706, 161253783489, 75547476522, 155395681176, 0, 0, 180062781238, 50880376460]) (branchResiduals107 21 1) 11182451
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck107_22_0 :
    integerResidualCheck 107 22 0 (dualNumerators107 22 0) ∧
    integerMassCheck 107 22 0 (dualNumerators107 22 0) := by
  apply integerChecks_of_simple 107 22 0 (dualNumerators107 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 685604038196, 78395435442, 9067941093, 451115529884, 645216866088, 0, 19333649461, 782002431258, 503065535987, 142151330101]) (branchResiduals107 22 0) 6465674
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck107_22_1 :
    integerResidualCheck 107 22 1 (dualNumerators107 22 1) ∧
    integerMassCheck 107 22 1 (dualNumerators107 22 1) := by
  apply integerChecks_of_simple 107 22 1 (dualNumerators107 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 108732662288, 12539033463, 1534493418, 71511669319, 33503252091, 68913760194, 0, 0, 79852948501, 22564063785]) (branchResiduals107 22 1) 6465674
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck107_23_0 :
    integerResidualCheck 107 23 0 (dualNumerators107 23 0) ∧
    integerMassCheck 107 23 0 (dualNumerators107 23 0) := by
  apply integerChecks_of_simple 107 23 0 (dualNumerators107 23 0)
    (![581614421966, 107073576748, 581614421967, 0, 2, 2066609823263, 2447066870339, 0, 815473519327, 581614421966, 2066609823265, 0, 177764221088, 965599897143, 2447066870339, 0, 0, 965599897144, 1958837637556, 1654287895857, 901424703129, 3202969314485, 901424703129, 1067374451772, 2066609823265, 0, 177764221088, 965599897143, 0, 0, 3202969314485, 1496550924032, 459324915655, 1037226008378, 901424703129, 0, 1263875081678, 0, 962160690349, 2240808624136, 985423706048, 278451375631]) (branchResiduals107 23 0) 35297932
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck107_23_1 :
    integerResidualCheck 107 23 1 (dualNumerators107 23 1) ∧
    integerMassCheck 107 23 1 (dualNumerators107 23 1) := by
  apply integerChecks_of_simple 107 23 1 (dualNumerators107 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1830784228945, 211125748477, 25837005087, 1204076434982, 564110399358, 1160334187225, 0, 0, 1344522571906, 379922014678]) (branchResiduals107 23 1) 35297932
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck107_24_0 :
    integerResidualCheck 107 24 0 (dualNumerators107 24 0) ∧
    integerMassCheck 107 24 0 (dualNumerators107 24 0) := by
  apply integerChecks_of_simple 107 24 0 (dualNumerators107 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 384946583730, 686246488518, 705016048726, 601815130180, 835192545885, 236000526363]) (branchResiduals107 24 0) 9356857
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck107_24_1 :
    integerResidualCheck 107 24 1 (dualNumerators107 24 1) ∧
    integerMassCheck 107 24 1 (dualNumerators107 24 1) := by
  apply integerChecks_of_simple 107 24 1 (dualNumerators107 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 690777049383, 178822020994, 48434165160, 99625565721, 0, 0, 115439864933, 32619865948]) (branchResiduals107 24 1) 9356857
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck107_25_0 :
    integerResidualCheck 107 25 0 (dualNumerators107 25 0) ∧
    integerMassCheck 107 25 0 (dualNumerators107 25 0) := by
  apply integerChecks_of_simple 107 25 0 (dualNumerators107 25 0)
    (![34966365041, 6437209308, 34966365041, 0, 1, 22997469043, 27231238312, 0, 632721051475, 451271169324, 515942815115, 0, 137926201422, 749203214751, 610926434029, 0, 0, 749203214752, 1519850467647, 1283552135172, 54193197479, 35643006641, 699410063567, 828169486116, 515942815115, 0, 137926201422, 749203214751, 0, 0, 799642480277, 1161164957288, 492609519496, 668555437793, 54193197479, 0, 340961156265, 639671999393, 0, 35643006641, 764584390126, 216048765531]) (branchResiduals107 25 0) 8671199
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck107_25_1 :
    integerResidualCheck 107 25 1 (dualNumerators107 25 1) ∧
    integerMassCheck 107 25 1 (dualNumerators107 25 1) := by
  apply integerChecks_of_simple 107 25 1 (dualNumerators107 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals107 25 1) 8671199
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck107_26_0 :
    integerResidualCheck 107 26 0 (dualNumerators107 26 0) ∧
    integerMassCheck 107 26 0 (dualNumerators107 26 0) := by
  apply integerChecks_of_simple 107 26 0 (dualNumerators107 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals107 26 0) 15099566
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck107_26_1 :
    integerResidualCheck 107 26 1 (dualNumerators107 26 1) ∧
    integerMassCheck 107 26 1 (dualNumerators107 26 1) := by
  apply integerChecks_of_simple 107 26 1 (dualNumerators107 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 1025837005087, 204076434982, 564110399358, 1160334187225, 0, 0, 1344522571906, 379922014678]) (branchResiduals107 26 1) 15099566
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck107_27_0 :
    integerResidualCheck 107 27 0 (dualNumerators107 27 0) ∧
    integerMassCheck 107 27 0 (dualNumerators107 27 0) := by
  apply integerChecks_of_simple 107 27 0 (dualNumerators107 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 436855949686, 304617712691, 595678484088, 168320989550]) (branchResiduals107 27 0) 7338775
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck107_27_1 :
    integerResidualCheck 107 27 1 (dualNumerators107 27 1) ∧
    integerMassCheck 107 27 1 (dualNumerators107 27 1) := by
  apply integerChecks_of_simple 107 27 1 (dualNumerators107 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 585228946605, 946708994604, 377837583379, 0, 385157561486, 908602750628, 385949753226, 259267112862, 413046270426, 116714568052]) (branchResiduals107 27 1) 7338775
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck107_28_0 :
    integerResidualCheck 107 28 0 (dualNumerators107 28 0) ∧
    integerMassCheck 107 28 0 (dualNumerators107 28 0) := by
  apply integerChecks_of_simple 107 28 0 (dualNumerators107 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 374399059503, 471423145846, 503065535987, 142151330101]) (branchResiduals107 28 0) 10335557
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck107_28_1 :
    integerResidualCheck 107 28 1 (dualNumerators107 28 1) ∧
    integerMassCheck 107 28 1 (dualNumerators107 28 1) := by
  apply integerChecks_of_simple 107 28 1 (dualNumerators107 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 484442151291, 449974794159, 2156352207, 100492021777, 362407121329, 426731607121, 0, 0, 112213633330, 31708229033]) (branchResiduals107 28 1) 10335557
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck107_29_0 :
    integerResidualCheck 107 29 0 (dualNumerators107 29 0) ∧
    integerMassCheck 107 29 0 (dualNumerators107 29 0) := by
  apply integerChecks_of_simple 107 29 0 (dualNumerators107 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals107 29 0) 40352153
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck107_29_1 :
    integerResidualCheck 107 29 1 (dualNumerators107 29 1) ∧
    integerMassCheck 107 29 1 (dualNumerators107 29 1) := by
  apply integerChecks_of_simple 107 29 1 (dualNumerators107 29 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1830784228945, 211125748477, 25837005087, 1204076434982, 1564110399358, 160334187225, 0, 0, 1344522571906, 379922014678]) (branchResiduals107 29 1) 40352153
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck107_30_0 :
    integerResidualCheck 107 30 0 (dualNumerators107 30 0) ∧
    integerMassCheck 107 30 0 (dualNumerators107 30 0) := by
  apply integerChecks_of_simple 107 30 0 (dualNumerators107 30 0)
    (![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 115599349926, 0, 37915592376, 205954223378, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 0, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 111490371098, 207711178340, 178745918050, 13520283734, 69802588317, 199771188218, 179163558800, 0, 269573776534, 0]) (branchResiduals107 30 0) 7680628
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck107_30_1 :
    integerResidualCheck 107 30 1 (dualNumerators107 30 1) ∧
    integerMassCheck 107 30 1 (dualNumerators107 30 1) := by
  apply integerChecks_of_simple 107 30 1 (dualNumerators107 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 277657182166, 626992442474, 544901951702, 0, 159509769938, 604489703700, 556554858415, 372095930671, 536287180313, 227712293325]) (branchResiduals107 30 1) 7680628
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck107_31_0 :
    integerResidualCheck 107 31 0 (dualNumerators107 31 0) ∧
    integerMassCheck 107 31 0 (dualNumerators107 31 0) := by
  apply integerChecks_of_simple 107 31 0 (dualNumerators107 31 0)
    (![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1719079079316, 0, 1491143233587, 0, 2035556695381, 0, 1259308150413, 1, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079316, 0, 1491143233587, 0, 0, 0, 2664343059941, 1951759503826, 1903210393687, 48549110140, 743462473284, 1537550536268, 1648310233018, 0, 761819131889, 1902523928053, 1648310233018, 0]) (branchResiduals107 31 0) 32891612
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck107_31_1 :
    integerResidualCheck 107 31 1 (dualNumerators107 31 1) ∧
    integerMassCheck 107 31 1 (dualNumerators107 31 1) := by
  apply integerChecks_of_simple 107 31 1 (dualNumerators107 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 556963843680, 992902647048, 18993131489, 744564115640, 845258320866, 704608169862]) (branchResiduals107 31 1) 32891612
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck107_32_0 :
    integerResidualCheck 107 32 0 (dualNumerators107 32 0) ∧
    integerMassCheck 107 32 0 (dualNumerators107 32 0) := by
  apply integerChecks_of_simple 107 32 0 (dualNumerators107 32 0)
    (![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 0, 2079538667399, 1160276651773, 0, 382837210862, 2079538667397, 979882959195, 1, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 1160276651773, 0, 0, 0, 3223007296772, 1518687763292, 1380877698023, 137810065270, 0, 914758491801, 1182536788648, 100033413309, 60954317499, 3162052979273, 0, 1282570201956]) (branchResiduals107 32 0) 67647473
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck107_32_1 :
    integerResidualCheck 107 32 1 (dualNumerators107 32 1) ∧
    integerMassCheck 107 32 1 (dualNumerators107 32 1) := by
  apply integerChecks_of_simple 107 32 1 (dualNumerators107 32 1)
    (![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1946401957496, 0, 638403098871, 3467750500273, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957496, 0, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 1877217101011, 3497333197567, 3009631152853, 227647532122, 1175299814610, 3363643757919, 3016663171407, 0, 4538943572529, 0]) (branchResiduals107 32 1) 67647473
    branchSparseDots107 branchIntegerCurvature107 branchDots107
    branchIntegerCurvature107_entry rfl
    (congrFun (congrFun branchResiduals107_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks107 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 107 j s (dualNumerators107 j s) ∧
    integerMassCheck 107 j s (dualNumerators107 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck107_0_0
    · exact integerCheck107_0_1
  · fin_cases s
    · exact integerCheck107_1_0
    · exact integerCheck107_1_1
  · fin_cases s
    · exact integerCheck107_2_0
    · exact integerCheck107_2_1
  · fin_cases s
    · exact integerCheck107_3_0
    · exact integerCheck107_3_1
  · fin_cases s
    · exact integerCheck107_4_0
    · exact integerCheck107_4_1
  · fin_cases s
    · exact integerCheck107_5_0
    · exact integerCheck107_5_1
  · fin_cases s
    · exact integerCheck107_6_0
    · exact integerCheck107_6_1
  · fin_cases s
    · exact integerCheck107_7_0
    · exact integerCheck107_7_1
  · fin_cases s
    · exact integerCheck107_8_0
    · exact integerCheck107_8_1
  · fin_cases s
    · exact integerCheck107_9_0
    · exact integerCheck107_9_1
  · fin_cases s
    · exact integerCheck107_10_0
    · exact integerCheck107_10_1
  · fin_cases s
    · exact integerCheck107_11_0
    · exact integerCheck107_11_1
  · fin_cases s
    · exact integerCheck107_12_0
    · exact integerCheck107_12_1
  · fin_cases s
    · exact integerCheck107_13_0
    · exact integerCheck107_13_1
  · fin_cases s
    · exact integerCheck107_14_0
    · exact integerCheck107_14_1
  · fin_cases s
    · exact integerCheck107_15_0
    · exact integerCheck107_15_1
  · fin_cases s
    · exact integerCheck107_16_0
    · exact integerCheck107_16_1
  · fin_cases s
    · exact integerCheck107_17_0
    · exact integerCheck107_17_1
  · fin_cases s
    · exact integerCheck107_18_0
    · exact integerCheck107_18_1
  · fin_cases s
    · exact integerCheck107_19_0
    · exact integerCheck107_19_1
  · fin_cases s
    · exact integerCheck107_20_0
    · exact integerCheck107_20_1
  · fin_cases s
    · exact integerCheck107_21_0
    · exact integerCheck107_21_1
  · fin_cases s
    · exact integerCheck107_22_0
    · exact integerCheck107_22_1
  · fin_cases s
    · exact integerCheck107_23_0
    · exact integerCheck107_23_1
  · fin_cases s
    · exact integerCheck107_24_0
    · exact integerCheck107_24_1
  · fin_cases s
    · exact integerCheck107_25_0
    · exact integerCheck107_25_1
  · fin_cases s
    · exact integerCheck107_26_0
    · exact integerCheck107_26_1
  · fin_cases s
    · exact integerCheck107_27_0
    · exact integerCheck107_27_1
  · fin_cases s
    · exact integerCheck107_28_0
    · exact integerCheck107_28_1
  · fin_cases s
    · exact integerCheck107_29_0
    · exact integerCheck107_29_1
  · fin_cases s
    · exact integerCheck107_30_0
    · exact integerCheck107_30_1
  · fin_cases s
    · exact integerCheck107_31_0
    · exact integerCheck107_31_1
  · fin_cases s
    · exact integerCheck107_32_0
    · exact integerCheck107_32_1

end ElevenSquare.Tasks.T06
