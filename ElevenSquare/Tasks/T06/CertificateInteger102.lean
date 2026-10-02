import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual102
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
import ElevenSquare.Tasks.T06.SparseColumn35
import ElevenSquare.Tasks.T06.SparseColumn36
import ElevenSquare.Tasks.T06.SparseColumn37
import ElevenSquare.Tasks.T06.SparseColumn38
import ElevenSquare.Tasks.T06.SparseColumn39
import ElevenSquare.Tasks.T06.SparseColumn40
import ElevenSquare.Tasks.T06.SparseColumn42
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn53
import ElevenSquare.Tasks.T06.SparseColumn56
import ElevenSquare.Tasks.T06.SparseColumn58

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix102 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral43, roundedGradientLiteral44, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix102_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = branchIntegerMatrix102 := by
  change roundedGradients ∘ branchRows 102 = branchIntegerMatrix102
  rw [show branchRows 102 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 52, 53, 54, 55, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral43_eq, roundedGradientLiteral44_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix102]

theorem branchColumn102_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 0) i) = _
  rw [branchColumn102_0]
  exact sparseColumn00_sum n

theorem branchColumn102_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 1) i) = _
  rw [branchColumn102_1]
  exact sparseColumn01_sum n

theorem branchColumn102_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 2) i) = _
  rw [branchColumn102_2]
  exact sparseColumn02_sum n

theorem branchColumn102_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 3) i) = _
  rw [branchColumn102_3]
  exact sparseColumn03_sum n

theorem branchColumn102_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 4) i) = _
  rw [branchColumn102_4]
  exact sparseColumn04_sum n

theorem branchColumn102_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 5) i) = _
  rw [branchColumn102_5]
  exact sparseColumn05_sum n

theorem branchColumn102_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 6) i) = _
  rw [branchColumn102_6]
  exact sparseColumn06_sum n

theorem branchColumn102_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 7) i) = _
  rw [branchColumn102_7]
  exact sparseColumn07_sum n

theorem branchColumn102_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 8) i) = _
  rw [branchColumn102_8]
  exact sparseColumn08_sum n

theorem branchColumn102_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 9) i) = _
  rw [branchColumn102_9]
  exact sparseColumn09_sum n

theorem branchColumn102_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 10) i) = _
  rw [branchColumn102_10]
  exact sparseColumn10_sum n

theorem branchColumn102_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 11) i) = _
  rw [branchColumn102_11]
  exact sparseColumn11_sum n

theorem branchColumn102_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 12) i) = _
  rw [branchColumn102_12]
  exact sparseColumn35_sum n

theorem branchColumn102_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 13) i) = _
  rw [branchColumn102_13]
  exact sparseColumn36_sum n

theorem branchColumn102_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 14) = sparseColumn37 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 14) = sparseDot37 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 14) i) = _
  rw [branchColumn102_14]
  exact sparseColumn37_sum n

theorem branchColumn102_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 15) i) = _
  rw [branchColumn102_15]
  exact sparseColumn38_sum n

theorem branchColumn102_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 16) i) = _
  rw [branchColumn102_16]
  exact sparseColumn39_sum n

theorem branchColumn102_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 17) = sparseColumn40 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 17) = sparseDot40 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 17) i) = _
  rw [branchColumn102_17]
  exact sparseColumn40_sum n

theorem branchColumn102_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 18) i) = _
  rw [branchColumn102_18]
  exact sparseColumn18_sum n

theorem branchColumn102_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 19) i) = _
  rw [branchColumn102_19]
  exact sparseColumn19_sum n

theorem branchColumn102_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 20) = sparseColumn58 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 20) = sparseDot58 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 20) i) = _
  rw [branchColumn102_20]
  exact sparseColumn58_sum n

theorem branchColumn102_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 21) i) = _
  rw [branchColumn102_21]
  exact sparseColumn21_sum n

theorem branchColumn102_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 22) i) = _
  rw [branchColumn102_22]
  exact sparseColumn22_sum n

theorem branchColumn102_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 23) = sparseColumn53 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 23) = sparseDot53 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 23) i) = _
  rw [branchColumn102_23]
  exact sparseColumn53_sum n

theorem branchColumn102_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 24) i) = _
  rw [branchColumn102_24]
  exact sparseColumn24_sum n

theorem branchColumn102_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 25) i) = _
  rw [branchColumn102_25]
  exact sparseColumn25_sum n

theorem branchColumn102_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 26) = sparseColumn56 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 26) = sparseDot56 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 26) i) = _
  rw [branchColumn102_26]
  exact sparseColumn56_sum n

theorem branchColumn102_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 27) i) = _
  rw [branchColumn102_27]
  exact sparseColumn27_sum n

theorem branchColumn102_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 28) i) = _
  rw [branchColumn102_28]
  exact sparseColumn28_sum n

theorem branchColumn102_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 29) = sparseColumn42 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 29) = sparseDot42 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 29) i) = _
  rw [branchColumn102_29]
  exact sparseColumn42_sum n

theorem branchColumn102_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 30) i) = _
  rw [branchColumn102_30]
  exact sparseColumn30_sum n

theorem branchColumn102_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 31) i) = _
  rw [branchColumn102_31]
  exact sparseColumn31_sum n

theorem branchColumn102_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 102 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 102 i)) = _
  rw [branchIntegerMatrix102_eq]
  simp only [branchIntegerMatrix102, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot102_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 102 i) 32) i) = _
  rw [branchColumn102_32]
  exact sparseColumn43_sum n

def branchSparseDots102 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot37, sparseDot38, sparseDot39, sparseDot40, sparseDot18, sparseDot19, sparseDot58, sparseDot21, sparseDot22, sparseDot53, sparseDot24, sparseDot25, sparseDot56, sparseDot27, sparseDot28, sparseDot42, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot102_0 :
    branchSparseDots102 0 = sparseDot00 := rfl

private theorem branchSparseDot102_1 :
    branchSparseDots102 1 = sparseDot01 := rfl

private theorem branchSparseDot102_2 :
    branchSparseDots102 2 = sparseDot02 := rfl

private theorem branchSparseDot102_3 :
    branchSparseDots102 3 = sparseDot03 := rfl

private theorem branchSparseDot102_4 :
    branchSparseDots102 4 = sparseDot04 := rfl

private theorem branchSparseDot102_5 :
    branchSparseDots102 5 = sparseDot05 := rfl

private theorem branchSparseDot102_6 :
    branchSparseDots102 6 = sparseDot06 := rfl

private theorem branchSparseDot102_7 :
    branchSparseDots102 7 = sparseDot07 := rfl

private theorem branchSparseDot102_8 :
    branchSparseDots102 8 = sparseDot08 := rfl

private theorem branchSparseDot102_9 :
    branchSparseDots102 9 = sparseDot09 := rfl

private theorem branchSparseDot102_10 :
    branchSparseDots102 10 = sparseDot10 := rfl

private theorem branchSparseDot102_11 :
    branchSparseDots102 11 = sparseDot11 := rfl

private theorem branchSparseDot102_12 :
    branchSparseDots102 12 = sparseDot35 := rfl

private theorem branchSparseDot102_13 :
    branchSparseDots102 13 = sparseDot36 := rfl

private theorem branchSparseDot102_14 :
    branchSparseDots102 14 = sparseDot37 := rfl

private theorem branchSparseDot102_15 :
    branchSparseDots102 15 = sparseDot38 := rfl

private theorem branchSparseDot102_16 :
    branchSparseDots102 16 = sparseDot39 := rfl

private theorem branchSparseDot102_17 :
    branchSparseDots102 17 = sparseDot40 := rfl

private theorem branchSparseDot102_18 :
    branchSparseDots102 18 = sparseDot18 := rfl

private theorem branchSparseDot102_19 :
    branchSparseDots102 19 = sparseDot19 := rfl

private theorem branchSparseDot102_20 :
    branchSparseDots102 20 = sparseDot58 := rfl

private theorem branchSparseDot102_21 :
    branchSparseDots102 21 = sparseDot21 := rfl

private theorem branchSparseDot102_22 :
    branchSparseDots102 22 = sparseDot22 := rfl

private theorem branchSparseDot102_23 :
    branchSparseDots102 23 = sparseDot53 := rfl

private theorem branchSparseDot102_24 :
    branchSparseDots102 24 = sparseDot24 := rfl

private theorem branchSparseDot102_25 :
    branchSparseDots102 25 = sparseDot25 := rfl

private theorem branchSparseDot102_26 :
    branchSparseDots102 26 = sparseDot56 := rfl

private theorem branchSparseDot102_27 :
    branchSparseDots102 27 = sparseDot27 := rfl

private theorem branchSparseDot102_28 :
    branchSparseDots102 28 = sparseDot28 := rfl

private theorem branchSparseDot102_29 :
    branchSparseDots102 29 = sparseDot42 := rfl

private theorem branchSparseDot102_30 :
    branchSparseDots102 30 = sparseDot30 := rfl

private theorem branchSparseDot102_31 :
    branchSparseDots102 31 = sparseDot31 := rfl

private theorem branchSparseDot102_32 :
    branchSparseDots102 32 = sparseDot43 := rfl

theorem branchDots102 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 102 i) k) = branchSparseDots102 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot102_0 n
      _ = _ := congrFun branchSparseDot102_0.symm n
  · calc
      _ = sparseDot01 n := branchDot102_1 n
      _ = _ := congrFun branchSparseDot102_1.symm n
  · calc
      _ = sparseDot02 n := branchDot102_2 n
      _ = _ := congrFun branchSparseDot102_2.symm n
  · calc
      _ = sparseDot03 n := branchDot102_3 n
      _ = _ := congrFun branchSparseDot102_3.symm n
  · calc
      _ = sparseDot04 n := branchDot102_4 n
      _ = _ := congrFun branchSparseDot102_4.symm n
  · calc
      _ = sparseDot05 n := branchDot102_5 n
      _ = _ := congrFun branchSparseDot102_5.symm n
  · calc
      _ = sparseDot06 n := branchDot102_6 n
      _ = _ := congrFun branchSparseDot102_6.symm n
  · calc
      _ = sparseDot07 n := branchDot102_7 n
      _ = _ := congrFun branchSparseDot102_7.symm n
  · calc
      _ = sparseDot08 n := branchDot102_8 n
      _ = _ := congrFun branchSparseDot102_8.symm n
  · calc
      _ = sparseDot09 n := branchDot102_9 n
      _ = _ := congrFun branchSparseDot102_9.symm n
  · calc
      _ = sparseDot10 n := branchDot102_10 n
      _ = _ := congrFun branchSparseDot102_10.symm n
  · calc
      _ = sparseDot11 n := branchDot102_11 n
      _ = _ := congrFun branchSparseDot102_11.symm n
  · calc
      _ = sparseDot35 n := branchDot102_12 n
      _ = _ := congrFun branchSparseDot102_12.symm n
  · calc
      _ = sparseDot36 n := branchDot102_13 n
      _ = _ := congrFun branchSparseDot102_13.symm n
  · calc
      _ = sparseDot37 n := branchDot102_14 n
      _ = _ := congrFun branchSparseDot102_14.symm n
  · calc
      _ = sparseDot38 n := branchDot102_15 n
      _ = _ := congrFun branchSparseDot102_15.symm n
  · calc
      _ = sparseDot39 n := branchDot102_16 n
      _ = _ := congrFun branchSparseDot102_16.symm n
  · calc
      _ = sparseDot40 n := branchDot102_17 n
      _ = _ := congrFun branchSparseDot102_17.symm n
  · calc
      _ = sparseDot18 n := branchDot102_18 n
      _ = _ := congrFun branchSparseDot102_18.symm n
  · calc
      _ = sparseDot19 n := branchDot102_19 n
      _ = _ := congrFun branchSparseDot102_19.symm n
  · calc
      _ = sparseDot58 n := branchDot102_20 n
      _ = _ := congrFun branchSparseDot102_20.symm n
  · calc
      _ = sparseDot21 n := branchDot102_21 n
      _ = _ := congrFun branchSparseDot102_21.symm n
  · calc
      _ = sparseDot22 n := branchDot102_22 n
      _ = _ := congrFun branchSparseDot102_22.symm n
  · calc
      _ = sparseDot53 n := branchDot102_23 n
      _ = _ := congrFun branchSparseDot102_23.symm n
  · calc
      _ = sparseDot24 n := branchDot102_24 n
      _ = _ := congrFun branchSparseDot102_24.symm n
  · calc
      _ = sparseDot25 n := branchDot102_25 n
      _ = _ := congrFun branchSparseDot102_25.symm n
  · calc
      _ = sparseDot56 n := branchDot102_26 n
      _ = _ := congrFun branchSparseDot102_26.symm n
  · calc
      _ = sparseDot27 n := branchDot102_27 n
      _ = _ := congrFun branchSparseDot102_27.symm n
  · calc
      _ = sparseDot28 n := branchDot102_28 n
      _ = _ := congrFun branchSparseDot102_28.symm n
  · calc
      _ = sparseDot42 n := branchDot102_29 n
      _ = _ := congrFun branchSparseDot102_29.symm n
  · calc
      _ = sparseDot30 n := branchDot102_30 n
      _ = _ := congrFun branchSparseDot102_30.symm n
  · calc
      _ = sparseDot31 n := branchDot102_31 n
      _ = _ := congrFun branchSparseDot102_31.symm n
  · calc
      _ = sparseDot43 n := branchDot102_32 n
      _ = _ := congrFun branchSparseDot102_32.symm n

def branchIntegerCurvature102 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101955390, 101955390, 79086693, 79086693, 115699695, 115699695, 48290998, 48290998, 289103692, 289103692]

theorem branchIntegerCurvature102_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 102 i)) = branchIntegerCurvature102 := by
  change curvatureNumerators ∘ branchRows 102 = branchIntegerCurvature102
  rw [show branchRows 102 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 52, 53, 54, 55, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature102_entry (i : Fin 42) :
    curvatureNumerators (branchRows 102 i) = branchIntegerCurvature102 i :=
  congrFun branchIntegerCurvature102_eq i

def branchResiduals102 : Fin 33 → Fin 2 → ℕ := ![![1299974688071347, 33000000000000], ![1547568338714486, 33000000000000], ![1581546938652594, 1334780787543421], ![33000000000000, 1023162669606423], ![862834505619167, 33000000000000], ![1053929828911293, 897235670319759], ![718437899644272, 624777238175104], ![33000000000000, 758032674910454], ![1578858284965189, 1130060485958286], ![1024064357040925, 33000000000000], ![33000000000000, 777258998153226], ![508497981315586, 462667529964949], ![988662669606423, 66000000000000], ![33000000000000, 862834505619167], ![1051890091114860, 895735670319792], ![474631775297671, 33000000000000], ![66000000000000, 743747994947801], ![955815327884707, 328515366361924], ![624270008705623, 258523427845872], ![631812607869006, 513941060933229], ![1317158320728742, 851835656632042], ![753705438750442, 374327679103908], ![470441009569099, 91598195142583], ![1317158320728742, 851835656632042], ![669077966760564, 232313982650245], ![507660306129472, 222935526651450], ![398909472332109, 851835656632042], ![411767323504107, 547562078551805], ![286734838804341, 300295031691792], ![398909472332109, 851835656632042], ![98335888223922, 552342907173232], ![968663138331286, 650744168333354], ![2018525953127619, 917530022434856]]

theorem branchResiduals102_eq : residualNumerators 102 = branchResiduals102 := rfl

theorem integerCheck102_0_0 :
    integerResidualCheck 102 0 0 (dualNumerators102 0 0) ∧
    integerMassCheck 102 0 0 (dualNumerators102 0 0) := by
  apply integerChecks_of_simple 102 0 0 (dualNumerators102 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1975857894035, 197188430033, 0, 1308901425339, 1692057632752, 143134913133, 1896652816305, 70360777679, 818327875519, 1016864670366]) (branchResiduals102 0 0) 18767167
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck102_0_1 :
    integerResidualCheck 102 0 1 (dualNumerators102 0 1) ∧
    integerMassCheck 102 0 1 (dualNumerators102 0 1) := by
  apply integerChecks_of_simple 102 0 1 (dualNumerators102 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals102 0 1) 18767167
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck102_1_0 :
    integerResidualCheck 102 1 0 (dualNumerators102 1 0) ∧
    integerMassCheck 102 1 0 (dualNumerators102 1 0) := by
  apply integerChecks_of_simple 102 1 0 (dualNumerators102 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 2339607766574, 233490264546, 0, 1549866490727, 2003560676621, 169485647447, 2245821257146, 83313998652, 968979732271, 1204066591796]) (branchResiduals102 1 0) 22176635
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck102_1_1 :
    integerResidualCheck 102 1 1 (dualNumerators102 1 1) ∧
    integerMassCheck 102 1 1 (dualNumerators102 1 1) := by
  apply integerChecks_of_simple 102 1 1 (dualNumerators102 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals102 1 1) 22176635
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck102_2_0 :
    integerResidualCheck 102 2 0 (dualNumerators102 2 0) ∧
    integerMassCheck 102 2 0 (dualNumerators102 2 0) := by
  apply integerChecks_of_simple 102 2 0 (dualNumerators102 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 2339607766576, 233490264546, 0, 1549866490728, 2003560676622, 169485647447, 2245821257148, 83313998652, 968979732272, 1204066591797]) (branchResiduals102 2 0) 22681452
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck102_2_1 :
    integerResidualCheck 102 2 1 (dualNumerators102 2 1) ∧
    integerMassCheck 102 2 1 (dualNumerators102 2 1) := by
  apply integerChecks_of_simple 102 2 1 (dualNumerators102 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1975857894033, 197188430032, 0, 1308901425338, 1692057632751, 143134913133, 1896652816304, 70360777679, 818327875518, 1016864670365]) (branchResiduals102 2 1) 22681452
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck102_3_0 :
    integerResidualCheck 102 3 0 (dualNumerators102 3 0) ∧
    integerMassCheck 102 3 0 (dualNumerators102 3 0) := by
  apply integerChecks_of_simple 102 3 0 (dualNumerators102 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals102 3 0) 16360330
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck102_3_1 :
    integerResidualCheck 102 3 1 (dualNumerators102 3 1) ∧
    integerMassCheck 102 3 1 (dualNumerators102 3 1) := by
  apply integerChecks_of_simple 102 3 1 (dualNumerators102 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000001, 0, 203380245200, 1104743927907, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1556835168689, 155370426011, 0, 1031321016287, 1333220793899, 112780107975, 1494427213684, 55439277044, 644784030255, 801216871619]) (branchResiduals102 3 1) 16360330
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck102_4_0 :
    integerResidualCheck 102 4 0 (dualNumerators102 4 0) ∧
    integerMassCheck 102 4 0 (dualNumerators102 4 0) := by
  apply integerChecks_of_simple 102 4 0 (dualNumerators102 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757645, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1314786650016, 131214251859, 0, 870976665588, 1125938658502, 95245651778, 1262081554611, 46819870729, 544536410901, 676647899379]) (branchResiduals102 4 0) 13760362
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck102_4_1 :
    integerResidualCheck 102 4 1 (dualNumerators102 4 1) ∧
    integerMassCheck 102 4 1 (dualNumerators102 4 1) := by
  apply integerChecks_of_simple 102 4 1 (dualNumerators102 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals102 4 1) 13760362
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck102_5_0 :
    integerResidualCheck 102 5 0 (dualNumerators102 5 0) ∧
    integerMassCheck 102 5 0 (dualNumerators102 5 0) := by
  apply integerChecks_of_simple 102 5 0 (dualNumerators102 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245201, 1104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1556835168690, 155370426011, 0, 1031321016288, 1333220793900, 112780107975, 1494427213685, 55439277044, 644784030255, 801216871620]) (branchResiduals102 5 0) 17641130
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck102_5_1 :
    integerResidualCheck 102 5 1 (dualNumerators102 5 1) ∧
    integerMassCheck 102 5 1 (dualNumerators102 5 1) := by
  apply integerChecks_of_simple 102 5 1 (dualNumerators102 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170264, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1314786650015, 131214251859, 0, 870976665588, 1125938658501, 95245651778, 1262081554610, 46819870729, 544536410901, 676647899378]) (branchResiduals102 5 1) 17641130
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck102_6_0 :
    integerResidualCheck 102 6 0 (dualNumerators102 6 0) ∧
    integerMassCheck 102 6 0 (dualNumerators102 6 0) := by
  apply integerChecks_of_simple 102 6 0 (dualNumerators102 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 659499318402, 1175693227483, 103906894360, 5439901403, 818327875519, 1016864670366]) (branchResiduals102 6 0) 8962451
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck102_6_1 :
    integerResidualCheck 102 6 1 (dualNumerators102 6 1) ∧
    integerMassCheck 102 6 1 (dualNumerators102 6 1) := by
  apply integerChecks_of_simple 102 6 1 (dualNumerators102 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 760187607595, 1097479190627, 0, 0]) (branchResiduals102 6 1) 8962451
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck102_7_0 :
    integerResidualCheck 102 7 0 (dualNumerators102 7 0) ∧
    integerMassCheck 102 7 0 (dualNumerators102 7 0) := by
  apply integerChecks_of_simple 102 7 0 (dualNumerators102 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals102 7 0) 10424794
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck102_7_1 :
    integerResidualCheck 102 7 1 (dualNumerators102 7 1) ∧
    integerMassCheck 102 7 1 (dualNumerators102 7 1) := by
  apply integerChecks_of_simple 102 7 1 (dualNumerators102 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646810, 830103123887, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675220, 1, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 1169803883289, 116745132273, 0, 774933245365, 1001780338312, 84742823724, 1122910628575, 41656999326, 484489866137, 602033295899]) (branchResiduals102 7 1) 10424794
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck102_8_0 :
    integerResidualCheck 102 8 0 (dualNumerators102 8 0) ∧
    integerMassCheck 102 8 0 (dualNumerators102 8 0) := by
  apply integerChecks_of_simple 102 8 0 (dualNumerators102 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293619, 1660206247774, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350440, 2, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 2339607766578, 233490264546, 0, 1549866490730, 2003560676624, 169485647447, 2245821257150, 83313998652, 968979732273, 1204066591798]) (branchResiduals102 8 0) 22681452
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck102_8_1 :
    integerResidualCheck 102 8 1 (dualNumerators102 8 1) ∧
    integerMassCheck 102 8 1 (dualNumerators102 8 1) := by
  apply integerChecks_of_simple 102 8 1 (dualNumerators102 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590429, 217988955956, 0, 1402086139075, 1269150346660, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546384, 0, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1668661932650, 166530613233, 0, 1105400337063, 1428985438754, 120881051972, 1601771242546, 59421455166, 691098574663, 858767916063]) (branchResiduals102 8 1) 22681452
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck102_9_0 :
    integerResidualCheck 102 9 0 (dualNumerators102 9 0) ∧
    integerMassCheck 102 9 0 (dualNumerators102 9 0) := by
  apply integerChecks_of_simple 102 9 0 (dualNumerators102 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 1556835168689, 155370426011, 0, 1031321016287, 1333220793899, 112780107975, 1494427213684, 55439277044, 644784030255, 801216871619]) (branchResiduals102 9 0) 16350530
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck102_9_1 :
    integerResidualCheck 102 9 1 (dualNumerators102 9 1) ∧
    integerMassCheck 102 9 1 (dualNumerators102 9 1) := by
  apply integerChecks_of_simple 102 9 1 (dualNumerators102 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals102 9 1) 16350530
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck102_10_0 :
    integerResidualCheck 102 10 0 (dualNumerators102 10 0) ∧
    integerMassCheck 102 10 0 (dualNumerators102 10 0) := by
  apply integerChecks_of_simple 102 10 0 (dualNumerators102 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals102 10 0) 10683139
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck102_10_1 :
    integerResidualCheck 102 10 1 (dualNumerators102 10 1) ∧
    integerMassCheck 102 10 1 (dualNumerators102 10 1) := by
  apply integerChecks_of_simple 102 10 1 (dualNumerators102 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 1190127971561, 118773453779, 0, 788396879662, 1019185197635, 86215139429, 1142419996822, 42380745027, 492907358117, 612492978948]) (branchResiduals102 10 1) 10683139
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck102_11_0 :
    integerResidualCheck 102 11 0 (dualNumerators102 11 0) ∧
    integerMassCheck 102 11 0 (dualNumerators102 11 0) := by
  apply integerChecks_of_simple 102 11 0 (dualNumerators102 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 739679135332, 73819158688, 0, 489998333105, 633436104137, 53583766880, 710028043730, 26340152980, 306347970271, 380671900746]) (branchResiduals102 11 0) 15120968
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck102_11_1 :
    integerResidualCheck 102 11 1 (dualNumerators102 11 1) ∧
    integerMassCheck 102 11 1 (dualNumerators102 11 1) := by
  apply integerChecks_of_simple 102 11 1 (dualNumerators102 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 674502345597, 67314587240, 0, 446822154676, 577620913742, 48862235962, 647463958437, 24019191727, 279354134309, 347129015395]) (branchResiduals102 11 1) 15120968
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck102_12_0 :
    integerResidualCheck 102 12 0 (dualNumerators102 12 0) ∧
    integerMassCheck 102 12 0 (dualNumerators102 12 0) := by
  apply integerChecks_of_simple 102 12 0 (dualNumerators102 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1556835168689, 155370426011, 0, 1031321016287, 1333220793899, 112780107975, 1494427213684, 55439277044, 644784030255, 801216871619]) (branchResiduals102 12 0) 16348076
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck102_12_1 :
    integerResidualCheck 102 12 1 (dualNumerators102 12 1) ∧
    integerMassCheck 102 12 1 (dualNumerators102 12 1) := by
  apply integerChecks_of_simple 102 12 1 (dualNumerators102 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals102 12 1) 16348076
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck102_13_0 :
    integerResidualCheck 102 13 0 (dualNumerators102 13 0) ∧
    integerMassCheck 102 13 0 (dualNumerators102 13 0) := by
  apply integerChecks_of_simple 102 13 0 (dualNumerators102 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals102 13 0) 13962901
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck102_13_1 :
    integerResidualCheck 102 13 1 (dualNumerators102 13 1) ∧
    integerMassCheck 102 13 1 (dualNumerators102 13 1) := by
  apply integerChecks_of_simple 102 13 1 (dualNumerators102 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1314786650016, 131214251859, 0, 870976665588, 1125938658502, 95245651778, 1262081554611, 46819870729, 544536410901, 676647899379]) (branchResiduals102 13 1) 13962901
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck102_14_0 :
    integerResidualCheck 102 14 0 (dualNumerators102 14 0) ∧
    integerMassCheck 102 14 0 (dualNumerators102 14 0) := by
  apply integerChecks_of_simple 102 14 0 (dualNumerators102 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1556835168690, 155370426011, 0, 1031321016288, 1333220793900, 112780107975, 1494427213685, 55439277044, 644784030255, 801216871620]) (branchResiduals102 14 0) 20161291
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck102_14_1 :
    integerResidualCheck 102 14 1 (dualNumerators102 14 1) ∧
    integerMassCheck 102 14 1 (dualNumerators102 14 1) := by
  apply integerChecks_of_simple 102 14 1 (dualNumerators102 14 1)
    (![561968834605, 103456879454, 561968834605, 0, 1, 844525275673, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 0, 1000000000000, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1314786650015, 131214251859, 0, 870976665588, 1125938658501, 95245651778, 1262081554610, 46819870729, 544536410901, 676647899378]) (branchResiduals102 14 1) 20161291
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck102_15_0 :
    integerResidualCheck 102 15 0 (dualNumerators102 15 0) ∧
    integerMassCheck 102 15 0 (dualNumerators102 15 0) := by
  apply integerChecks_of_simple 102 15 0 (dualNumerators102 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819834, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819834, 475117180167, 0, 736368196709, 813498294019, 739679135332, 73819158688, 0, 489998333105, 633436104137, 53583766880, 710028043729, 26340152980, 306347970271, 380671900746]) (branchResiduals102 15 0) 12900283
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck102_15_1 :
    integerResidualCheck 102 15 1 (dualNumerators102 15 1) ∧
    integerMassCheck 102 15 1 (dualNumerators102 15 1) := by
  apply integerChecks_of_simple 102 15 1 (dualNumerators102 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals102 15 1) 12900283
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck102_16_0 :
    integerResidualCheck 102 16 0 (dualNumerators102 16 0) ∧
    integerMassCheck 102 16 0 (dualNumerators102 16 0) := by
  apply integerChecks_of_simple 102 16 0 (dualNumerators102 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals102 16 0) 10683060
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck102_16_1 :
    integerResidualCheck 102 16 1 (dualNumerators102 16 1) ∧
    integerMassCheck 102 16 1 (dualNumerators102 16 1) := by
  apply integerChecks_of_simple 102 16 1 (dualNumerators102 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 1190127971561, 118773453779, 0, 788396879662, 1019185197635, 86215139429, 1142419996822, 42380745027, 492907358117, 612492978948]) (branchResiduals102 16 1) 10683060
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck102_17_0 :
    integerResidualCheck 102 17 0 (dualNumerators102 17 0) ∧
    integerMassCheck 102 17 0 (dualNumerators102 17 0) := by
  apply integerChecks_of_simple 102 17 0 (dualNumerators102 17 0)
    (![602334801078, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546386, 0, 844525275676, 602334801077, 905187143137, 0, 1184097183123, 0, 1071829546386, 0, 0, 1000000000001, 2028622458797, 1713222941254, 933538524390, 1402919220984, 933538524390, 1105400337065, 905187143137, 0, 1184097183123, 0, 0, 0, 1402919220984, 1549866490728, 1409227178680, 140639312049, 0, 933538524390, 1206814321600, 102087103741, 1352736300180, 50182920805, 583650214286, 725251211054]) (branchResiduals102 17 0) 15120968
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck102_17_1 :
    integerResidualCheck 102 17 1 (dualNumerators102 17 1) ∧
    integerMassCheck 102 17 1 (dualNumerators102 17 1) := by
  apply integerChecks_of_simple 102 17 1 (dualNumerators102 17 1)
    (![201148953074, 37030955649, 201148953074, 0, 1, 302286113723, 357936135756, 0, 282028158995, 201148953074, 0, 0, 0, 395427772555, 55650022034, 302286113723, 636234862349, 0, 677455931550, 572128657349, 311754022014, 468503118271, 311754022014, 369147059294, 0, 0, 0, 395427772555, 0, 302286113723, 468503118271, 517575975116, 470609652850, 46966322267, 0, 311754022014, 403014132522, 34091860545, 451744594666, 16758523606, 194909258696, 242196734371]) (branchResiduals102 17 1) 15120968
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck102_18_0 :
    integerResidualCheck 102 18 0 (dualNumerators102 18 0) ∧
    integerMassCheck 102 18 0 (dualNumerators102 18 0) := by
  apply integerChecks_of_simple 102 18 0 (dualNumerators102 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 1065874698487, 202522000941, 0, 763999473637, 900221849434, 170971222815, 953519106044, 33030453619, 477654049462, 593539022787]) (branchResiduals102 18 0) 13565580
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck102_18_1 :
    integerResidualCheck 102 18 1 (dualNumerators102 18 1) ∧
    integerMassCheck 102 18 1 (dualNumerators102 18 1) := by
  apply integerChecks_of_simple 102 18 1 (dualNumerators102 18 1)
    (![543792441172, 100110656623, 543792441172, 0, 1, 180671424657, 213932525007, 0, 71292007252, 50847095100, 180671424657, 0, 92181412018, 500721469249, 213932525007, 0, 0, 500721469249, 171249542446, 144624567043, 842805682483, 280016586907, 78806208846, 93314209907, 180671424657, 1, 92181412018, 500721469249, 0, 0, 280016586907, 776051426377, 127580111437, 3254448853, 78806208846, 0, 110493093096, 0, 188935308970, 91081277938, 49269804597, 61223288500]) (branchResiduals102 18 1) 13565580
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck102_19_0 :
    integerResidualCheck 102 19 0 (dualNumerators102 19 0) ∧
    integerMassCheck 102 19 0 (dualNumerators102 19 0) := by
  apply integerChecks_of_simple 102 19 0 (dualNumerators102 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 813889575590, 257303496658, 0, 645216866088, 673991557577, 230658067064, 653752451905, 19962510160, 403390917798, 501258706842]) (branchResiduals102 19 0) 8248658
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck102_19_1 :
    integerResidualCheck 102 19 1 (dualNumerators102 19 1) ∧
    integerMassCheck 102 19 1 (dualNumerators102 19 1) := by
  apply integerChecks_of_simple 102 19 1 (dualNumerators102 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 1, 987477735649, 0, 744995341971, 19004131667, 109777015092, 350406455885, 645216866088, 0, 838241775552, 149235960098, 287707656866, 357509209222]) (branchResiduals102 19 1) 8248658
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck102_20_0 :
    integerResidualCheck 102 20 0 (dualNumerators102 20 0) ∧
    integerMassCheck 102 20 0 (dualNumerators102 20 0) := by
  apply integerChecks_of_simple 102 20 0 (dualNumerators102 20 0)
    (![581614421966, 107073576748, 581614421967, 0, 2, 2066609823263, 2447066870339, 0, 815473519327, 581614421966, 2066609823265, 0, 177764221089, 965599897142, 2447066870339, 0, 0, 965599897144, 1958837637556, 1654287895857, 901424703129, 3202969314485, 901424703129, 1067374451772, 2066609823263, 2, 177764221088, 965599897143, 0, 0, 3202969314485, 1496550924032, 1459324915655, 37226008378, 901424703129, 0, 1263875081678, 0, 2161136251736, 1041833062749, 563572586882, 700302494796]) (branchResiduals102 20 0) 35312013
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck102_20_1 :
    integerResidualCheck 102 20 1 (dualNumerators102 20 1) ∧
    integerMassCheck 102 20 1 (dualNumerators102 20 1) := by
  apply integerChecks_of_simple 102 20 1 (dualNumerators102 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 25837005087, 1204076434982, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals102 20 1) 35312013
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck102_21_0 :
    integerResidualCheck 102 21 0 (dualNumerators102 21 0) ∧
    integerMassCheck 102 21 0 (dualNumerators102 21 0) := by
  apply integerChecks_of_simple 102 21 0 (dualNumerators102 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 1, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 604293255477, 704608169863, 851509250277, 798941670661, 583650214286, 725251211053]) (branchResiduals102 21 0) 11182451
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck102_21_1 :
    integerResidualCheck 102 21 1 (dualNumerators102 21 1) ∧
    integerMassCheck 102 21 1 (dualNumerators102 21 1) := by
  apply integerChecks_of_simple 102 21 1 (dualNumerators102 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 917967404853, 905358228364, 3460174706, 161253783489, 75547476522, 155395681176, 0, 0, 102979506989, 127963650709]) (branchResiduals102 21 1) 11182451
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck102_22_0 :
    integerResidualCheck 102 22 0 (dualNumerators102 22 0) ∧
    integerMassCheck 102 22 0 (dualNumerators102 22 0) := by
  apply integerChecks_of_simple 102 22 0 (dualNumerators102 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 234488508312, 529510965326, 460183470977, 0, 194101336204, 451115529884, 310954038967, 490382041752, 287707656866, 357509209222]) (branchResiduals102 22 0) 6465674
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck102_22_1 :
    integerResidualCheck 102 22 1 (dualNumerators102 22 1) ∧
    integerMassCheck 102 22 1 (dualNumerators102 22 1) := by
  apply integerChecks_of_simple 102 22 1 (dualNumerators102 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 108732662288, 12539033463, 1534493418, 71511669319, 33503252091, 68913760194, 0, 0, 45668611868, 56748400418]) (branchResiduals102 22 1) 6465674
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck102_23_0 :
    integerResidualCheck 102 23 0 (dualNumerators102 23 0) ∧
    integerMassCheck 102 23 0 (dualNumerators102 23 0) := by
  apply integerChecks_of_simple 102 23 0 (dualNumerators102 23 0)
    (![581614421966, 107073576748, 581614421967, 0, 2, 2066609823263, 2447066870339, 0, 815473519327, 581614421966, 2066609823265, 0, 177764221089, 965599897142, 2447066870339, 0, 0, 965599897144, 1958837637556, 1654287895857, 901424703129, 3202969314485, 901424703129, 1067374451772, 2066609823263, 2, 177764221088, 965599897143, 0, 0, 3202969314485, 1496550924032, 459324915655, 1037226008378, 901424703129, 0, 1263875081678, 0, 2161136251736, 1041833062749, 563572586882, 700302494796]) (branchResiduals102 23 0) 35297932
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck102_23_1 :
    integerResidualCheck 102 23 1 (dualNumerators102 23 1) ∧
    integerMassCheck 102 23 1 (dualNumerators102 23 1) := by
  apply integerChecks_of_simple 102 23 1 (dualNumerators102 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1830784228945, 211125748477, 25837005087, 1204076434982, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals102 23 1) 35297932
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck102_24_0 :
    integerResidualCheck 102 24 0 (dualNumerators102 24 0) ∧
    integerMassCheck 102 24 0 (dualNumerators102 24 0) := by
  apply integerChecks_of_simple 102 24 0 (dualNumerators102 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 384946583730, 686246488518, 569308312247, 737522866658, 477654049462, 593539022787]) (branchResiduals102 24 0) 9356857
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck102_24_1 :
    integerResidualCheck 102 24 1 (dualNumerators102 24 1) ∧
    integerMassCheck 102 24 1 (dualNumerators102 24 1) := by
  apply integerChecks_of_simple 102 24 1 (dualNumerators102 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623507, 113117556459, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 690777049383, 178822020994, 48434165160, 99625565721, 0, 0, 66021086067, 82038644814]) (branchResiduals102 24 1) 9356857
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck102_25_0 :
    integerResidualCheck 102 25 0 (dualNumerators102 25 0) ∧
    integerMassCheck 102 25 0 (dualNumerators102 25 0) := by
  apply integerChecks_of_simple 102 25 0 (dualNumerators102 25 0)
    (![34423495944, 6337268637, 34423495944, 0, 1, 22181646803, 26265225496, 0, 631959902239, 450728300227, 515126992874, 0, 137760279295, 748301940085, 609960421212, 0, 0, 748301940086, 1518022121617, 1282008050738, 53351822857, 34378591088, 698568688945, 827173216796, 515126992874, 1, 137760279295, 748301940085, 0, 0, 798378064725, 1159768101884, 492180793363, 667587308522, 53351822857, 0, 340714859712, 638738616250, 34378591088, 0, 436746587681, 542706888281]) (branchResiduals102 25 0) 8671199
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck102_25_1 :
    integerResidualCheck 102 25 1 (dualNumerators102 25 1) ∧
    integerMassCheck 102 25 1 (dualNumerators102 25 1) := by
  apply integerChecks_of_simple 102 25 1 (dualNumerators102 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 1, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 415529968297, 599898615461, 0, 0]) (branchResiduals102 25 1) 8671199
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck102_26_0 :
    integerResidualCheck 102 26 0 (dualNumerators102 26 0) ∧
    integerMassCheck 102 26 0 (dualNumerators102 26 0) := by
  apply integerChecks_of_simple 102 26 0 (dualNumerators102 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 1, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0]) (branchResiduals102 26 0) 15099566
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck102_26_1 :
    integerResidualCheck 102 26 1 (dualNumerators102 26 1) ∧
    integerMassCheck 102 26 1 (dualNumerators102 26 1) := by
  apply integerChecks_of_simple 102 26 1 (dualNumerators102 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 1025837005087, 204076434982, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals102 26 1) 15099566
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck102_27_0 :
    integerResidualCheck 102 27 0 (dualNumerators102 27 0) ∧
    integerMassCheck 102 27 0 (dualNumerators102 27 0) := by
  apply integerChecks_of_simple 102 27 0 (dualNumerators102 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 1, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 286173900105, 455299762271, 340673826058, 423325647580]) (branchResiduals102 27 0) 7338775
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck102_27_1 :
    integerResidualCheck 102 27 1 (dualNumerators102 27 1) ∧
    integerMassCheck 102 27 1 (dualNumerators102 27 1) := by
  apply integerChecks_of_simple 102 27 1 (dualNumerators102 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583262, 988432197465, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 963066529984, 568871411225, 0, 377837583379, 762995144865, 530765167250, 621055226706, 24161639382, 236224837801, 293536000677]) (branchResiduals102 27 1) 7338775
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck102_28_0 :
    integerResidualCheck 102 28 0 (dualNumerators102 28 0) ∧
    integerMassCheck 102 28 0 (dualNumerators102 28 0) := by
  apply integerChecks_of_simple 102 28 0 (dualNumerators102 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 1, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 450383711774, 395438493575, 287707656866, 357509209222]) (branchResiduals102 28 0) 10335557
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck102_28_1 :
    integerResidualCheck 102 28 1 (dualNumerators102 28 1) ∧
    integerMassCheck 102 28 1 (dualNumerators102 28 1) := by
  apply integerChecks_of_simple 102 28 1 (dualNumerators102 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 484442151291, 449974794159, 2156352207, 100492021777, 362407121329, 426731607121, 0, 0, 64175975503, 79745886859]) (branchResiduals102 28 1) 10335557
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck102_29_0 :
    integerResidualCheck 102 29 0 (dualNumerators102 29 0) ∧
    integerMassCheck 102 29 0 (dualNumerators102 29 0) := by
  apply integerChecks_of_simple 102 29 0 (dualNumerators102 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 1, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0]) (branchResiduals102 29 0) 40352153
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck102_29_1 :
    integerResidualCheck 102 29 1 (dualNumerators102 29 1) ∧
    integerMassCheck 102 29 1 (dualNumerators102 29 1) := by
  apply integerChecks_of_simple 102 29 1 (dualNumerators102 29 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1830784228945, 211125748477, 25837005087, 1204076434982, 1564110399358, 160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals102 29 1) 40352153
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck102_30_0 :
    integerResidualCheck 102 30 0 (dualNumerators102 30 0) ∧
    integerMassCheck 102 30 0 (dualNumerators102 30 0) := by
  apply integerChecks_of_simple 102 30 0 (dualNumerators102 30 0)
    (![49325597255, 9080703511, 49325597255, 0, 0, 3298611714, 3905876838, 0, 69158736213, 49325597255, 3298611714, 0, 15075840703, 81890664738, 3905876838, 0, 0, 81890664738, 166125241653, 1140296965504, 76448090321, 5112407761, 76448090321, 90521968404, 3298611714, 0, 15075840703, 81890664738, 0, 0, 5112407761, 126919597181, 114050929660, 12868667522, 1351620770, 75096469552, 97475206242, 9711601556, 5112407761, 0, 107186807798, 0]) (branchResiduals102 30 0) 7680628
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck102_30_1 :
    integerResidualCheck 102 30 1 (dualNumerators102 30 1) ∧
    integerMassCheck 102 30 1 (dualNumerators102 30 1) := by
  apply integerChecks_of_simple 102 30 1 (dualNumerators102 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195716, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 1, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 822559133868, 82090490772, 0, 544901951702, 704411721639, 59587751998, 893898125793, 34752663293, 281282522283, 482716951355]) (branchResiduals102 30 1) 7680628
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck102_31_0 :
    integerResidualCheck 102 31 0 (dualNumerators102 31 0) ∧
    integerMassCheck 102 31 0 (dualNumerators102 31 0) := by
  apply integerChecks_of_simple 102 31 0 (dualNumerators102 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 1032415642124, 2, 592902192609, 0, 1222480453651, 0, 500720887661, 0, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642124, 1, 592902192609, 0, 0, 0, 1600106408231, 776050524992, 756746629027, 19303895966, 820904449873, 751938125789, 655394283556, 0, 732639129519, 867467278713, 655394283556, 0]) (branchResiduals102 31 0) 32891612
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck102_31_1 :
    integerResidualCheck 102 31 1 (dualNumerators102 31 1) ∧
    integerMassCheck 102 31 1 (dualNumerators102 31 1) := by
  apply integerChecks_of_simple 102 31 1 (dualNumerators102 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 556963843680, 992902647048, 725570984152, 37986262977, 327950144489, 1221916346239]) (branchResiduals102 31 1) 32891612
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck102_32_0 :
    integerResidualCheck 102 32 0 (dualNumerators102 32 0) ∧
    integerMassCheck 102 32 0 (dualNumerators102 32 0) := by
  apply integerChecks_of_simple 102 32 0 (dualNumerators102 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 0, 2743468108582, 2028778803022, 0, 505064750776, 2743468108580, 1713354977902, 2, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 2028778803022, 0, 0, 0, 4252009289869, 2655471466972, 2414506401585, 240965065387, 0, 1599482877825, 2067701325315, 174911447373, 4074076396250, 177932893619, 0, 2242612772688]) (branchResiduals102 32 0) 67647473
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck102_32_1 :
    integerResidualCheck 102 32 1 (dualNumerators102 32 1) ∧
    integerMassCheck 102 32 1 (dualNumerators102 32 1) := by
  apply integerChecks_of_simple 102 32 1 (dualNumerators102 32 1)
    (![830518849052, 152896180641, 830518849053, 0, 1, 55540314888, 65765130409, 0, 1164458966499, 830518849051, 55540314888, 0, 253839194360, 1378832582089, 65765130409, 0, 0, 1378832582090, 2797130742946, 2362247611782, 1287193334063, 86080072929, 1287193334063, 1524162000997, 55540314888, 0, 253839194360, 1378832582089, 0, 0, 86080072929, 2137006415304, 1920330459346, 216675955958, 22757890183, 1264435443881, 1641237016970, 163518915031, 86080072929, 0, 1804755932001, 0]) (branchResiduals102 32 1) 67647473
    branchSparseDots102 branchIntegerCurvature102 branchDots102
    branchIntegerCurvature102_entry rfl
    (congrFun (congrFun branchResiduals102_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks102 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 102 j s (dualNumerators102 j s) ∧
    integerMassCheck 102 j s (dualNumerators102 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck102_0_0
    · exact integerCheck102_0_1
  · fin_cases s
    · exact integerCheck102_1_0
    · exact integerCheck102_1_1
  · fin_cases s
    · exact integerCheck102_2_0
    · exact integerCheck102_2_1
  · fin_cases s
    · exact integerCheck102_3_0
    · exact integerCheck102_3_1
  · fin_cases s
    · exact integerCheck102_4_0
    · exact integerCheck102_4_1
  · fin_cases s
    · exact integerCheck102_5_0
    · exact integerCheck102_5_1
  · fin_cases s
    · exact integerCheck102_6_0
    · exact integerCheck102_6_1
  · fin_cases s
    · exact integerCheck102_7_0
    · exact integerCheck102_7_1
  · fin_cases s
    · exact integerCheck102_8_0
    · exact integerCheck102_8_1
  · fin_cases s
    · exact integerCheck102_9_0
    · exact integerCheck102_9_1
  · fin_cases s
    · exact integerCheck102_10_0
    · exact integerCheck102_10_1
  · fin_cases s
    · exact integerCheck102_11_0
    · exact integerCheck102_11_1
  · fin_cases s
    · exact integerCheck102_12_0
    · exact integerCheck102_12_1
  · fin_cases s
    · exact integerCheck102_13_0
    · exact integerCheck102_13_1
  · fin_cases s
    · exact integerCheck102_14_0
    · exact integerCheck102_14_1
  · fin_cases s
    · exact integerCheck102_15_0
    · exact integerCheck102_15_1
  · fin_cases s
    · exact integerCheck102_16_0
    · exact integerCheck102_16_1
  · fin_cases s
    · exact integerCheck102_17_0
    · exact integerCheck102_17_1
  · fin_cases s
    · exact integerCheck102_18_0
    · exact integerCheck102_18_1
  · fin_cases s
    · exact integerCheck102_19_0
    · exact integerCheck102_19_1
  · fin_cases s
    · exact integerCheck102_20_0
    · exact integerCheck102_20_1
  · fin_cases s
    · exact integerCheck102_21_0
    · exact integerCheck102_21_1
  · fin_cases s
    · exact integerCheck102_22_0
    · exact integerCheck102_22_1
  · fin_cases s
    · exact integerCheck102_23_0
    · exact integerCheck102_23_1
  · fin_cases s
    · exact integerCheck102_24_0
    · exact integerCheck102_24_1
  · fin_cases s
    · exact integerCheck102_25_0
    · exact integerCheck102_25_1
  · fin_cases s
    · exact integerCheck102_26_0
    · exact integerCheck102_26_1
  · fin_cases s
    · exact integerCheck102_27_0
    · exact integerCheck102_27_1
  · fin_cases s
    · exact integerCheck102_28_0
    · exact integerCheck102_28_1
  · fin_cases s
    · exact integerCheck102_29_0
    · exact integerCheck102_29_1
  · fin_cases s
    · exact integerCheck102_30_0
    · exact integerCheck102_30_1
  · fin_cases s
    · exact integerCheck102_31_0
    · exact integerCheck102_31_1
  · fin_cases s
    · exact integerCheck102_32_0
    · exact integerCheck102_32_1

end ElevenSquare.Tasks.T06
