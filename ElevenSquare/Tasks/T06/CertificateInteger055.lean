import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual055
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
import ElevenSquare.Tasks.T06.SparseColumn26
import ElevenSquare.Tasks.T06.SparseColumn27
import ElevenSquare.Tasks.T06.SparseColumn28
import ElevenSquare.Tasks.T06.SparseColumn30
import ElevenSquare.Tasks.T06.SparseColumn31
import ElevenSquare.Tasks.T06.SparseColumn35
import ElevenSquare.Tasks.T06.SparseColumn36
import ElevenSquare.Tasks.T06.SparseColumn38
import ElevenSquare.Tasks.T06.SparseColumn39
import ElevenSquare.Tasks.T06.SparseColumn41
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn49
import ElevenSquare.Tasks.T06.SparseColumn52
import ElevenSquare.Tasks.T06.SparseColumn54

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix055 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix055_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = branchIntegerMatrix055 := by
  change roundedGradients ∘ branchRows 55 = branchIntegerMatrix055
  rw [show branchRows 55 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 34, 35, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, branchIntegerMatrix055]

theorem branchColumn055_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 0) i) = _
  rw [branchColumn055_0]
  exact sparseColumn00_sum n

theorem branchColumn055_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 1) i) = _
  rw [branchColumn055_1]
  exact sparseColumn01_sum n

theorem branchColumn055_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 2) i) = _
  rw [branchColumn055_2]
  exact sparseColumn02_sum n

theorem branchColumn055_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 3) i) = _
  rw [branchColumn055_3]
  exact sparseColumn03_sum n

theorem branchColumn055_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 4) i) = _
  rw [branchColumn055_4]
  exact sparseColumn04_sum n

theorem branchColumn055_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 5) i) = _
  rw [branchColumn055_5]
  exact sparseColumn05_sum n

theorem branchColumn055_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 6) i) = _
  rw [branchColumn055_6]
  exact sparseColumn06_sum n

theorem branchColumn055_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 7) i) = _
  rw [branchColumn055_7]
  exact sparseColumn07_sum n

theorem branchColumn055_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 8) i) = _
  rw [branchColumn055_8]
  exact sparseColumn08_sum n

theorem branchColumn055_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 9) i) = _
  rw [branchColumn055_9]
  exact sparseColumn09_sum n

theorem branchColumn055_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 10) i) = _
  rw [branchColumn055_10]
  exact sparseColumn10_sum n

theorem branchColumn055_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 11) i) = _
  rw [branchColumn055_11]
  exact sparseColumn11_sum n

theorem branchColumn055_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 12) i) = _
  rw [branchColumn055_12]
  exact sparseColumn35_sum n

theorem branchColumn055_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 13) i) = _
  rw [branchColumn055_13]
  exact sparseColumn36_sum n

theorem branchColumn055_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 14) i) = _
  rw [branchColumn055_14]
  exact sparseColumn41_sum n

theorem branchColumn055_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 15) i) = _
  rw [branchColumn055_15]
  exact sparseColumn38_sum n

theorem branchColumn055_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 16) i) = _
  rw [branchColumn055_16]
  exact sparseColumn39_sum n

theorem branchColumn055_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 17) i) = _
  rw [branchColumn055_17]
  exact sparseColumn17_sum n

theorem branchColumn055_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 18) i) = _
  rw [branchColumn055_18]
  exact sparseColumn18_sum n

theorem branchColumn055_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 19) i) = _
  rw [branchColumn055_19]
  exact sparseColumn19_sum n

theorem branchColumn055_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 20) = sparseColumn52 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 20) = sparseDot52 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 20) i) = _
  rw [branchColumn055_20]
  exact sparseColumn52_sum n

theorem branchColumn055_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 21) i) = _
  rw [branchColumn055_21]
  exact sparseColumn21_sum n

theorem branchColumn055_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 22) i) = _
  rw [branchColumn055_22]
  exact sparseColumn22_sum n

theorem branchColumn055_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 23) = sparseColumn54 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 23) = sparseDot54 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 23) i) = _
  rw [branchColumn055_23]
  exact sparseColumn54_sum n

theorem branchColumn055_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 24) i) = _
  rw [branchColumn055_24]
  exact sparseColumn24_sum n

theorem branchColumn055_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 25) i) = _
  rw [branchColumn055_25]
  exact sparseColumn25_sum n

theorem branchColumn055_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 26) = sparseColumn26 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 26) = sparseDot26 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 26) i) = _
  rw [branchColumn055_26]
  exact sparseColumn26_sum n

theorem branchColumn055_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 27) i) = _
  rw [branchColumn055_27]
  exact sparseColumn27_sum n

theorem branchColumn055_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 28) i) = _
  rw [branchColumn055_28]
  exact sparseColumn28_sum n

theorem branchColumn055_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 29) = sparseColumn49 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 29) = sparseDot49 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 29) i) = _
  rw [branchColumn055_29]
  exact sparseColumn49_sum n

theorem branchColumn055_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 30) i) = _
  rw [branchColumn055_30]
  exact sparseColumn30_sum n

theorem branchColumn055_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 31) i) = _
  rw [branchColumn055_31]
  exact sparseColumn31_sum n

theorem branchColumn055_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 55 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 55 i)) = _
  rw [branchIntegerMatrix055_eq]
  simp only [branchIntegerMatrix055, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot055_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 55 i) 32) i) = _
  rw [branchColumn055_32]
  exact sparseColumn43_sum n

def branchSparseDots055 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot52, sparseDot21, sparseDot22, sparseDot54, sparseDot24, sparseDot25, sparseDot26, sparseDot27, sparseDot28, sparseDot49, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot055_0 :
    branchSparseDots055 0 = sparseDot00 := rfl

private theorem branchSparseDot055_1 :
    branchSparseDots055 1 = sparseDot01 := rfl

private theorem branchSparseDot055_2 :
    branchSparseDots055 2 = sparseDot02 := rfl

private theorem branchSparseDot055_3 :
    branchSparseDots055 3 = sparseDot03 := rfl

private theorem branchSparseDot055_4 :
    branchSparseDots055 4 = sparseDot04 := rfl

private theorem branchSparseDot055_5 :
    branchSparseDots055 5 = sparseDot05 := rfl

private theorem branchSparseDot055_6 :
    branchSparseDots055 6 = sparseDot06 := rfl

private theorem branchSparseDot055_7 :
    branchSparseDots055 7 = sparseDot07 := rfl

private theorem branchSparseDot055_8 :
    branchSparseDots055 8 = sparseDot08 := rfl

private theorem branchSparseDot055_9 :
    branchSparseDots055 9 = sparseDot09 := rfl

private theorem branchSparseDot055_10 :
    branchSparseDots055 10 = sparseDot10 := rfl

private theorem branchSparseDot055_11 :
    branchSparseDots055 11 = sparseDot11 := rfl

private theorem branchSparseDot055_12 :
    branchSparseDots055 12 = sparseDot35 := rfl

private theorem branchSparseDot055_13 :
    branchSparseDots055 13 = sparseDot36 := rfl

private theorem branchSparseDot055_14 :
    branchSparseDots055 14 = sparseDot41 := rfl

private theorem branchSparseDot055_15 :
    branchSparseDots055 15 = sparseDot38 := rfl

private theorem branchSparseDot055_16 :
    branchSparseDots055 16 = sparseDot39 := rfl

private theorem branchSparseDot055_17 :
    branchSparseDots055 17 = sparseDot17 := rfl

private theorem branchSparseDot055_18 :
    branchSparseDots055 18 = sparseDot18 := rfl

private theorem branchSparseDot055_19 :
    branchSparseDots055 19 = sparseDot19 := rfl

private theorem branchSparseDot055_20 :
    branchSparseDots055 20 = sparseDot52 := rfl

private theorem branchSparseDot055_21 :
    branchSparseDots055 21 = sparseDot21 := rfl

private theorem branchSparseDot055_22 :
    branchSparseDots055 22 = sparseDot22 := rfl

private theorem branchSparseDot055_23 :
    branchSparseDots055 23 = sparseDot54 := rfl

private theorem branchSparseDot055_24 :
    branchSparseDots055 24 = sparseDot24 := rfl

private theorem branchSparseDot055_25 :
    branchSparseDots055 25 = sparseDot25 := rfl

private theorem branchSparseDot055_26 :
    branchSparseDots055 26 = sparseDot26 := rfl

private theorem branchSparseDot055_27 :
    branchSparseDots055 27 = sparseDot27 := rfl

private theorem branchSparseDot055_28 :
    branchSparseDots055 28 = sparseDot28 := rfl

private theorem branchSparseDot055_29 :
    branchSparseDots055 29 = sparseDot49 := rfl

private theorem branchSparseDot055_30 :
    branchSparseDots055 30 = sparseDot30 := rfl

private theorem branchSparseDot055_31 :
    branchSparseDots055 31 = sparseDot31 := rfl

private theorem branchSparseDot055_32 :
    branchSparseDots055 32 = sparseDot43 := rfl

theorem branchDots055 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 55 i) k) = branchSparseDots055 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot055_0 n
      _ = _ := congrFun branchSparseDot055_0.symm n
  · calc
      _ = sparseDot01 n := branchDot055_1 n
      _ = _ := congrFun branchSparseDot055_1.symm n
  · calc
      _ = sparseDot02 n := branchDot055_2 n
      _ = _ := congrFun branchSparseDot055_2.symm n
  · calc
      _ = sparseDot03 n := branchDot055_3 n
      _ = _ := congrFun branchSparseDot055_3.symm n
  · calc
      _ = sparseDot04 n := branchDot055_4 n
      _ = _ := congrFun branchSparseDot055_4.symm n
  · calc
      _ = sparseDot05 n := branchDot055_5 n
      _ = _ := congrFun branchSparseDot055_5.symm n
  · calc
      _ = sparseDot06 n := branchDot055_6 n
      _ = _ := congrFun branchSparseDot055_6.symm n
  · calc
      _ = sparseDot07 n := branchDot055_7 n
      _ = _ := congrFun branchSparseDot055_7.symm n
  · calc
      _ = sparseDot08 n := branchDot055_8 n
      _ = _ := congrFun branchSparseDot055_8.symm n
  · calc
      _ = sparseDot09 n := branchDot055_9 n
      _ = _ := congrFun branchSparseDot055_9.symm n
  · calc
      _ = sparseDot10 n := branchDot055_10 n
      _ = _ := congrFun branchSparseDot055_10.symm n
  · calc
      _ = sparseDot11 n := branchDot055_11 n
      _ = _ := congrFun branchSparseDot055_11.symm n
  · calc
      _ = sparseDot35 n := branchDot055_12 n
      _ = _ := congrFun branchSparseDot055_12.symm n
  · calc
      _ = sparseDot36 n := branchDot055_13 n
      _ = _ := congrFun branchSparseDot055_13.symm n
  · calc
      _ = sparseDot41 n := branchDot055_14 n
      _ = _ := congrFun branchSparseDot055_14.symm n
  · calc
      _ = sparseDot38 n := branchDot055_15 n
      _ = _ := congrFun branchSparseDot055_15.symm n
  · calc
      _ = sparseDot39 n := branchDot055_16 n
      _ = _ := congrFun branchSparseDot055_16.symm n
  · calc
      _ = sparseDot17 n := branchDot055_17 n
      _ = _ := congrFun branchSparseDot055_17.symm n
  · calc
      _ = sparseDot18 n := branchDot055_18 n
      _ = _ := congrFun branchSparseDot055_18.symm n
  · calc
      _ = sparseDot19 n := branchDot055_19 n
      _ = _ := congrFun branchSparseDot055_19.symm n
  · calc
      _ = sparseDot52 n := branchDot055_20 n
      _ = _ := congrFun branchSparseDot055_20.symm n
  · calc
      _ = sparseDot21 n := branchDot055_21 n
      _ = _ := congrFun branchSparseDot055_21.symm n
  · calc
      _ = sparseDot22 n := branchDot055_22 n
      _ = _ := congrFun branchSparseDot055_22.symm n
  · calc
      _ = sparseDot54 n := branchDot055_23 n
      _ = _ := congrFun branchSparseDot055_23.symm n
  · calc
      _ = sparseDot24 n := branchDot055_24 n
      _ = _ := congrFun branchSparseDot055_24.symm n
  · calc
      _ = sparseDot25 n := branchDot055_25 n
      _ = _ := congrFun branchSparseDot055_25.symm n
  · calc
      _ = sparseDot26 n := branchDot055_26 n
      _ = _ := congrFun branchSparseDot055_26.symm n
  · calc
      _ = sparseDot27 n := branchDot055_27 n
      _ = _ := congrFun branchSparseDot055_27.symm n
  · calc
      _ = sparseDot28 n := branchDot055_28 n
      _ = _ := congrFun branchSparseDot055_28.symm n
  · calc
      _ = sparseDot49 n := branchDot055_29 n
      _ = _ := congrFun branchSparseDot055_29.symm n
  · calc
      _ = sparseDot30 n := branchDot055_30 n
      _ = _ := congrFun branchSparseDot055_30.symm n
  · calc
      _ = sparseDot31 n := branchDot055_31 n
      _ = _ := congrFun branchSparseDot055_31.symm n
  · calc
      _ = sparseDot43 n := branchDot055_32 n
      _ = _ := congrFun branchSparseDot055_32.symm n

def branchIntegerCurvature055 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101955390, 101955390, 44932602, 44932602, 106371291, 106371291, 48290998, 48290998, 289103692, 289103692]

theorem branchIntegerCurvature055_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 55 i)) = branchIntegerCurvature055 := by
  change curvatureNumerators ∘ branchRows 55 = branchIntegerCurvature055
  rw [show branchRows 55 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 34, 35, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature055_entry (i : Fin 42) :
    curvatureNumerators (branchRows 55 i) = branchIntegerCurvature055 i :=
  congrFun branchIntegerCurvature055_eq i

def branchResiduals055 : Fin 33 → Fin 2 → ℕ := ![![1298358832191850, 33000000000000], ![1545976822133216, 33000000000000], ![1582092005565650, 1335969174222770], ![33000000000000, 1022930750167970], ![857830431900127, 33000000000000], ![1054811092855473, 893551548351339], ![719847115983962, 622101700319854], ![33000000000000, 760492582531897], ![1575841241234724, 1129128913475471], ![1024411482413589, 33000000000000], ![33000000000000, 776664960286302], ![509913235637530, 466008616642146], ![989009794979087, 66000000000000], ![33000000000000, 860568754468382], ![1054771355059073, 485776263453423], ![475834814781294, 33000000000000], ![66000000000000, 743153957080877], ![659651122074735, 462407576546813], ![621217066994571, 257752760320188], ![625483586774998, 505762080657722], ![1358614081564648, 951157236569897], ![753830467458193, 387499252561215], ![465183772839361, 96820869253143], ![1358614081564648, 951157236569897], ![667371168578856, 230003409392788], ![500485136134307, 221360137673294], ![396136216194598, 853076072054392], ![407212648413384, 545348246810860], ![283466941102630, 308506886524828], ![396136216194598, 951157236569897], ![96820869253143, 553234699230039], ![966898838209851, 648436709070965], ![2021223467364655, 951157236569897]]

theorem branchResiduals055_eq : residualNumerators 55 = branchResiduals055 := rfl

theorem integerCheck055_0_0 :
    integerResidualCheck 55 0 0 (dualNumerators055 0 0) ∧
    integerMassCheck 55 0 0 (dualNumerators055 0 0) := by
  apply integerChecks_of_simple 55 0 0 (dualNumerators055 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1820383169708, 352663154359, 0, 1308901425339, 1754571864380, 80620681505, 1741178091979, 225835502005, 818327875519, 1016864670366]) (branchResiduals055 0 0) 18767167
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck055_0_1 :
    integerResidualCheck 55 0 1 (dualNumerators055 0 1) ∧
    integerMassCheck 55 0 1 (dualNumerators055 0 1) := by
  apply integerChecks_of_simple 55 0 1 (dualNumerators055 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals055 0 1) 18767167
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck055_1_0 :
    integerResidualCheck 55 1 0 (dualNumerators055 1 0) ∧
    integerMassCheck 55 1 0 (dualNumerators055 1 0) := by
  apply integerChecks_of_simple 55 1 0 (dualNumerators055 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 2155510583453, 417587447667, 0, 1549866490727, 2077583602197, 95462721871, 2061724074025, 267411181773, 968979732271, 1204066591796]) (branchResiduals055 1 0) 22176635
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck055_1_1 :
    integerResidualCheck 55 1 1 (dualNumerators055 1 1) ∧
    integerMassCheck 55 1 1 (dualNumerators055 1 1) := by
  apply integerChecks_of_simple 55 1 1 (dualNumerators055 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals055 1 1) 22176635
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck055_2_0 :
    integerResidualCheck 55 2 0 (dualNumerators055 2 0) ∧
    integerMassCheck 55 2 0 (dualNumerators055 2 0) := by
  apply integerChecks_of_simple 55 2 0 (dualNumerators055 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 2155510583455, 417587447667, 0, 1549866490728, 2077583602198, 95462721871, 2061724074027, 267411181773, 968979732272, 1204066591797]) (branchResiduals055 2 0) 22681452
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck055_2_1 :
    integerResidualCheck 55 2 1 (dualNumerators055 2 1) ∧
    integerMassCheck 55 2 1 (dualNumerators055 2 1) := by
  apply integerChecks_of_simple 55 2 1 (dualNumerators055 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1820383169707, 352663154359, 0, 1308901425338, 1754571864379, 80620681504, 1741178091978, 225835502005, 818327875518, 1016864670365]) (branchResiduals055 2 1) 22681452
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck055_3_0 :
    integerResidualCheck 55 3 0 (dualNumerators055 3 0) ∧
    integerMassCheck 55 3 0 (dualNumerators055 3 0) := by
  apply integerChecks_of_simple 55 3 0 (dualNumerators055 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals055 3 0) 16360330
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck055_3_1 :
    integerResidualCheck 55 3 1 (dualNumerators055 3 1) ∧
    integerMassCheck 55 3 1 (dualNumerators055 3 1) := by
  apply integerChecks_of_simple 55 3 1 (dualNumerators055 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000001, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000001, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1434332169154, 277873425546, 0, 1031321016287, 1382477552007, 63523349867, 1371924214149, 177942276579, 644784030255, 801216871619]) (branchResiduals055 3 1) 16360330
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck055_4_0 :
    integerResidualCheck 55 4 0 (dualNumerators055 4 0) ∧
    integerMassCheck 55 4 0 (dualNumerators055 4 0) := by
  apply integerChecks_of_simple 55 4 0 (dualNumerators055 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000001, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1211329770563, 234671131311, 0, 870976665588, 1167537235722, 53647074558, 1158624675158, 150276750182, 544536410901, 676647899379]) (branchResiduals055 4 0) 13760362
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck055_4_1 :
    integerResidualCheck 55 4 1 (dualNumerators055 4 1) ∧
    integerMassCheck 55 4 1 (dualNumerators055 4 1) := by
  apply integerChecks_of_simple 55 4 1 (dualNumerators055 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals055 4 1) 13760362
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck055_5_0 :
    integerResidualCheck 55 5 0 (dualNumerators055 5 0) ∧
    integerMassCheck 55 5 0 (dualNumerators055 5 0) := by
  apply integerChecks_of_simple 55 5 0 (dualNumerators055 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1434332169156, 277873425546, 0, 1031321016288, 1382477552008, 63523349867, 1371924214150, 177942276579, 644784030255, 801216871620]) (branchResiduals055 5 0) 17641130
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck055_5_1 :
    integerResidualCheck 55 5 1 (dualNumerators055 5 1) ∧
    integerMassCheck 55 5 1 (dualNumerators055 5 1) := by
  apply integerChecks_of_simple 55 5 1 (dualNumerators055 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1211329770562, 234671131311, 0, 870976665588, 1167537235721, 53647074558, 1158624675157, 150276750182, 544536410901, 676647899378]) (branchResiduals055 5 1) 17641130
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck055_6_0 :
    integerResidualCheck 55 6 0 (dualNumerators055 6 0) ∧
    integerMassCheck 55 6 0 (dualNumerators055 6 0) := by
  apply integerChecks_of_simple 55 6 0 (dualNumerators055 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 877488274356, 957704271528, 103906894360, 5439901403, 818327875519, 1016864670366]) (branchResiduals055 6 0) 8962451
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck055_6_1 :
    integerResidualCheck 55 6 1 (dualNumerators055 6 1) ∧
    integerMassCheck 55 6 1 (dualNumerators055 6 1) := by
  apply integerChecks_of_simple 55 6 1 (dualNumerators055 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 760187607595, 1097479190627, 0, 0]) (branchResiduals055 6 1) 8962451
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck055_7_0 :
    integerResidualCheck 55 7 0 (dualNumerators055 7 0) ∧
    integerMassCheck 55 7 0 (dualNumerators055 7 0) := by
  apply integerChecks_of_simple 55 7 0 (dualNumerators055 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals055 7 0) 10424794
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck055_7_1 :
    integerResidualCheck 55 7 1 (dualNumerators055 7 1) ∧
    integerMassCheck 55 7 1 (dualNumerators055 7 1) := by
  apply integerChecks_of_simple 55 7 1 (dualNumerators055 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 1077755291729, 208793723834, 0, 774933245365, 1038791801100, 47731360936, 1030862037014, 133705590887, 484489866137, 602033295899]) (branchResiduals055 7 1) 10424794
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck055_8_0 :
    integerResidualCheck 55 8 0 (dualNumerators055 8 0) ∧
    integerMassCheck 55 8 0 (dualNumerators055 8 0) := by
  apply integerChecks_of_simple 55 8 0 (dualNumerators055 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 2155510583457, 417587447668, 0, 1549866490730, 2077583602200, 95462721871, 2061724074028, 267411181773, 968979732273, 1204066591798]) (branchResiduals055 8 0) 22681452
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck055_8_1 :
    integerResidualCheck 55 8 1 (dualNumerators055 8 1) ∧
    integerMassCheck 55 8 1 (dualNumerators055 8 1) := by
  apply integerChecks_of_simple 55 8 1 (dualNumerators055 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1537359598228, 297832947655, 0, 1105400337063, 1481780287453, 68086203273, 1470468908124, 190723789588, 691098574663, 858767916063]) (branchResiduals055 8 1) 22681452
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck055_9_0 :
    integerResidualCheck 55 9 0 (dualNumerators055 9 0) ∧
    integerMassCheck 55 9 0 (dualNumerators055 9 0) := by
  apply integerChecks_of_simple 55 9 0 (dualNumerators055 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 1434332169154, 277873425546, 0, 1031321016287, 1382477552007, 63523349867, 1371924214149, 177942276579, 644784030255, 801216871619]) (branchResiduals055 9 0) 16350530
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck055_9_1 :
    integerResidualCheck 55 9 1 (dualNumerators055 9 1) ∧
    integerMassCheck 55 9 1 (dualNumerators055 9 1) := by
  apply integerChecks_of_simple 55 9 1 (dualNumerators055 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals055 9 1) 16350530
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck055_10_0 :
    integerResidualCheck 55 10 0 (dualNumerators055 10 0) ∧
    integerMassCheck 55 10 0 (dualNumerators055 10 0) := by
  apply integerChecks_of_simple 55 10 0 (dualNumerators055 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals055 10 0) 10683139
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck055_10_1 :
    integerResidualCheck 55 10 1 (dualNumerators055 10 1) ∧
    integerMassCheck 55 10 1 (dualNumerators055 10 1) := by
  apply integerChecks_of_simple 55 10 1 (dualNumerators055 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 1096480134411, 212421290928, 0, 788396879662, 1056839694908, 48560642157, 1048772159673, 136028582177, 492907358117, 612492978948]) (branchResiduals055 10 1) 10683139
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck055_11_0 :
    integerResidualCheck 55 11 0 (dualNumerators055 11 0) ∧
    integerMassCheck 55 11 0 (dualNumerators055 11 0) := by
  apply integerChecks_of_simple 55 11 0 (dualNumerators055 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 681475855631, 132022438389, 0, 489998333105, 656838836154, 30181034864, 651824764029, 84543432681, 306347970271, 380671900746]) (branchResiduals055 11 0) 15120968
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck055_11_1 :
    integerResidualCheck 55 11 1 (dualNumerators055 11 1) ∧
    integerMassCheck 55 11 1 (dualNumerators055 11 1) := by
  apply integerChecks_of_simple 55 11 1 (dualNumerators055 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 621427644954, 120389287883, 0, 446822154676, 598961515206, 27521634498, 594389257794, 77093892371, 279354134309, 347129015395]) (branchResiduals055 11 1) 15120968
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck055_12_0 :
    integerResidualCheck 55 12 0 (dualNumerators055 12 0) ∧
    integerMassCheck 55 12 0 (dualNumerators055 12 0) := by
  apply integerChecks_of_simple 55 12 0 (dualNumerators055 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1434332169154, 277873425546, 0, 1031321016287, 1382477552007, 63523349867, 1371924214149, 177942276579, 644784030255, 801216871619]) (branchResiduals055 12 0) 16348076
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck055_12_1 :
    integerResidualCheck 55 12 1 (dualNumerators055 12 1) ∧
    integerMassCheck 55 12 1 (dualNumerators055 12 1) := by
  apply integerChecks_of_simple 55 12 1 (dualNumerators055 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals055 12 1) 16348076
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck055_13_0 :
    integerResidualCheck 55 13 0 (dualNumerators055 13 0) ∧
    integerMassCheck 55 13 0 (dualNumerators055 13 0) := by
  apply integerChecks_of_simple 55 13 0 (dualNumerators055 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals055 13 0) 13962901
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck055_13_1 :
    integerResidualCheck 55 13 1 (dualNumerators055 13 1) ∧
    integerMassCheck 55 13 1 (dualNumerators055 13 1) := by
  apply integerChecks_of_simple 55 13 1 (dualNumerators055 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1211329770563, 234671131311, 0, 870976665588, 1167537235722, 53647074558, 1158624675158, 150276750182, 544536410901, 676647899379]) (branchResiduals055 13 1) 13962901
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck055_14_0 :
    integerResidualCheck 55 14 0 (dualNumerators055 14 0) ∧
    integerMassCheck 55 14 0 (dualNumerators055 14 0) := by
  apply integerChecks_of_simple 55 14 0 (dualNumerators055 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1434332169156, 277873425546, 0, 1031321016288, 1382477552008, 63523349867, 1371924214150, 177942276579, 644784030255, 801216871620]) (branchResiduals055 14 0) 20161291
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck055_14_1 :
    integerResidualCheck 55 14 1 (dualNumerators055 14 1) ∧
    integerMassCheck 55 14 1 (dualNumerators055 14 1) := by
  apply integerChecks_of_simple 55 14 1 (dualNumerators055 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 656716276290, 127225760691, 0, 472195570901, 632974376182, 29084488712, 628142476787, 81471776052, 295217646558, 366841218336]) (branchResiduals055 14 1) 20161291
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck055_15_0 :
    integerResidualCheck 55 15 0 (dualNumerators055 15 0) ∧
    integerMassCheck 55 15 0 (dualNumerators055 15 0) := by
  apply integerChecks_of_simple 55 15 0 (dualNumerators055 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 681475855631, 132022438389, 0, 489998333105, 656838836153, 30181034864, 651824764029, 84543432681, 306347970271, 380671900746]) (branchResiduals055 15 0) 12900283
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck055_15_1 :
    integerResidualCheck 55 15 1 (dualNumerators055 15 1) ∧
    integerMassCheck 55 15 1 (dualNumerators055 15 1) := by
  apply integerChecks_of_simple 55 15 1 (dualNumerators055 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals055 15 1) 12900283
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck055_16_0 :
    integerResidualCheck 55 16 0 (dualNumerators055 16 0) ∧
    integerMassCheck 55 16 0 (dualNumerators055 16 0) := by
  apply integerChecks_of_simple 55 16 0 (dualNumerators055 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals055 16 0) 10683060
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck055_16_1 :
    integerResidualCheck 55 16 1 (dualNumerators055 16 1) ∧
    integerMassCheck 55 16 1 (dualNumerators055 16 1) := by
  apply integerChecks_of_simple 55 16 1 (dualNumerators055 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 1096480134411, 212421290928, 0, 788396879662, 1056839694908, 48560642157, 1048772159673, 136028582177, 492907358117, 612492978948]) (branchResiduals055 16 1) 10683060
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck055_17_0 :
    integerResidualCheck 55 17 0 (dualNumerators055 17 0) ∧
    integerMassCheck 55 17 0 (dualNumerators055 17 0) := by
  apply integerChecks_of_simple 55 17 0 (dualNumerators055 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 893807506737, 173157486820, 0, 642670147151, 861494178583, 39584726736, 854917840966, 110885153378, 401798703857, 499280201462]) (branchResiduals055 17 0) 15120968
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck055_17_1 :
    integerResidualCheck 55 17 1 (dualNumerators055 17 1) ∧
    integerMassCheck 55 17 1 (dualNumerators055 17 1) := by
  apply integerChecks_of_simple 55 17 1 (dualNumerators055 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 621427644954, 120389287883, 0, 446822154676, 598961515206, 27521634498, 594389257794, 77093892370, 279354134309, 347129015395]) (branchResiduals055 17 1) 15120968
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck055_18_0 :
    integerResidualCheck 55 18 0 (dualNumerators055 18 0) ∧
    integerMassCheck 55 18 0 (dualNumerators055 18 0) := by
  apply integerChecks_of_simple 55 18 0 (dualNumerators055 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 975124848843, 293271850585, 0, 763999473637, 936711106099, 134481966149, 862769256399, 123780303264, 477654049462, 593539022787]) (branchResiduals055 18 0) 13565580
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck055_18_1 :
    integerResidualCheck 55 18 1 (dualNumerators055 18 1) ∧
    integerMassCheck 55 18 1 (dualNumerators055 18 1) := by
  apply integerChecks_of_simple 55 18 1 (dualNumerators055 18 1)
    (![546080038515, 100531796850, 546080038516, 0, 1, 184109219884, 218003208651, 0, 74499415779, 53134692444, 184109219884, 0, 92880591654, 504519352652, 218003208651, 0, 0, 504519352652, 178954014012, 151131188017, 846351152950, 285344710532, 82351679314, 97512391500, 184109219884, 0, 92880591654, 504519352652, 0, 0, 285344710532, 781937638598, 119604774277, 17115998234, 82351679314, 0, 115464148095, 0, 180745426040, 104599284492, 51486440059, 63977708037]) (branchResiduals055 18 1) 13565580
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck055_19_0 :
    integerResidualCheck 55 19 0 (dualNumerators055 19 0) ∧
    integerMassCheck 55 19 0 (dualNumerators055 19 0) := by
  apply integerChecks_of_simple 55 19 0 (dualNumerators055 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 737249033801, 333944038447, 0, 645216866088, 704807657121, 199841967519, 577111910116, 96603051948, 403390917798, 501258706842]) (branchResiduals055 19 0) 8248658
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck055_19_1 :
    integerResidualCheck 55 19 1 (dualNumerators055 19 1) ∧
    integerMassCheck 55 19 1 (dualNumerators055 19 1) := by
  apply integerChecks_of_simple 55 19 1 (dualNumerators055 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 668354800182, 95644673455, 131755764247, 328427706730, 645216866088, 0, 761601233763, 225876501886, 287707656866, 357509209222]) (branchResiduals055 19 1) 8248658
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck055_20_0 :
    integerResidualCheck 55 20 0 (dualNumerators055 20 0) ∧
    integerMassCheck 55 20 0 (dualNumerators055 20 0) := by
  apply integerChecks_of_simple 55 20 0 (dualNumerators055 20 0)
    (![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 2105933038876, 0, 185761786321, 1009041980816, 2493629379175, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038876, 0, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 1368099033367, 195781320438, 941979561817, 0, 1320736486917, 0, 2067456287976, 1196458760692, 588927568327, 731808918591]) (branchResiduals055 20 0) 35312013
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck055_20_1 :
    integerResidualCheck 55 20 1 (dualNumerators055 20 1) ∧
    integerMassCheck 55 20 1 (dualNumerators055 20 1) := by
  apply integerChecks_of_simple 55 20 1 (dualNumerators055 20 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 836254566552, 1355737922885, 0, 1320313360088, 769869471398, 1081323590019, 0, 135852760286, 825462640703, 1025730420714]) (branchResiduals055 20 1) 35312013
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck055_21_0 :
    integerResidualCheck 55 21 0 (dualNumerators055 21 0) ∧
    integerMassCheck 55 21 0 (dualNumerators055 21 0) := by
  apply integerChecks_of_simple 55 21 0 (dualNumerators055 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 759767979803, 549133445537, 851509250277, 798941670661, 583650214286, 725251211053]) (branchResiduals055 21 0) 11182451
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck055_21_1 :
    integerResidualCheck 55 21 1 (dualNumerators055 21 1) ∧
    integerMassCheck 55 21 1 (dualNumerators055 21 1) := by
  apply integerChecks_of_simple 55 21 1 (dualNumerators055 21 1)
    (![114087637157, 21003212630, 114087637157, 0, 1, 11738971135, 13900082653, 0, 159960694697, 114087637156, 11738971135, 0, 218966847953, 1189409008000, 13900082653, 0, 0, 1189409008001, 1568336550649, 324499857786, 176820605835, 18193837997, 176820605835, 209372781287, 11738971135, 0, 218966847953, 1189409008000, 0, 0, 18193837997, 1843425165269, 918700010035, 924725155234, 0, 176820605835, 103103392317, 144814328227, 0, 18193837997, 110548608107, 137369112437]) (branchResiduals055 21 1) 11182451
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck055_22_0 :
    integerResidualCheck 55 22 0 (dualNumerators055 22 0) ∧
    integerMassCheck 55 22 0 (dualNumerators055 22 0) := by
  apply integerChecks_of_simple 55 22 0 (dualNumerators055 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 179826715678, 584172757959, 460183470977, 0, 216080085359, 429136780729, 256292246333, 545043834385, 287707656866, 357509209222]) (branchResiduals055 22 0) 6465674
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck055_22_1 :
    integerResidualCheck 55 22 1 (dualNumerators055 22 1) ∧
    integerMassCheck 55 22 1 (dualNumerators055 22 1) := by
  apply integerChecks_of_simple 55 22 1 (dualNumerators055 22 1)
    (![50594765625, 9314353833, 50594765625, 0, 0, 5205914576, 6164308785, 0, 70938219592, 50594765625, 5205914576, 0, 15463748427, 83997745994, 6164308785, 0, 0, 83997745994, 1170399714012, 143906865451, 78415131848, 8068472555, 78415131848, 92851136735, 5205914576, 0, 15463748427, 83997745994, 0, 0, 8068472555, 130185291813, 109057552771, 21127739043, 0, 78415131848, 45723551643, 64221217814, 0, 8068472555, 49025302449, 60919467008]) (branchResiduals055 22 1) 6465674
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck055_23_0 :
    integerResidualCheck 55 23 0 (dualNumerators055 23 0) ∧
    integerMassCheck 55 23 0 (dualNumerators055 23 0) := by
  apply integerChecks_of_simple 55 23 0 (dualNumerators055 23 0)
    (![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 2105933038876, 0, 185761786321, 1009041980816, 2493629379175, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038876, 0, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 368099033367, 1195781320438, 941979561817, 0, 1320736486917, 0, 2067456287976, 1196458760692, 588927568327, 731808918591]) (branchResiduals055 23 0) 35297932
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck055_23_1 :
    integerResidualCheck 55 23 1 (dualNumerators055 23 1) ∧
    integerMassCheck 55 23 1 (dualNumerators055 23 1) := by
  apply integerChecks_of_simple 55 23 1 (dualNumerators055 23 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 1836254566552, 355737922885, 0, 1320313360088, 769869471398, 1081323590019, 0, 135852760286, 825462640703, 1025730420714]) (branchResiduals055 23 1) 35297932
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck055_24_0 :
    integerResidualCheck 55 24 0 (dualNumerators055 24 0) ∧
    integerMassCheck 55 24 0 (dualNumerators055 24 0) := by
  apply integerChecks_of_simple 55 24 0 (dualNumerators055 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 512185690040, 559007382209, 569308312247, 737522866658, 477654049462, 593539022787]) (branchResiduals055 24 0) 9356857
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck055_24_1 :
    integerResidualCheck 55 24 1 (dualNumerators055 24 1) ∧
    integerMassCheck 55 24 1 (dualNumerators055 24 1) := by
  apply integerChecks_of_simple 55 24 1 (dualNumerators055 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 587483804282, 282115266095, 66021086067, 82038644814, 0, 0, 66021086067, 82038644814]) (branchResiduals055 24 1) 9356857
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck055_25_0 :
    integerResidualCheck 55 25 0 (dualNumerators055 25 0) ∧
    integerMassCheck 55 25 0 (dualNumerators055 25 0) := by
  apply integerChecks_of_simple 55 25 0 (dualNumerators055 25 0)
    (![30936264063, 5695279071, 30936264063, 0, 1, 16941043971, 20059842445, 0, 627070502755, 447241068346, 509886390043, 0, 136694444206, 742512415929, 603755038162, 0, 0, 742512415929, 1506277362888, 1272089305134, 47947079019, 26256356369, 693163945107, 820773474842, 509886390043, 0, 136694444206, 742512415929, 0, 0, 790255830005, 1150795112397, 483731503338, 667063609060, 47947079019, 0, 448879356988, 522996202554, 26256356369, 0, 433367530667, 538508028875]) (branchResiduals055 25 0) 8671199
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck055_25_1 :
    integerResidualCheck 55 25 1 (dualNumerators055 25 1) ∧
    integerMassCheck 55 25 1 (dualNumerators055 25 1) := by
  apply integerChecks_of_simple 55 25 1 (dualNumerators055 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 415529968297, 599898615461, 0, 0]) (branchResiduals055 25 1) 8671199
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck055_26_0 :
    integerResidualCheck 55 26 0 (dualNumerators055 26 0) ∧
    integerMassCheck 55 26 0 (dualNumerators055 26 0) := by
  apply integerChecks_of_simple 55 26 0 (dualNumerators055 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0]) (branchResiduals055 26 0) 15099566
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck055_26_1 :
    integerResidualCheck 55 26 1 (dualNumerators055 26 1) ∧
    integerMassCheck 55 26 1 (dualNumerators055 26 1) := by
  apply integerChecks_of_simple 55 26 1 (dualNumerators055 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 879744679617, 350168760452, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals055 26 1) 15099566
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck055_27_0 :
    integerResidualCheck 55 27 0 (dualNumerators055 27 0) ∧
    integerMassCheck 55 27 0 (dualNumerators055 27 0) := by
  apply integerChecks_of_simple 55 27 0 (dualNumerators055 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 286173900105, 455299762271, 340673826058, 423325647580]) (branchResiduals055 27 0) 7338775
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck055_27_1 :
    integerResidualCheck 55 27 1 (dualNumerators055 27 1) ∧
    integerMassCheck 55 27 1 (dualNumerators055 27 1) := by
  apply integerChecks_of_simple 55 27 1 (dualNumerators055 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 918185996600, 613751944609, 0, 377837583379, 871790834897, 421969477217, 576174693322, 69042172766, 236224837801, 293536000677]) (branchResiduals055 27 1) 7338775
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck055_28_0 :
    integerResidualCheck 55 28 0 (dualNumerators055 28 0) ∧
    integerMassCheck 55 28 0 (dualNumerators055 28 0) := by
  apply integerChecks_of_simple 55 28 0 (dualNumerators055 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 450383711774, 395438493575, 287707656866, 357509209222]) (branchResiduals055 28 0) 10335557
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck055_28_1 :
    integerResidualCheck 55 28 1 (dualNumerators055 28 1) ∧
    integerMassCheck 55 28 1 (dualNumerators055 28 1) := by
  apply integerChecks_of_simple 55 28 1 (dualNumerators055 28 1)
    (![71098470185, 13089028086, 71098470186, 0, 1, 500260975618, 592357612055, 0, 99686179557, 71098470185, 7315629546, 0, 112480335850, 610983470480, 8662416338, 0, 0, 610983470481, 1239454790169, 202225622679, 110193136482, 775337722729, 110193136482, 130479382508, 7315629546, 0, 112480335850, 610983470480, 0, 0, 11338249092, 946942807286, 484898704770, 462044102516, 0, 110193136482, 456220281523, 343496853848, 0, 11338249092, 68892976605, 85607292678]) (branchResiduals055 28 1) 10335557
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck055_29_0 :
    integerResidualCheck 55 29 0 (dualNumerators055 29 0) ∧
    integerMassCheck 55 29 0 (dualNumerators055 29 0) := by
  apply integerChecks_of_simple 55 29 0 (dualNumerators055 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0]) (branchResiduals055 29 0) 40352153
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck055_29_1 :
    integerResidualCheck 55 29 1 (dualNumerators055 29 1) ∧
    integerMassCheck 55 29 1 (dualNumerators055 29 1) := by
  apply integerChecks_of_simple 55 29 1 (dualNumerators055 29 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 1836254566552, 355737922885, 0, 1320313360088, 1769869471398, 81323590019, 0, 135852760286, 825462640703, 1025730420714]) (branchResiduals055 29 1) 40352153
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck055_30_0 :
    integerResidualCheck 55 30 0 (dualNumerators055 30 0) ∧
    integerMassCheck 55 30 0 (dualNumerators055 30 0) := by
  apply integerChecks_of_simple 55 30 0 (dualNumerators055 30 0)
    (![50594765625, 9314353833, 50594765625, 0, 0, 5205914576, 6164308785, 0, 70938219592, 50594765625, 5205914576, 0, 15463748427, 83997745994, 6164308785, 0, 0, 83997745994, 170399714012, 1143906865451, 78415131848, 8068472555, 78415131848, 92851136735, 5205914576, 0, 15463748427, 83997745994, 0, 0, 8068472555, 130185291813, 109057552771, 21127739043, 0, 78415131848, 105114855418, 4829914039, 0, 8068472555, 108416606224, 1528163233]) (branchResiduals055 30 0) 7680628
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck055_30_1 :
    integerResidualCheck 55 30 1 (dualNumerators055 30 1) ∧
    integerMassCheck 55 30 1 (dualNumerators055 30 1) := by
  apply integerChecks_of_simple 55 30 1 (dualNumerators055 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 757834259187, 146815365454, 0, 544901951702, 730436696602, 33562777035, 829173251111, 99477537975, 281282522283, 482716951355]) (branchResiduals055 30 1) 7680628
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck055_31_0 :
    integerResidualCheck 55 31 0 (dualNumerators055 31 0) ∧
    integerMassCheck 55 31 0 (dualNumerators055 31 0) := by
  apply integerChecks_of_simple 55 31 0 (dualNumerators055 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 1032415642125, 1, 592902192609, 0, 1222480453651, 0, 500720887661, 0, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642125, 0, 592902192609, 0, 0, 0, 1600106408231, 776050524992, 678897187053, 97153337939, 711927549445, 860915026216, 655394283556, 0, 654789687546, 945316720686, 655394283556, 0]) (branchResiduals055 31 0) 32891612
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck055_31_1 :
    integerResidualCheck 55 31 1 (dualNumerators055 31 1) ∧
    integerMassCheck 55 31 1 (dualNumerators055 31 1) := by
  apply integerChecks_of_simple 55 31 1 (dualNumerators055 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 741061026801, 808805463926, 725570984152, 37986262977, 327950144489, 1221916346239]) (branchResiduals055 31 1) 32891612
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck055_32_0 :
    integerResidualCheck 55 32 0 (dualNumerators055 32 0) ∧
    integerMassCheck 55 32 0 (dualNumerators055 32 0) := by
  apply integerChecks_of_simple 55 32 0 (dualNumerators055 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 0, 2743468108582, 2028778803022, 0, 505064750776, 2743468108580, 1713354977902, 2, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 2028778803022, 0, 0, 0, 4252009289869, 2655471466972, 2224515654627, 430955812345, 0, 1599482877825, 2144093971220, 98518801469, 3884085649292, 367923640577, 0, 2242612772688]) (branchResiduals055 32 0) 67647473
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck055_32_1 :
    integerResidualCheck 55 32 1 (dualNumerators055 32 1) ∧
    integerMassCheck 55 32 1 (dualNumerators055 32 1) := by
  apply integerChecks_of_simple 55 32 1 (dualNumerators055 32 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 1836254566552, 355737922885, 0, 1320313360088, 1769869471398, 81323590019, 0, 135852760286, 1825462640703, 25730420714]) (branchResiduals055 32 1) 67647473
    branchSparseDots055 branchIntegerCurvature055 branchDots055
    branchIntegerCurvature055_entry rfl
    (congrFun (congrFun branchResiduals055_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks055 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 55 j s (dualNumerators055 j s) ∧
    integerMassCheck 55 j s (dualNumerators055 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck055_0_0
    · exact integerCheck055_0_1
  · fin_cases s
    · exact integerCheck055_1_0
    · exact integerCheck055_1_1
  · fin_cases s
    · exact integerCheck055_2_0
    · exact integerCheck055_2_1
  · fin_cases s
    · exact integerCheck055_3_0
    · exact integerCheck055_3_1
  · fin_cases s
    · exact integerCheck055_4_0
    · exact integerCheck055_4_1
  · fin_cases s
    · exact integerCheck055_5_0
    · exact integerCheck055_5_1
  · fin_cases s
    · exact integerCheck055_6_0
    · exact integerCheck055_6_1
  · fin_cases s
    · exact integerCheck055_7_0
    · exact integerCheck055_7_1
  · fin_cases s
    · exact integerCheck055_8_0
    · exact integerCheck055_8_1
  · fin_cases s
    · exact integerCheck055_9_0
    · exact integerCheck055_9_1
  · fin_cases s
    · exact integerCheck055_10_0
    · exact integerCheck055_10_1
  · fin_cases s
    · exact integerCheck055_11_0
    · exact integerCheck055_11_1
  · fin_cases s
    · exact integerCheck055_12_0
    · exact integerCheck055_12_1
  · fin_cases s
    · exact integerCheck055_13_0
    · exact integerCheck055_13_1
  · fin_cases s
    · exact integerCheck055_14_0
    · exact integerCheck055_14_1
  · fin_cases s
    · exact integerCheck055_15_0
    · exact integerCheck055_15_1
  · fin_cases s
    · exact integerCheck055_16_0
    · exact integerCheck055_16_1
  · fin_cases s
    · exact integerCheck055_17_0
    · exact integerCheck055_17_1
  · fin_cases s
    · exact integerCheck055_18_0
    · exact integerCheck055_18_1
  · fin_cases s
    · exact integerCheck055_19_0
    · exact integerCheck055_19_1
  · fin_cases s
    · exact integerCheck055_20_0
    · exact integerCheck055_20_1
  · fin_cases s
    · exact integerCheck055_21_0
    · exact integerCheck055_21_1
  · fin_cases s
    · exact integerCheck055_22_0
    · exact integerCheck055_22_1
  · fin_cases s
    · exact integerCheck055_23_0
    · exact integerCheck055_23_1
  · fin_cases s
    · exact integerCheck055_24_0
    · exact integerCheck055_24_1
  · fin_cases s
    · exact integerCheck055_25_0
    · exact integerCheck055_25_1
  · fin_cases s
    · exact integerCheck055_26_0
    · exact integerCheck055_26_1
  · fin_cases s
    · exact integerCheck055_27_0
    · exact integerCheck055_27_1
  · fin_cases s
    · exact integerCheck055_28_0
    · exact integerCheck055_28_1
  · fin_cases s
    · exact integerCheck055_29_0
    · exact integerCheck055_29_1
  · fin_cases s
    · exact integerCheck055_30_0
    · exact integerCheck055_30_1
  · fin_cases s
    · exact integerCheck055_31_0
    · exact integerCheck055_31_1
  · fin_cases s
    · exact integerCheck055_32_0
    · exact integerCheck055_32_1

end ElevenSquare.Tasks.T06
