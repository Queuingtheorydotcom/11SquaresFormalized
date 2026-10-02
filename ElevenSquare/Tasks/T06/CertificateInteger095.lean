import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual095
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
import ElevenSquare.Tasks.T06.SparseColumn35
import ElevenSquare.Tasks.T06.SparseColumn36
import ElevenSquare.Tasks.T06.SparseColumn38
import ElevenSquare.Tasks.T06.SparseColumn39
import ElevenSquare.Tasks.T06.SparseColumn41
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn47
import ElevenSquare.Tasks.T06.SparseColumn51
import ElevenSquare.Tasks.T06.SparseColumn55
import ElevenSquare.Tasks.T06.SparseColumn57

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix095 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix095_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = branchIntegerMatrix095 := by
  change roundedGradients ∘ branchRows 95 = branchIntegerMatrix095
  rw [show branchRows 95 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 54, 55, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix095]

theorem branchColumn095_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 0) i) = _
  rw [branchColumn095_0]
  exact sparseColumn00_sum n

theorem branchColumn095_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 1) i) = _
  rw [branchColumn095_1]
  exact sparseColumn01_sum n

theorem branchColumn095_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 2) i) = _
  rw [branchColumn095_2]
  exact sparseColumn02_sum n

theorem branchColumn095_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 3) i) = _
  rw [branchColumn095_3]
  exact sparseColumn03_sum n

theorem branchColumn095_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 4) i) = _
  rw [branchColumn095_4]
  exact sparseColumn04_sum n

theorem branchColumn095_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 5) i) = _
  rw [branchColumn095_5]
  exact sparseColumn05_sum n

theorem branchColumn095_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 6) i) = _
  rw [branchColumn095_6]
  exact sparseColumn06_sum n

theorem branchColumn095_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 7) i) = _
  rw [branchColumn095_7]
  exact sparseColumn07_sum n

theorem branchColumn095_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 8) i) = _
  rw [branchColumn095_8]
  exact sparseColumn08_sum n

theorem branchColumn095_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 9) i) = _
  rw [branchColumn095_9]
  exact sparseColumn09_sum n

theorem branchColumn095_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 10) i) = _
  rw [branchColumn095_10]
  exact sparseColumn10_sum n

theorem branchColumn095_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 11) i) = _
  rw [branchColumn095_11]
  exact sparseColumn11_sum n

theorem branchColumn095_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 12) i) = _
  rw [branchColumn095_12]
  exact sparseColumn35_sum n

theorem branchColumn095_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 13) i) = _
  rw [branchColumn095_13]
  exact sparseColumn36_sum n

theorem branchColumn095_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 14) i) = _
  rw [branchColumn095_14]
  exact sparseColumn41_sum n

theorem branchColumn095_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 15) i) = _
  rw [branchColumn095_15]
  exact sparseColumn38_sum n

theorem branchColumn095_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 16) i) = _
  rw [branchColumn095_16]
  exact sparseColumn39_sum n

theorem branchColumn095_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 17) i) = _
  rw [branchColumn095_17]
  exact sparseColumn17_sum n

theorem branchColumn095_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 18) i) = _
  rw [branchColumn095_18]
  exact sparseColumn18_sum n

theorem branchColumn095_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 19) i) = _
  rw [branchColumn095_19]
  exact sparseColumn19_sum n

theorem branchColumn095_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 20) = sparseColumn55 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 20) = sparseDot55 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 20) i) = _
  rw [branchColumn095_20]
  exact sparseColumn55_sum n

theorem branchColumn095_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 21) i) = _
  rw [branchColumn095_21]
  exact sparseColumn21_sum n

theorem branchColumn095_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 22) i) = _
  rw [branchColumn095_22]
  exact sparseColumn22_sum n

theorem branchColumn095_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 23) = sparseColumn47 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 23) = sparseDot47 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 23) i) = _
  rw [branchColumn095_23]
  exact sparseColumn47_sum n

theorem branchColumn095_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 24) i) = _
  rw [branchColumn095_24]
  exact sparseColumn24_sum n

theorem branchColumn095_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 25) i) = _
  rw [branchColumn095_25]
  exact sparseColumn25_sum n

theorem branchColumn095_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 26) = sparseColumn57 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 26) = sparseDot57 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 26) i) = _
  rw [branchColumn095_26]
  exact sparseColumn57_sum n

theorem branchColumn095_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 27) i) = _
  rw [branchColumn095_27]
  exact sparseColumn27_sum n

theorem branchColumn095_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 28) i) = _
  rw [branchColumn095_28]
  exact sparseColumn28_sum n

theorem branchColumn095_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 29) = sparseColumn51 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 29) = sparseDot51 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 29) i) = _
  rw [branchColumn095_29]
  exact sparseColumn51_sum n

theorem branchColumn095_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 30) i) = _
  rw [branchColumn095_30]
  exact sparseColumn30_sum n

theorem branchColumn095_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 31) i) = _
  rw [branchColumn095_31]
  exact sparseColumn31_sum n

theorem branchColumn095_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 95 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 95 i)) = _
  rw [branchIntegerMatrix095_eq]
  simp only [branchIntegerMatrix095, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot095_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 95 i) 32) i) = _
  rw [branchColumn095_32]
  exact sparseColumn43_sum n

def branchSparseDots095 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot55, sparseDot21, sparseDot22, sparseDot47, sparseDot24, sparseDot25, sparseDot57, sparseDot27, sparseDot28, sparseDot51, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot095_0 :
    branchSparseDots095 0 = sparseDot00 := rfl

private theorem branchSparseDot095_1 :
    branchSparseDots095 1 = sparseDot01 := rfl

private theorem branchSparseDot095_2 :
    branchSparseDots095 2 = sparseDot02 := rfl

private theorem branchSparseDot095_3 :
    branchSparseDots095 3 = sparseDot03 := rfl

private theorem branchSparseDot095_4 :
    branchSparseDots095 4 = sparseDot04 := rfl

private theorem branchSparseDot095_5 :
    branchSparseDots095 5 = sparseDot05 := rfl

private theorem branchSparseDot095_6 :
    branchSparseDots095 6 = sparseDot06 := rfl

private theorem branchSparseDot095_7 :
    branchSparseDots095 7 = sparseDot07 := rfl

private theorem branchSparseDot095_8 :
    branchSparseDots095 8 = sparseDot08 := rfl

private theorem branchSparseDot095_9 :
    branchSparseDots095 9 = sparseDot09 := rfl

private theorem branchSparseDot095_10 :
    branchSparseDots095 10 = sparseDot10 := rfl

private theorem branchSparseDot095_11 :
    branchSparseDots095 11 = sparseDot11 := rfl

private theorem branchSparseDot095_12 :
    branchSparseDots095 12 = sparseDot35 := rfl

private theorem branchSparseDot095_13 :
    branchSparseDots095 13 = sparseDot36 := rfl

private theorem branchSparseDot095_14 :
    branchSparseDots095 14 = sparseDot41 := rfl

private theorem branchSparseDot095_15 :
    branchSparseDots095 15 = sparseDot38 := rfl

private theorem branchSparseDot095_16 :
    branchSparseDots095 16 = sparseDot39 := rfl

private theorem branchSparseDot095_17 :
    branchSparseDots095 17 = sparseDot17 := rfl

private theorem branchSparseDot095_18 :
    branchSparseDots095 18 = sparseDot18 := rfl

private theorem branchSparseDot095_19 :
    branchSparseDots095 19 = sparseDot19 := rfl

private theorem branchSparseDot095_20 :
    branchSparseDots095 20 = sparseDot55 := rfl

private theorem branchSparseDot095_21 :
    branchSparseDots095 21 = sparseDot21 := rfl

private theorem branchSparseDot095_22 :
    branchSparseDots095 22 = sparseDot22 := rfl

private theorem branchSparseDot095_23 :
    branchSparseDots095 23 = sparseDot47 := rfl

private theorem branchSparseDot095_24 :
    branchSparseDots095 24 = sparseDot24 := rfl

private theorem branchSparseDot095_25 :
    branchSparseDots095 25 = sparseDot25 := rfl

private theorem branchSparseDot095_26 :
    branchSparseDots095 26 = sparseDot57 := rfl

private theorem branchSparseDot095_27 :
    branchSparseDots095 27 = sparseDot27 := rfl

private theorem branchSparseDot095_28 :
    branchSparseDots095 28 = sparseDot28 := rfl

private theorem branchSparseDot095_29 :
    branchSparseDots095 29 = sparseDot51 := rfl

private theorem branchSparseDot095_30 :
    branchSparseDots095 30 = sparseDot30 := rfl

private theorem branchSparseDot095_31 :
    branchSparseDots095 31 = sparseDot31 := rfl

private theorem branchSparseDot095_32 :
    branchSparseDots095 32 = sparseDot43 := rfl

theorem branchDots095 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 95 i) k) = branchSparseDots095 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot095_0 n
      _ = _ := congrFun branchSparseDot095_0.symm n
  · calc
      _ = sparseDot01 n := branchDot095_1 n
      _ = _ := congrFun branchSparseDot095_1.symm n
  · calc
      _ = sparseDot02 n := branchDot095_2 n
      _ = _ := congrFun branchSparseDot095_2.symm n
  · calc
      _ = sparseDot03 n := branchDot095_3 n
      _ = _ := congrFun branchSparseDot095_3.symm n
  · calc
      _ = sparseDot04 n := branchDot095_4 n
      _ = _ := congrFun branchSparseDot095_4.symm n
  · calc
      _ = sparseDot05 n := branchDot095_5 n
      _ = _ := congrFun branchSparseDot095_5.symm n
  · calc
      _ = sparseDot06 n := branchDot095_6 n
      _ = _ := congrFun branchSparseDot095_6.symm n
  · calc
      _ = sparseDot07 n := branchDot095_7 n
      _ = _ := congrFun branchSparseDot095_7.symm n
  · calc
      _ = sparseDot08 n := branchDot095_8 n
      _ = _ := congrFun branchSparseDot095_8.symm n
  · calc
      _ = sparseDot09 n := branchDot095_9 n
      _ = _ := congrFun branchSparseDot095_9.symm n
  · calc
      _ = sparseDot10 n := branchDot095_10 n
      _ = _ := congrFun branchSparseDot095_10.symm n
  · calc
      _ = sparseDot11 n := branchDot095_11 n
      _ = _ := congrFun branchSparseDot095_11.symm n
  · calc
      _ = sparseDot35 n := branchDot095_12 n
      _ = _ := congrFun branchSparseDot095_12.symm n
  · calc
      _ = sparseDot36 n := branchDot095_13 n
      _ = _ := congrFun branchSparseDot095_13.symm n
  · calc
      _ = sparseDot41 n := branchDot095_14 n
      _ = _ := congrFun branchSparseDot095_14.symm n
  · calc
      _ = sparseDot38 n := branchDot095_15 n
      _ = _ := congrFun branchSparseDot095_15.symm n
  · calc
      _ = sparseDot39 n := branchDot095_16 n
      _ = _ := congrFun branchSparseDot095_16.symm n
  · calc
      _ = sparseDot17 n := branchDot095_17 n
      _ = _ := congrFun branchSparseDot095_17.symm n
  · calc
      _ = sparseDot18 n := branchDot095_18 n
      _ = _ := congrFun branchSparseDot095_18.symm n
  · calc
      _ = sparseDot19 n := branchDot095_19 n
      _ = _ := congrFun branchSparseDot095_19.symm n
  · calc
      _ = sparseDot55 n := branchDot095_20 n
      _ = _ := congrFun branchSparseDot095_20.symm n
  · calc
      _ = sparseDot21 n := branchDot095_21 n
      _ = _ := congrFun branchSparseDot095_21.symm n
  · calc
      _ = sparseDot22 n := branchDot095_22 n
      _ = _ := congrFun branchSparseDot095_22.symm n
  · calc
      _ = sparseDot47 n := branchDot095_23 n
      _ = _ := congrFun branchSparseDot095_23.symm n
  · calc
      _ = sparseDot24 n := branchDot095_24 n
      _ = _ := congrFun branchSparseDot095_24.symm n
  · calc
      _ = sparseDot25 n := branchDot095_25 n
      _ = _ := congrFun branchSparseDot095_25.symm n
  · calc
      _ = sparseDot57 n := branchDot095_26 n
      _ = _ := congrFun branchSparseDot095_26.symm n
  · calc
      _ = sparseDot27 n := branchDot095_27 n
      _ = _ := congrFun branchSparseDot095_27.symm n
  · calc
      _ = sparseDot28 n := branchDot095_28 n
      _ = _ := congrFun branchSparseDot095_28.symm n
  · calc
      _ = sparseDot51 n := branchDot095_29 n
      _ = _ := congrFun branchSparseDot095_29.symm n
  · calc
      _ = sparseDot30 n := branchDot095_30 n
      _ = _ := congrFun branchSparseDot095_30.symm n
  · calc
      _ = sparseDot31 n := branchDot095_31 n
      _ = _ := congrFun branchSparseDot095_31.symm n
  · calc
      _ = sparseDot43 n := branchDot095_32 n
      _ = _ := congrFun branchSparseDot095_32.symm n

def branchIntegerCurvature095 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101981296, 101981296, 79086693, 79086693, 106371291, 106371291, 88123140, 88123140, 289103692, 289103692]

theorem branchIntegerCurvature095_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 95 i)) = branchIntegerCurvature095 := by
  change curvatureNumerators ∘ branchRows 95 = branchIntegerCurvature095
  rw [show branchRows 95 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 54, 55, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature095_entry (i : Fin 42) :
    curvatureNumerators (branchRows 95 i) = branchIntegerCurvature095 i :=
  congrFun branchIntegerCurvature095_eq i

def branchResiduals095 : Fin 33 → Fin 2 → ℕ := ![![1297565975360340, 33000000000000], ![1544514594487470, 33000000000000], ![1581539058914914, 1336679166854766], ![33000000000000, 1022396486393496], ![854644144614054, 33000000000000], ![1055372881583803, 893555090351787], ![720684911205881, 624798065222648], ![33000000000000, 762914491067486], ![1579326946298457, 1127412779189880], ![1023877218639115, 33000000000000], ![33000000000000, 776990022433660], ![506439599915230, 465731538416614], ![988475531204613, 66000000000000], ![33000000000000, 857382467182309], ![1055333143787403, 485300919860411], ![471239952661726, 33000000000000], ![66000000000000, 743479019228235], ![659238669079673, 464670881179528], ![622025083477463, 268267612633314], ![630797423496172, 511570728876640], ![1474116175544279, 851858990529808], ![751104335538261, 374549059863808], ![471055853251425, 90602725914513], ![1474116175544279, 851858990529808], ![671310974030878, 230313982650212], ![508596188202063, 218713669397988], ![398805840068707, 851858990529808], ![407851233060713, 545645408385546], ![285139865366158, 298620828727661], ![398805840068707, 891219687505299], ![96761882902073, 550677939267354], ![966829345481371, 648710695287693], ![2018497587553951, 920579729933358]]

theorem branchResiduals095_eq : residualNumerators 95 = branchResiduals095 := rfl

theorem integerCheck095_0_0 :
    integerResidualCheck 95 0 0 (dualNumerators095 0 0) ∧
    integerMassCheck 95 0 0 (dualNumerators095 0 0) := by
  apply integerChecks_of_simple 95 0 0 (dualNumerators095 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1452036338470, 721009985597, 1308901425339, 0, 601145163368, 1234047382517, 1330333654477, 636679939507, 818327875519, 1016864670366]) (branchResiduals095 0 0) 18767167
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck095_0_1 :
    integerResidualCheck 95 0 1 (dualNumerators095 0 1) ∧
    integerMassCheck 95 0 1 (dualNumerators095 0 1) := by
  apply integerChecks_of_simple 95 0 1 (dualNumerators095 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals095 0 1) 18767167
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck095_1_0 :
    integerResidualCheck 95 1 0 (dualNumerators095 1 0) ∧
    integerMassCheck 95 1 0 (dualNumerators095 1 0) := by
  apply integerChecks_of_simple 95 1 0 (dualNumerators095 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 1719352138172, 853745892948, 1549866490727, 0, 711814294591, 1461232029476, 1575244332878, 753890922920, 968979732271, 1204066591796]) (branchResiduals095 1 0) 22176635
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck095_1_1 :
    integerResidualCheck 95 1 1 (dualNumerators095 1 1) ∧
    integerMassCheck 95 1 1 (dualNumerators095 1 1) := by
  apply integerChecks_of_simple 95 1 1 (dualNumerators095 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals095 1 1) 22176635
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck095_2_0 :
    integerResidualCheck 95 2 0 (dualNumerators095 2 0) ∧
    integerMassCheck 95 2 0 (dualNumerators095 2 0) := by
  apply integerChecks_of_simple 95 2 0 (dualNumerators095 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 1719352138173, 853745892949, 1549866490728, 0, 711814294592, 1461232029477, 1575244332879, 753890922921, 968979732272, 1204066591797]) (branchResiduals095 2 0) 22681452
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck095_2_1 :
    integerResidualCheck 95 2 1 (dualNumerators095 2 1) ∧
    integerMassCheck 95 2 1 (dualNumerators095 2 1) := by
  apply integerChecks_of_simple 95 2 1 (dualNumerators095 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1452036338469, 721009985597, 1308901425338, 0, 601145163368, 1234047382516, 1330333654476, 636679939507, 818327875518, 1016864670365]) (branchResiduals095 2 1) 22681452
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck095_3_0 :
    integerResidualCheck 95 3 0 (dualNumerators095 3 0) ∧
    integerMassCheck 95 3 0 (dualNumerators095 3 0) := by
  apply integerChecks_of_simple 95 3 0 (dualNumerators095 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals095 3 0) 16360330
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck095_3_1 :
    integerResidualCheck 95 3 1 (dualNumerators095 3 1) ∧
    integerMassCheck 95 3 1 (dualNumerators095 3 1) := by
  apply integerChecks_of_simple 95 3 1 (dualNumerators095 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000001, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000001, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1144101124261, 568104470439, 1031321016287, 0, 473659535255, 972341366619, 1048208085022, 501658405706, 644784030255, 801216871619]) (branchResiduals095 3 1) 16360330
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck095_4_0 :
    integerResidualCheck 95 4 0 (dualNumerators095 4 0) ∧
    integerMassCheck 95 4 0 (dualNumerators095 4 0) := by
  apply integerChecks_of_simple 95 4 0 (dualNumerators095 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000001, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 966222317365, 479778584509, 870976665588, 0, 400017449587, 821166860693, 885238221966, 423663203373, 544536410901, 676647899379]) (branchResiduals095 4 0) 13760362
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck095_4_1 :
    integerResidualCheck 95 4 1 (dualNumerators095 4 1) ∧
    integerMassCheck 95 4 1 (dualNumerators095 4 1) := by
  apply integerChecks_of_simple 95 4 1 (dualNumerators095 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals095 4 1) 13760362
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck095_5_0 :
    integerResidualCheck 95 5 0 (dualNumerators095 5 0) ∧
    integerMassCheck 95 5 0 (dualNumerators095 5 0) := by
  apply integerChecks_of_simple 95 5 0 (dualNumerators095 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1144101124262, 568104470440, 1031321016288, 0, 473659535256, 972341366620, 1048208085022, 501658405707, 644784030255, 801216871620]) (branchResiduals095 5 0) 17641130
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck095_5_1 :
    integerResidualCheck 95 5 1 (dualNumerators095 5 1) ∧
    integerMassCheck 95 5 1 (dualNumerators095 5 1) := by
  apply integerChecks_of_simple 95 5 1 (dualNumerators095 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 966222317364, 479778584509, 870976665588, 0, 400017449587, 821166860692, 885238221966, 423663203373, 544536410901, 676647899378]) (branchResiduals095 5 1) 17641130
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck095_6_0 :
    integerResidualCheck 95 6 0 (dualNumerators095 6 0) ∧
    integerMassCheck 95 6 0 (dualNumerators095 6 0) := by
  apply integerChecks_of_simple 95 6 0 (dualNumerators095 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 877488274356, 957704271528, 2719950702, 106626845062, 818327875519, 1016864670366]) (branchResiduals095 6 0) 8962451
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck095_6_1 :
    integerResidualCheck 95 6 1 (dualNumerators095 6 1) ∧
    integerMassCheck 95 6 1 (dualNumerators095 6 1) := by
  apply integerChecks_of_simple 95 6 1 (dualNumerators095 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals095 6 1) 8962451
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck095_7_0 :
    integerResidualCheck 95 7 0 (dualNumerators095 7 0) ∧
    integerMassCheck 95 7 0 (dualNumerators095 7 0) := by
  apply integerChecks_of_simple 95 7 0 (dualNumerators095 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals095 7 0) 10424794
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck095_7_1 :
    integerResidualCheck 95 7 1 (dualNumerators095 7 1) ∧
    integerMassCheck 95 7 1 (dualNumerators095 7 1) := by
  apply integerChecks_of_simple 95 7 1 (dualNumerators095 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 859676069088, 426872946475, 774933245365, 0, 355907147296, 730616014740, 787622166441, 376945461461, 484489866137, 602033295899]) (branchResiduals095 7 1) 10424794
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck095_8_0 :
    integerResidualCheck 95 8 0 (dualNumerators095 8 0) ∧
    integerMassCheck 95 8 0 (dualNumerators095 8 0) := by
  apply integerChecks_of_simple 95 8 0 (dualNumerators095 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 1719352138175, 853745892950, 1549866490730, 0, 711814294592, 1461232029479, 1575244332881, 753890922921, 968979732273, 1204066591798]) (branchResiduals095 8 0) 22681452
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck095_8_1 :
    integerResidualCheck 95 8 1 (dualNumerators095 8 1) ∧
    integerMassCheck 95 8 1 (dualNumerators095 8 1) := by
  apply integerChecks_of_simple 95 8 1 (dualNumerators095 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1226281389033, 608911156849, 1105400337063, 0, 507682284813, 1042184205913, 1123500396284, 537692301428, 691098574663, 858767916063]) (branchResiduals095 8 1) 22681452
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck095_9_0 :
    integerResidualCheck 95 9 0 (dualNumerators095 9 0) ∧
    integerMassCheck 95 9 0 (dualNumerators095 9 0) := by
  apply integerChecks_of_simple 95 9 0 (dualNumerators095 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 1144101124261, 568104470439, 1031321016287, 0, 473659535255, 972341366619, 1048208085022, 501658405706, 644784030255, 801216871619]) (branchResiduals095 9 0) 16350530
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck095_9_1 :
    integerResidualCheck 95 9 1 (dualNumerators095 9 1) ∧
    integerMassCheck 95 9 1 (dualNumerators095 9 1) := by
  apply integerChecks_of_simple 95 9 1 (dualNumerators095 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals095 9 1) 16350530
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck095_10_0 :
    integerResidualCheck 95 10 0 (dualNumerators095 10 0) ∧
    integerMassCheck 95 10 0 (dualNumerators095 10 0) := by
  apply integerChecks_of_simple 95 10 0 (dualNumerators095 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals095 10 0) 10683139
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck095_10_1 :
    integerResidualCheck 95 10 1 (dualNumerators095 10 1) ∧
    integerMassCheck 95 10 1 (dualNumerators095 10 1) := by
  apply integerChecks_of_simple 95 10 1 (dualNumerators095 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 874612019090, 434289406250, 788396879662, 0, 362090652396, 743309684668, 801306257136, 383494484713, 492907358117, 612492978948]) (branchResiduals095 10 1) 10683139
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck095_11_0 :
    integerResidualCheck 95 11 0 (dualNumerators095 11 0) ∧
    integerMassCheck 95 11 0 (dualNumerators095 11 0) := by
  apply integerChecks_of_simple 95 11 0 (dualNumerators095 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 543582099984, 269916194035, 489998333105, 0, 225043782750, 461976088268, 498021669583, 238346527126, 306347970271, 380671900746]) (branchResiduals095 11 0) 15120968
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck095_11_1 :
    integerResidualCheck 95 11 1 (dualNumerators095 11 1) ∧
    integerMassCheck 95 11 1 (dualNumerators095 11 1) := by
  apply integerChecks_of_simple 95 11 1 (dualNumerators095 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 495684390637, 246132542200, 446822154676, 0, 205214061173, 421269088530, 454138515265, 217344634900, 279354134309, 347129015395]) (branchResiduals095 11 1) 15120968
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck095_12_0 :
    integerResidualCheck 95 12 0 (dualNumerators095 12 0) ∧
    integerMassCheck 95 12 0 (dualNumerators095 12 0) := by
  apply integerChecks_of_simple 95 12 0 (dualNumerators095 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1144101124261, 568104470439, 1031321016287, 0, 473659535255, 972341366619, 1048208085022, 501658405706, 644784030255, 801216871619]) (branchResiduals095 12 0) 16348076
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck095_12_1 :
    integerResidualCheck 95 12 1 (dualNumerators095 12 1) ∧
    integerMassCheck 95 12 1 (dualNumerators095 12 1) := by
  apply integerChecks_of_simple 95 12 1 (dualNumerators095 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals095 12 1) 16348076
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck095_13_0 :
    integerResidualCheck 95 13 0 (dualNumerators095 13 0) ∧
    integerMassCheck 95 13 0 (dualNumerators095 13 0) := by
  apply integerChecks_of_simple 95 13 0 (dualNumerators095 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals095 13 0) 13962901
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck095_13_1 :
    integerResidualCheck 95 13 1 (dualNumerators095 13 1) ∧
    integerMassCheck 95 13 1 (dualNumerators095 13 1) := by
  apply integerChecks_of_simple 95 13 1 (dualNumerators095 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 966222317365, 479778584509, 870976665588, 0, 400017449587, 821166860693, 885238221966, 423663203373, 544536410901, 676647899379]) (branchResiduals095 13 1) 13962901
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck095_14_0 :
    integerResidualCheck 95 14 0 (dualNumerators095 14 0) ∧
    integerMassCheck 95 14 0 (dualNumerators095 14 0) := by
  apply integerChecks_of_simple 95 14 0 (dualNumerators095 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1144101124262, 568104470440, 1031321016288, 0, 473659535256, 972341366620, 1048208085022, 501658405707, 644784030255, 801216871620]) (branchResiduals095 14 0) 20161291
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck095_14_1 :
    integerResidualCheck 95 14 1 (dualNumerators095 14 1) ∧
    integerMassCheck 95 14 1 (dualNumerators095 14 1) := by
  apply integerChecks_of_simple 95 14 1 (dualNumerators095 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 523832516750, 260109520231, 472195570901, 0, 216867426466, 445191438428, 479927401181, 229686851658, 295217646558, 366841218336]) (branchResiduals095 14 1) 20161291
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck095_15_0 :
    integerResidualCheck 95 15 0 (dualNumerators095 15 0) ∧
    integerMassCheck 95 15 0 (dualNumerators095 15 0) := by
  apply integerChecks_of_simple 95 15 0 (dualNumerators095 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 543582099984, 269916194035, 489998333105, 0, 225043782750, 461976088267, 498021669583, 238346527126, 306347970271, 380671900746]) (branchResiduals095 15 0) 12900283
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck095_15_1 :
    integerResidualCheck 95 15 1 (dualNumerators095 15 1) ∧
    integerMassCheck 95 15 1 (dualNumerators095 15 1) := by
  apply integerChecks_of_simple 95 15 1 (dualNumerators095 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals095 15 1) 12900283
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck095_16_0 :
    integerResidualCheck 95 16 0 (dualNumerators095 16 0) ∧
    integerMassCheck 95 16 0 (dualNumerators095 16 0) := by
  apply integerChecks_of_simple 95 16 0 (dualNumerators095 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals095 16 0) 10683060
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck095_16_1 :
    integerResidualCheck 95 16 1 (dualNumerators095 16 1) ∧
    integerMassCheck 95 16 1 (dualNumerators095 16 1) := by
  apply integerChecks_of_simple 95 16 1 (dualNumerators095 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 874612019090, 434289406250, 788396879662, 0, 362090652396, 743309684668, 801306257136, 383494484713, 492907358117, 612492978948]) (branchResiduals095 16 1) 10683060
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck095_17_0 :
    integerResidualCheck 95 17 0 (dualNumerators095 17 0) ∧
    integerMassCheck 95 17 0 (dualNumerators095 17 0) := by
  apply integerChecks_of_simple 95 17 0 (dualNumerators095 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 712949339994, 354015653563, 642670147151, 0, 295162067305, 605916838014, 653193364245, 312609630099, 401798703857, 499280201462]) (branchResiduals095 17 0) 15120968
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck095_17_1 :
    integerResidualCheck 95 17 1 (dualNumerators095 17 1) ∧
    integerMassCheck 95 17 1 (dualNumerators095 17 1) := by
  apply integerChecks_of_simple 95 17 1 (dualNumerators095 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 495684390637, 246132542200, 446822154676, 0, 205214061173, 421269088530, 454138515265, 217344634900, 279354134309, 347129015395]) (branchResiduals095 17 1) 15120968
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck095_18_0 :
    integerResidualCheck 95 18 0 (dualNumerators095 18 0) ∧
    integerMassCheck 95 18 0 (dualNumerators095 18 0) := by
  apply integerChecks_of_simple 95 18 0 (dualNumerators095 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 934970696450, 333426002978, 763999473637, 0, 263461482107, 807731590141, 772489965679, 214059593984, 477654049462, 593539022787]) (branchResiduals095 18 0) 13565580
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck095_18_1 :
    integerResidualCheck 95 18 1 (dualNumerators095 18 1) ∧
    integerMassCheck 95 18 1 (dualNumerators095 18 1) := by
  apply integerChecks_of_simple 95 18 1 (dualNumerators095 18 1)
    (![552774353318, 101764201348, 552774353318, 0, 1, 194169418432, 229915461414, 0, 83885421775, 59829007246, 194169418432, 0, 94926637302, 515633295911, 229915461414, 0, 0, 515633295912, 201500008915, 170171850577, 856726447141, 300936675152, 92726973504, 109797748126, 194169418432, 0, 94926637302, 515633295911, 0, 0, 300936675152, 799162766836, 15443069854, 138502830895, 92726973504, 0, 130011204269, 0, 98264701746, 202671973406, 57973095424, 72038108846]) (branchResiduals095 18 1) 13565580
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck095_19_0 :
    integerResidualCheck 95 19 0 (dualNumerators095 19 0) ∧
    integerMassCheck 95 19 0 (dualNumerators095 19 0) := by
  apply integerChecks_of_simple 95 19 0 (dualNumerators095 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 875874933151, 195318139098, 645216866088, 0, 136231332822, 768418291818, 648421029826, 25293932239, 403390917798, 501258706842]) (branchResiduals095 19 0) 8248658
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck095_19_1 :
    integerResidualCheck 95 19 1 (dualNumerators095 19 1) ∧
    integerMassCheck 95 19 1 (dualNumerators095 19 1) := by
  apply integerChecks_of_simple 95 19 1 (dualNumerators095 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 350406455885, 413593017753, 460183470977, 0, 371450951992, 273765914097, 475079366460, 512398369190, 287707656866, 357509209222]) (branchResiduals095 19 1) 8248658
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck095_20_0 :
    integerResidualCheck 95 20 0 (dualNumerators095 20 0) ∧
    integerMassCheck 95 20 0 (dualNumerators095 20 0) := by
  apply integerChecks_of_simple 95 20 0 (dualNumerators095 20 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 176645531640, 1584264425996, 1060657349048, 0, 1487132967409, 0, 1124000645334, 2318263067540, 663125166110, 824007801299]) (branchResiduals095 20 0) 35312013
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck095_20_1 :
    integerResidualCheck 95 20 1 (dualNumerators095 20 1) ∧
    integerMassCheck 95 20 1 (dualNumerators095 20 1) := by
  apply integerChecks_of_simple 95 20 1 (dualNumerators095 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals095 20 1) 35312013
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck095_21_0 :
    integerResidualCheck 95 21 0 (dualNumerators095 21 0) ∧
    integerMassCheck 95 21 0 (dualNumerators095 21 0) := by
  apply integerChecks_of_simple 95 21 0 (dualNumerators095 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 759767979803, 549133445537, 757887471419, 892563449519, 583650214286, 725251211053]) (branchResiduals095 21 0) 11182451
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck095_21_1 :
    integerResidualCheck 95 21 1 (dualNumerators095 21 1) ∧
    integerMassCheck 95 21 1 (dualNumerators095 21 1) := by
  apply integerChecks_of_simple 95 21 1 (dualNumerators095 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 860003851037, 963321782180, 3460174706, 161253783489, 102979506989, 127963650709, 0, 0, 102979506989, 127963650709]) (branchResiduals095 21 1) 11182451
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck095_22_0 :
    integerResidualCheck 95 22 0 (dualNumerators095 22 0) ∧
    integerMassCheck 95 22 0 (dualNumerators095 22 0) := by
  apply integerChecks_of_simple 95 22 0 (dualNumerators095 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 136031845564, 627967628074, 85708482881, 374474988096, 645216866088, 0, 95974191249, 705361889470, 287707656866, 357509209222]) (branchResiduals095 22 0) 6465674
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck095_22_1 :
    integerResidualCheck 95 22 1 (dualNumerators095 22 1) ∧
    integerMassCheck 95 22 1 (dualNumerators095 22 1) := by
  apply integerChecks_of_simple 95 22 1 (dualNumerators095 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 9522456419, 111749239332, 1534493418, 71511669319, 45668611868, 56748400418, 0, 0, 45668611868, 56748400418]) (branchResiduals095 22 1) 6465674
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck095_23_0 :
    integerResidualCheck 95 23 0 (dualNumerators095 23 0) ∧
    integerMassCheck 95 23 0 (dualNumerators095 23 0) := by
  apply integerChecks_of_simple 95 23 0 (dualNumerators095 23 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 1176645531640, 584264425996, 1060657349048, 0, 1487132967409, 0, 1124000645334, 2318263067540, 663125166110, 824007801299]) (branchResiduals095 23 0) 35297932
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck095_23_1 :
    integerResidualCheck 95 23 1 (dualNumerators095 23 1) ∧
    integerMassCheck 95 23 1 (dualNumerators095 23 1) := by
  apply integerChecks_of_simple 95 23 1 (dualNumerators095 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 160334187224, 1881575790198, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals095 23 1) 35297932
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck095_24_0 :
    integerResidualCheck 95 24 0 (dualNumerators095 24 0) ∧
    integerMassCheck 95 24 0 (dualNumerators095 24 0) := by
  apply integerChecks_of_simple 95 24 0 (dualNumerators095 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 512185690040, 559007382209, 705016048726, 601815130180, 477654049462, 593539022787]) (branchResiduals095 24 0) 9356857
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck095_24_1 :
    integerResidualCheck 95 24 1 (dualNumerators095 24 1) ∧
    integerMassCheck 95 24 1 (dualNumerators095 24 1) := by
  apply integerChecks_of_simple 95 24 1 (dualNumerators095 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 690777049383, 178822020994, 66021086067, 82038644814, 0, 0, 66021086067, 82038644814]) (branchResiduals095 24 1) 9356857
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck095_25_0 :
    integerResidualCheck 95 25 0 (dualNumerators095 25 0) ∧
    integerMassCheck 95 25 0 (dualNumerators095 25 0) := by
  apply integerChecks_of_simple 95 25 0 (dualNumerators095 25 0)
    (![34966365041, 6437209308, 34966365041, 0, 1, 22997469043, 27231238312, 0, 632721051475, 451271169324, 515942815115, 0, 137926201422, 749203214751, 610926434029, 0, 0, 749203214752, 1519850467647, 1283552135172, 54193197479, 35643006641, 699410063567, 828169486116, 515942815115, 0, 137926201422, 749203214751, 0, 0, 799642480277, 1161164957288, 639671999392, 521492957897, 54193197479, 0, 457443319543, 523189836115, 0, 35643006641, 437272616834, 543360538824]) (branchResiduals095 25 0) 8671199
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck095_25_1 :
    integerResidualCheck 95 25 1 (dualNumerators095 25 1) ∧
    integerMassCheck 95 25 1 (dualNumerators095 25 1) := by
  apply integerChecks_of_simple 95 25 1 (dualNumerators095 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals095 25 1) 8671199
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck095_26_0 :
    integerResidualCheck 95 26 0 (dualNumerators095 26 0) ∧
    integerMassCheck 95 26 0 (dualNumerators095 26 0) := by
  apply integerChecks_of_simple 95 26 0 (dualNumerators095 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals095 26 0) 15099566
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck095_26_1 :
    integerResidualCheck 95 26 1 (dualNumerators095 26 1) ∧
    integerMassCheck 95 26 1 (dualNumerators095 26 1) := by
  apply integerChecks_of_simple 95 26 1 (dualNumerators095 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 1025837005087, 204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals095 26 1) 15099566
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck095_27_0 :
    integerResidualCheck 95 27 0 (dualNumerators095 27 0) ∧
    integerMassCheck 95 27 0 (dualNumerators095 27 0) := by
  apply integerChecks_of_simple 95 27 0 (dualNumerators095 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 436855949686, 304617712691, 340673826058, 423325647580]) (branchResiduals095 27 0) 7338775
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck095_27_1 :
    integerResidualCheck 95 27 1 (dualNumerators095 27 1) ∧
    integerMassCheck 95 27 1 (dualNumerators095 27 1) := by
  apply integerChecks_of_simple 95 27 1 (dualNumerators095 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 908602750628, 623335190581, 377837583379, 0, 538833784902, 754926527212, 385949753226, 259267112862, 236224837801, 293536000677]) (branchResiduals095 27 1) 7338775
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck095_28_0 :
    integerResidualCheck 95 28 0 (dualNumerators095 28 0) ∧
    integerMassCheck 95 28 0 (dualNumerators095 28 0) := by
  apply integerChecks_of_simple 95 28 0 (dualNumerators095 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 374399059503, 471423145846, 287707656866, 357509209222]) (branchResiduals095 28 0) 10335557
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck095_28_1 :
    integerResidualCheck 95 28 1 (dualNumerators095 28 1) ∧
    integerMassCheck 95 28 1 (dualNumerators095 28 1) := by
  apply integerChecks_of_simple 95 28 1 (dualNumerators095 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 426731607120, 507685338329, 2156352207, 100492021777, 456143077212, 332995651238, 0, 0, 64175975503, 79745886859]) (branchResiduals095 28 1) 10335557
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck095_29_0 :
    integerResidualCheck 95 29 0 (dualNumerators095 29 0) ∧
    integerMassCheck 95 29 0 (dualNumerators095 29 0) := by
  apply integerChecks_of_simple 95 29 0 (dualNumerators095 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals095 29 0) 40352153
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck095_29_1 :
    integerResidualCheck 95 29 1 (dualNumerators095 29 1) ∧
    integerMassCheck 95 29 1 (dualNumerators095 29 1) := by
  apply integerChecks_of_simple 95 29 1 (dualNumerators095 29 1)
    (![813650000253, 149790673094, 813650000253, 0, 1, 30189853607, 35747720615, 0, 1140807387415, 813650000252, 30189853607, 0, 248683411329, 1350826813920, 35747720615, 0, 0, 1350826813921, 2740317612662, 2314267487267, 1261048870572, 46790242466, 1261048870572, 1493204415423, 30189853607, 0, 248683411329, 1350826813920, 0, 0, 46790242466, 2093601213671, 210019426506, 1883581787165, 72117429420, 1188931441153, 1768099142126, 0, 46790242466, 0, 788410359408, 979688782719]) (branchResiduals095 29 1) 40352153
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck095_30_0 :
    integerResidualCheck 95 30 0 (dualNumerators095 30 0) ∧
    integerMassCheck 95 30 0 (dualNumerators095 30 0) := by
  apply integerChecks_of_simple 95 30 0 (dualNumerators095 30 0)
    (![49325597255, 9080703511, 49325597255, 0, 0, 3298611714, 3905876838, 0, 69158736213, 49325597255, 3298611714, 0, 15075840703, 81890664738, 3905876838, 0, 0, 81890664738, 166125241653, 1140296965504, 76448090321, 5112407761, 76448090321, 90521968404, 3298611714, 0, 15075840703, 81890664738, 0, 0, 5112407761, 126919597181, 14951178082, 111968419099, 6591197296, 69856893026, 104967558241, 2219249557, 5112407761, 0, 107186807798, 0]) (branchResiduals095 30 0) 7680628
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck095_30_1 :
    integerResidualCheck 95 30 1 (dualNumerators095 30 1) ∧
    integerMassCheck 95 30 1 (dualNumerators095 30 1) := by
  apply integerChecks_of_simple 95 30 1 (dualNumerators095 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 604489703699, 300159920941, 544901951702, 0, 250259619582, 513739854055, 556554858415, 372095930671, 281282522283, 482716951355]) (branchResiduals095 30 1) 7680628
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck095_31_0 :
    integerResidualCheck 95 31 0 (dualNumerators095 31 0) ∧
    integerMassCheck 95 31 0 (dualNumerators095 31 0) := by
  apply integerChecks_of_simple 95 31 0 (dualNumerators095 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 1032415642125, 1, 592902192609, 0, 1222480453651, 0, 500720887661, 0, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642125, 0, 592902192609, 0, 0, 0, 1600106408231, 776050524992, 77849441973, 698201083019, 898753891846, 674088683815, 655394283556, 0, 905514817789, 694591590443, 655394283556, 0]) (branchResiduals095 31 0) 32891612
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck095_31_1 :
    integerResidualCheck 95 31 1 (dualNumerators095 31 1) ∧
    integerMassCheck 95 31 1 (dualNumerators095 31 1) := by
  apply integerChecks_of_simple 95 31 1 (dualNumerators095 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 741061026801, 808805463926, 18993131489, 744564115640, 327950144489, 1221916346239]) (branchResiduals095 31 1) 32891612
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck095_32_0 :
    integerResidualCheck 95 32 0 (dualNumerators095 32 0) ∧
    integerMassCheck 95 32 0 (dualNumerators095 32 0) := by
  apply integerChecks_of_simple 95 32 0 (dualNumerators095 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 0, 2743468108582, 2028778803022, 0, 505064750776, 2743468108580, 1713354977902, 2, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 2028778803022, 0, 0, 0, 4252009289869, 2655471466972, 266383392861, 2389088074111, 91471945490, 1508010932335, 2242612772688, 0, 163638085097, 4088371204772, 0, 2242612772688]) (branchResiduals095 32 0) 67647473
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck095_32_1 :
    integerResidualCheck 95 32 1 (dualNumerators095 32 1) ∧
    integerMassCheck 95 32 1 (dualNumerators095 32 1) := by
  apply integerChecks_of_simple 95 32 1 (dualNumerators095 32 1)
    (![830518849052, 152896180641, 830518849053, 0, 1, 55540314888, 65765130409, 0, 1164458966499, 830518849051, 55540314888, 0, 253839194360, 1378832582089, 65765130409, 0, 0, 1378832582090, 2797130742946, 2362247611782, 1287193334063, 86080072929, 1287193334063, 1524162000997, 55540314888, 0, 253839194360, 1378832582089, 0, 0, 86080072929, 2137006415304, 251740189748, 1885266225556, 110979164901, 1176214169163, 1767389357845, 37366574157, 86080072929, 0, 1804755932001, 0]) (branchResiduals095 32 1) 67647473
    branchSparseDots095 branchIntegerCurvature095 branchDots095
    branchIntegerCurvature095_entry rfl
    (congrFun (congrFun branchResiduals095_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks095 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 95 j s (dualNumerators095 j s) ∧
    integerMassCheck 95 j s (dualNumerators095 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck095_0_0
    · exact integerCheck095_0_1
  · fin_cases s
    · exact integerCheck095_1_0
    · exact integerCheck095_1_1
  · fin_cases s
    · exact integerCheck095_2_0
    · exact integerCheck095_2_1
  · fin_cases s
    · exact integerCheck095_3_0
    · exact integerCheck095_3_1
  · fin_cases s
    · exact integerCheck095_4_0
    · exact integerCheck095_4_1
  · fin_cases s
    · exact integerCheck095_5_0
    · exact integerCheck095_5_1
  · fin_cases s
    · exact integerCheck095_6_0
    · exact integerCheck095_6_1
  · fin_cases s
    · exact integerCheck095_7_0
    · exact integerCheck095_7_1
  · fin_cases s
    · exact integerCheck095_8_0
    · exact integerCheck095_8_1
  · fin_cases s
    · exact integerCheck095_9_0
    · exact integerCheck095_9_1
  · fin_cases s
    · exact integerCheck095_10_0
    · exact integerCheck095_10_1
  · fin_cases s
    · exact integerCheck095_11_0
    · exact integerCheck095_11_1
  · fin_cases s
    · exact integerCheck095_12_0
    · exact integerCheck095_12_1
  · fin_cases s
    · exact integerCheck095_13_0
    · exact integerCheck095_13_1
  · fin_cases s
    · exact integerCheck095_14_0
    · exact integerCheck095_14_1
  · fin_cases s
    · exact integerCheck095_15_0
    · exact integerCheck095_15_1
  · fin_cases s
    · exact integerCheck095_16_0
    · exact integerCheck095_16_1
  · fin_cases s
    · exact integerCheck095_17_0
    · exact integerCheck095_17_1
  · fin_cases s
    · exact integerCheck095_18_0
    · exact integerCheck095_18_1
  · fin_cases s
    · exact integerCheck095_19_0
    · exact integerCheck095_19_1
  · fin_cases s
    · exact integerCheck095_20_0
    · exact integerCheck095_20_1
  · fin_cases s
    · exact integerCheck095_21_0
    · exact integerCheck095_21_1
  · fin_cases s
    · exact integerCheck095_22_0
    · exact integerCheck095_22_1
  · fin_cases s
    · exact integerCheck095_23_0
    · exact integerCheck095_23_1
  · fin_cases s
    · exact integerCheck095_24_0
    · exact integerCheck095_24_1
  · fin_cases s
    · exact integerCheck095_25_0
    · exact integerCheck095_25_1
  · fin_cases s
    · exact integerCheck095_26_0
    · exact integerCheck095_26_1
  · fin_cases s
    · exact integerCheck095_27_0
    · exact integerCheck095_27_1
  · fin_cases s
    · exact integerCheck095_28_0
    · exact integerCheck095_28_1
  · fin_cases s
    · exact integerCheck095_29_0
    · exact integerCheck095_29_1
  · fin_cases s
    · exact integerCheck095_30_0
    · exact integerCheck095_30_1
  · fin_cases s
    · exact integerCheck095_31_0
    · exact integerCheck095_31_1
  · fin_cases s
    · exact integerCheck095_32_0
    · exact integerCheck095_32_1

end ElevenSquare.Tasks.T06
