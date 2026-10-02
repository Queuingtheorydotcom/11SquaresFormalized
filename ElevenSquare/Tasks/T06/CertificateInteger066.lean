import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.DataDual066
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
import ElevenSquare.Tasks.T06.SparseColumn23
import ElevenSquare.Tasks.T06.SparseColumn24
import ElevenSquare.Tasks.T06.SparseColumn25
import ElevenSquare.Tasks.T06.SparseColumn27
import ElevenSquare.Tasks.T06.SparseColumn28
import ElevenSquare.Tasks.T06.SparseColumn29
import ElevenSquare.Tasks.T06.SparseColumn30
import ElevenSquare.Tasks.T06.SparseColumn31
import ElevenSquare.Tasks.T06.SparseColumn32
import ElevenSquare.Tasks.T06.SparseColumn35
import ElevenSquare.Tasks.T06.SparseColumn36
import ElevenSquare.Tasks.T06.SparseColumn37
import ElevenSquare.Tasks.T06.SparseColumn38
import ElevenSquare.Tasks.T06.SparseColumn39
import ElevenSquare.Tasks.T06.SparseColumn40
import ElevenSquare.Tasks.T06.SparseColumn55
import ElevenSquare.Tasks.T06.SparseColumn56

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix066 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral43, roundedGradientLiteral44, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix066_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = branchIntegerMatrix066 := by
  change roundedGradients ∘ branchRows 66 = branchIntegerMatrix066
  rw [show branchRows 66 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 54, 55, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral43_eq, roundedGradientLiteral44_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix066]

theorem branchColumn066_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 0) i) = _
  rw [branchColumn066_0]
  exact sparseColumn00_sum n

theorem branchColumn066_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 1) i) = _
  rw [branchColumn066_1]
  exact sparseColumn01_sum n

theorem branchColumn066_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 2) i) = _
  rw [branchColumn066_2]
  exact sparseColumn02_sum n

theorem branchColumn066_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 3) i) = _
  rw [branchColumn066_3]
  exact sparseColumn03_sum n

theorem branchColumn066_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 4) i) = _
  rw [branchColumn066_4]
  exact sparseColumn04_sum n

theorem branchColumn066_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 5) i) = _
  rw [branchColumn066_5]
  exact sparseColumn05_sum n

theorem branchColumn066_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 6) i) = _
  rw [branchColumn066_6]
  exact sparseColumn06_sum n

theorem branchColumn066_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 7) i) = _
  rw [branchColumn066_7]
  exact sparseColumn07_sum n

theorem branchColumn066_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 8) i) = _
  rw [branchColumn066_8]
  exact sparseColumn08_sum n

theorem branchColumn066_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 9) i) = _
  rw [branchColumn066_9]
  exact sparseColumn09_sum n

theorem branchColumn066_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 10) i) = _
  rw [branchColumn066_10]
  exact sparseColumn10_sum n

theorem branchColumn066_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 11) i) = _
  rw [branchColumn066_11]
  exact sparseColumn11_sum n

theorem branchColumn066_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 12) i) = _
  rw [branchColumn066_12]
  exact sparseColumn35_sum n

theorem branchColumn066_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 13) i) = _
  rw [branchColumn066_13]
  exact sparseColumn36_sum n

theorem branchColumn066_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 14) = sparseColumn37 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 14) = sparseDot37 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 14) i) = _
  rw [branchColumn066_14]
  exact sparseColumn37_sum n

theorem branchColumn066_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 15) i) = _
  rw [branchColumn066_15]
  exact sparseColumn38_sum n

theorem branchColumn066_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 16) i) = _
  rw [branchColumn066_16]
  exact sparseColumn39_sum n

theorem branchColumn066_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 17) = sparseColumn40 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 17) = sparseDot40 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 17) i) = _
  rw [branchColumn066_17]
  exact sparseColumn40_sum n

theorem branchColumn066_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 18) i) = _
  rw [branchColumn066_18]
  exact sparseColumn18_sum n

theorem branchColumn066_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 19) i) = _
  rw [branchColumn066_19]
  exact sparseColumn19_sum n

theorem branchColumn066_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 20) = sparseColumn55 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 20) = sparseDot55 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 20) i) = _
  rw [branchColumn066_20]
  exact sparseColumn55_sum n

theorem branchColumn066_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 21) i) = _
  rw [branchColumn066_21]
  exact sparseColumn21_sum n

theorem branchColumn066_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 22) i) = _
  rw [branchColumn066_22]
  exact sparseColumn22_sum n

theorem branchColumn066_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 23) = sparseColumn23 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 23) = sparseDot23 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 23) i) = _
  rw [branchColumn066_23]
  exact sparseColumn23_sum n

theorem branchColumn066_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 24) i) = _
  rw [branchColumn066_24]
  exact sparseColumn24_sum n

theorem branchColumn066_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 25) i) = _
  rw [branchColumn066_25]
  exact sparseColumn25_sum n

theorem branchColumn066_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 26) = sparseColumn56 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 26) = sparseDot56 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 26) i) = _
  rw [branchColumn066_26]
  exact sparseColumn56_sum n

theorem branchColumn066_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 27) i) = _
  rw [branchColumn066_27]
  exact sparseColumn27_sum n

theorem branchColumn066_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 28) i) = _
  rw [branchColumn066_28]
  exact sparseColumn28_sum n

theorem branchColumn066_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 29) = sparseColumn29 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 29) = sparseDot29 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 29) i) = _
  rw [branchColumn066_29]
  exact sparseColumn29_sum n

theorem branchColumn066_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 30) i) = _
  rw [branchColumn066_30]
  exact sparseColumn30_sum n

theorem branchColumn066_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 31) i) = _
  rw [branchColumn066_31]
  exact sparseColumn31_sum n

theorem branchColumn066_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 66 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 66 i)) = _
  rw [branchIntegerMatrix066_eq]
  simp only [branchIntegerMatrix066, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot066_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 66 i) 32) i) = _
  rw [branchColumn066_32]
  exact sparseColumn32_sum n

def branchSparseDots066 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot37, sparseDot38, sparseDot39, sparseDot40, sparseDot18, sparseDot19, sparseDot55, sparseDot21, sparseDot22, sparseDot23, sparseDot24, sparseDot25, sparseDot56, sparseDot27, sparseDot28, sparseDot29, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot066_0 :
    branchSparseDots066 0 = sparseDot00 := rfl

private theorem branchSparseDot066_1 :
    branchSparseDots066 1 = sparseDot01 := rfl

private theorem branchSparseDot066_2 :
    branchSparseDots066 2 = sparseDot02 := rfl

private theorem branchSparseDot066_3 :
    branchSparseDots066 3 = sparseDot03 := rfl

private theorem branchSparseDot066_4 :
    branchSparseDots066 4 = sparseDot04 := rfl

private theorem branchSparseDot066_5 :
    branchSparseDots066 5 = sparseDot05 := rfl

private theorem branchSparseDot066_6 :
    branchSparseDots066 6 = sparseDot06 := rfl

private theorem branchSparseDot066_7 :
    branchSparseDots066 7 = sparseDot07 := rfl

private theorem branchSparseDot066_8 :
    branchSparseDots066 8 = sparseDot08 := rfl

private theorem branchSparseDot066_9 :
    branchSparseDots066 9 = sparseDot09 := rfl

private theorem branchSparseDot066_10 :
    branchSparseDots066 10 = sparseDot10 := rfl

private theorem branchSparseDot066_11 :
    branchSparseDots066 11 = sparseDot11 := rfl

private theorem branchSparseDot066_12 :
    branchSparseDots066 12 = sparseDot35 := rfl

private theorem branchSparseDot066_13 :
    branchSparseDots066 13 = sparseDot36 := rfl

private theorem branchSparseDot066_14 :
    branchSparseDots066 14 = sparseDot37 := rfl

private theorem branchSparseDot066_15 :
    branchSparseDots066 15 = sparseDot38 := rfl

private theorem branchSparseDot066_16 :
    branchSparseDots066 16 = sparseDot39 := rfl

private theorem branchSparseDot066_17 :
    branchSparseDots066 17 = sparseDot40 := rfl

private theorem branchSparseDot066_18 :
    branchSparseDots066 18 = sparseDot18 := rfl

private theorem branchSparseDot066_19 :
    branchSparseDots066 19 = sparseDot19 := rfl

private theorem branchSparseDot066_20 :
    branchSparseDots066 20 = sparseDot55 := rfl

private theorem branchSparseDot066_21 :
    branchSparseDots066 21 = sparseDot21 := rfl

private theorem branchSparseDot066_22 :
    branchSparseDots066 22 = sparseDot22 := rfl

private theorem branchSparseDot066_23 :
    branchSparseDots066 23 = sparseDot23 := rfl

private theorem branchSparseDot066_24 :
    branchSparseDots066 24 = sparseDot24 := rfl

private theorem branchSparseDot066_25 :
    branchSparseDots066 25 = sparseDot25 := rfl

private theorem branchSparseDot066_26 :
    branchSparseDots066 26 = sparseDot56 := rfl

private theorem branchSparseDot066_27 :
    branchSparseDots066 27 = sparseDot27 := rfl

private theorem branchSparseDot066_28 :
    branchSparseDots066 28 = sparseDot28 := rfl

private theorem branchSparseDot066_29 :
    branchSparseDots066 29 = sparseDot29 := rfl

private theorem branchSparseDot066_30 :
    branchSparseDots066 30 = sparseDot30 := rfl

private theorem branchSparseDot066_31 :
    branchSparseDots066 31 = sparseDot31 := rfl

private theorem branchSparseDot066_32 :
    branchSparseDots066 32 = sparseDot32 := rfl

theorem branchDots066 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 66 i) k) = branchSparseDots066 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot066_0 n
      _ = _ := congrFun branchSparseDot066_0.symm n
  · calc
      _ = sparseDot01 n := branchDot066_1 n
      _ = _ := congrFun branchSparseDot066_1.symm n
  · calc
      _ = sparseDot02 n := branchDot066_2 n
      _ = _ := congrFun branchSparseDot066_2.symm n
  · calc
      _ = sparseDot03 n := branchDot066_3 n
      _ = _ := congrFun branchSparseDot066_3.symm n
  · calc
      _ = sparseDot04 n := branchDot066_4 n
      _ = _ := congrFun branchSparseDot066_4.symm n
  · calc
      _ = sparseDot05 n := branchDot066_5 n
      _ = _ := congrFun branchSparseDot066_5.symm n
  · calc
      _ = sparseDot06 n := branchDot066_6 n
      _ = _ := congrFun branchSparseDot066_6.symm n
  · calc
      _ = sparseDot07 n := branchDot066_7 n
      _ = _ := congrFun branchSparseDot066_7.symm n
  · calc
      _ = sparseDot08 n := branchDot066_8 n
      _ = _ := congrFun branchSparseDot066_8.symm n
  · calc
      _ = sparseDot09 n := branchDot066_9 n
      _ = _ := congrFun branchSparseDot066_9.symm n
  · calc
      _ = sparseDot10 n := branchDot066_10 n
      _ = _ := congrFun branchSparseDot066_10.symm n
  · calc
      _ = sparseDot11 n := branchDot066_11 n
      _ = _ := congrFun branchSparseDot066_11.symm n
  · calc
      _ = sparseDot35 n := branchDot066_12 n
      _ = _ := congrFun branchSparseDot066_12.symm n
  · calc
      _ = sparseDot36 n := branchDot066_13 n
      _ = _ := congrFun branchSparseDot066_13.symm n
  · calc
      _ = sparseDot37 n := branchDot066_14 n
      _ = _ := congrFun branchSparseDot066_14.symm n
  · calc
      _ = sparseDot38 n := branchDot066_15 n
      _ = _ := congrFun branchSparseDot066_15.symm n
  · calc
      _ = sparseDot39 n := branchDot066_16 n
      _ = _ := congrFun branchSparseDot066_16.symm n
  · calc
      _ = sparseDot40 n := branchDot066_17 n
      _ = _ := congrFun branchSparseDot066_17.symm n
  · calc
      _ = sparseDot18 n := branchDot066_18 n
      _ = _ := congrFun branchSparseDot066_18.symm n
  · calc
      _ = sparseDot19 n := branchDot066_19 n
      _ = _ := congrFun branchSparseDot066_19.symm n
  · calc
      _ = sparseDot55 n := branchDot066_20 n
      _ = _ := congrFun branchSparseDot066_20.symm n
  · calc
      _ = sparseDot21 n := branchDot066_21 n
      _ = _ := congrFun branchSparseDot066_21.symm n
  · calc
      _ = sparseDot22 n := branchDot066_22 n
      _ = _ := congrFun branchSparseDot066_22.symm n
  · calc
      _ = sparseDot23 n := branchDot066_23 n
      _ = _ := congrFun branchSparseDot066_23.symm n
  · calc
      _ = sparseDot24 n := branchDot066_24 n
      _ = _ := congrFun branchSparseDot066_24.symm n
  · calc
      _ = sparseDot25 n := branchDot066_25 n
      _ = _ := congrFun branchSparseDot066_25.symm n
  · calc
      _ = sparseDot56 n := branchDot066_26 n
      _ = _ := congrFun branchSparseDot066_26.symm n
  · calc
      _ = sparseDot27 n := branchDot066_27 n
      _ = _ := congrFun branchSparseDot066_27.symm n
  · calc
      _ = sparseDot28 n := branchDot066_28 n
      _ = _ := congrFun branchSparseDot066_28.symm n
  · calc
      _ = sparseDot29 n := branchDot066_29 n
      _ = _ := congrFun branchSparseDot066_29.symm n
  · calc
      _ = sparseDot30 n := branchDot066_30 n
      _ = _ := congrFun branchSparseDot066_30.symm n
  · calc
      _ = sparseDot31 n := branchDot066_31 n
      _ = _ := congrFun branchSparseDot066_31.symm n
  · calc
      _ = sparseDot32 n := branchDot066_32 n
      _ = _ := congrFun branchSparseDot066_32.symm n

def branchIntegerCurvature066 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101981296, 101981296, 79086693, 79086693, 115699695, 115699695, 48290998, 48290998, 204734428, 204734428]

theorem branchIntegerCurvature066_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 66 i)) = branchIntegerCurvature066 := by
  change curvatureNumerators ∘ branchRows 66 = branchIntegerCurvature066
  rw [show branchRows 66 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 54, 55, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature066_entry (i : Fin 42) :
    curvatureNumerators (branchRows 66 i) = branchIntegerCurvature066 i :=
  congrFun branchIntegerCurvature066_eq i

theorem integerCheck066_0_0 :
    integerResidualCheck 66 0 0 (dualNumerators066 0 0) ∧
    integerMassCheck 66 0 0 (dualNumerators066 0 0) := by
  have hn : dualNumerators066 0 0 = ![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 143134913131, 2029911410936, 0, 1308901425339, 1692057632752, 143134913133, 1896652816305, 70360777679, 1430871029972, 404321515913] := rfl
  have he : residualNumerators 66 0 0 = 1298901627145098 := rfl
  have hr : radiusNumerators 0 = 18767167 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_0_1 :
    integerResidualCheck 66 0 1 (dualNumerators066 0 1) ∧
    integerMassCheck 66 0 1 (dualNumerators066 0 1) := by
  have hn : dualNumerators066 0 1 = ![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 66 0 1 = 33000000000000 := rfl
  have hr : radiusNumerators 0 = 18767167 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_1_0 :
    integerResidualCheck 66 1 0 (dualNumerators066 1 0) ∧
    integerMassCheck 66 1 0 (dualNumerators066 1 0) := by
  have hn : dualNumerators066 1 0 = ![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 169485647445, 2403612383675, 0, 1549866490727, 2003560676621, 169485647447, 2245821257146, 83313998652, 1694290356000, 478755968067] := rfl
  have he : residualNumerators 66 1 0 = 1546259270672572 := rfl
  have hr : radiusNumerators 1 = 22176635 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_1_1 :
    integerResidualCheck 66 1 1 (dualNumerators066 1 1) ∧
    integerMassCheck 66 1 1 (dualNumerators066 1 1) := by
  have hn : dualNumerators066 1 1 = ![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 66 1 1 = 33000000000000 := rfl
  have hr : radiusNumerators 1 = 22176635 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_2_0 :
    integerResidualCheck 66 2 0 (dualNumerators066 2 0) ∧
    integerMassCheck 66 2 0 (dualNumerators066 2 0) := by
  have hn : dualNumerators066 2 0 = ![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 169485647445, 2403612383677, 0, 1549866490728, 2003560676622, 169485647447, 2245821257148, 83313998652, 1694290356001, 478755968068] := rfl
  have he : residualNumerators 66 2 0 = 1582774446824660 := rfl
  have hr : radiusNumerators 2 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_2_1 :
    integerResidualCheck 66 2 1 (dualNumerators066 2 1) ∧
    integerMassCheck 66 2 1 (dualNumerators066 2 1) := by
  have hn : dualNumerators066 2 1 = ![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 143134913131, 2029911410934, 0, 1308901425338, 1692057632751, 143134913133, 1896652816304, 70360777679, 1430871029971, 404321515912] := rfl
  have he : residualNumerators 66 2 1 = 1335015321214479 := rfl
  have hr : radiusNumerators 2 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_3_0 :
    integerResidualCheck 66 3 0 (dualNumerators066 3 0) ∧
    integerMassCheck 66 3 0 (dualNumerators066 3 0) := by
  have hn : dualNumerators066 3 0 = ![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 66 3 0 = 33000000000000 := rfl
  have hr : radiusNumerators 3 = 16360330 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_3_1 :
    integerResidualCheck 66 3 1 (dualNumerators066 3 1) ∧
    integerMassCheck 66 3 1 (dualNumerators066 3 1) := by
  have hn : dualNumerators066 3 1 = ![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000000, 0, 203380245200, 1104743927907, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 112780107974, 1599425486726, 0, 1031321016287, 1333220793899, 112780107975, 1494427213684, 55439277044, 1127424369963, 318576531911] := rfl
  have he : residualNumerators 66 3 1 = 1023147337483776 := rfl
  have hr : radiusNumerators 3 = 16360330 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_4_0 :
    integerResidualCheck 66 4 0 (dualNumerators066 4 0) ∧
    integerMassCheck 66 4 0 (dualNumerators066 4 0) := by
  have hn : dualNumerators066 4 0 = ![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757645, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 95245651777, 1350755250097, 0, 870976665588, 1125938658502, 95245651778, 1262081554611, 46819870729, 952138376845, 269045933435] := rfl
  have he : residualNumerators 66 4 0 = 860313388414246 := rfl
  have hr : radiusNumerators 4 = 13760362 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_4_1 :
    integerResidualCheck 66 4 1 (dualNumerators066 4 1) ∧
    integerMassCheck 66 4 1 (dualNumerators066 4 1) := by
  have hn : dualNumerators066 4 1 = ![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 66 4 1 = 33000000000000 := rfl
  have hr : radiusNumerators 4 = 13760362 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_5_0 :
    integerResidualCheck 66 5 0 (dualNumerators066 5 0) ∧
    integerMassCheck 66 5 0 (dualNumerators066 5 0) := by
  have hn : dualNumerators066 5 0 = ![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245201, 1104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 112780107974, 1599425486727, 0, 1031321016288, 1333220793900, 112780107975, 1494427213685, 55439277044, 1127424369964, 318576531911] := rfl
  have he : residualNumerators 66 5 0 = 1054188539982353 := rfl
  have hr : radiusNumerators 5 = 17641130 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_5_1 :
    integerResidualCheck 66 5 1 (dualNumerators066 5 1) ∧
    integerMassCheck 66 5 1 (dualNumerators066 5 1) := by
  have hn : dualNumerators066 5 1 = ![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170264, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 95245651777, 1350755250096, 0, 870976665588, 1125938658501, 95245651778, 1262081554610, 46819870729, 952138376844, 269045933435] := rfl
  have he : residualNumerators 66 5 1 = 894235780703818 := rfl
  have hr : radiusNumerators 5 = 17641130 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_6_0 :
    integerResidualCheck 66 6 0 (dualNumerators066 6 0) ∧
    integerMassCheck 66 6 0 (dualNumerators066 6 0) := by
  have hn : dualNumerators066 6 0 = ![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 659499318402, 1175693227483, 103906894360, 5439901403, 1430871029972, 404321515913] := rfl
  have he : residualNumerators 66 6 0 = 719096183434180 := rfl
  have hr : radiusNumerators 6 = 8962451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_6_1 :
    integerResidualCheck 66 6 1 (dualNumerators066 6 1) ∧
    integerMassCheck 66 6 1 (dualNumerators066 6 1) := by
  have hn : dualNumerators066 6 1 = ![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 760187607595, 1097479190627, 0, 0] := rfl
  have he : residualNumerators 66 6 1 = 624777238175104 := rfl
  have hr : radiusNumerators 6 = 8962451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_7_0 :
    integerResidualCheck 66 7 0 (dualNumerators066 7 0) ∧
    integerMassCheck 66 7 0 (dualNumerators066 7 0) := by
  have hn : dualNumerators066 7 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 66 7 0 = 33000000000000 := rfl
  have hr : radiusNumerators 7 = 10424794 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_7_1 :
    integerResidualCheck 66 7 1 (dualNumerators066 7 1) ∧
    integerMassCheck 66 7 1 (dualNumerators066 7 1) := by
  have hn : dualNumerators066 7 1 = ![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646810, 830103123887, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675220, 1, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 84742823723, 1201806191840, 0, 774933245365, 1001780338312, 84742823724, 1122910628575, 41656999326, 847145178002, 239377984034] := rfl
  have he : residualNumerators 66 7 1 = 759261847292819 := rfl
  have hr : radiusNumerators 7 = 10424794 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_8_0 :
    integerResidualCheck 66 8 0 (dualNumerators066 8 0) ∧
    integerMassCheck 66 8 0 (dualNumerators066 8 0) := by
  have hn : dualNumerators066 8 0 = ![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293619, 1660206247774, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350440, 2, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 169485647445, 2403612383679, 0, 1549866490730, 2003560676624, 169485647447, 2245821257150, 83313998652, 1694290356003, 478755968068] := rfl
  have he : residualNumerators 66 8 0 = 1578310645107587 := rfl
  have hr : radiusNumerators 8 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_8_1 :
    integerResidualCheck 66 8 1 (dualNumerators066 8 1) ∧
    integerMassCheck 66 8 1 (dualNumerators066 8 1) := by
  have hn : dualNumerators066 8 1 = ![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590429, 217988955956, 0, 1402086139075, 1269150346660, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546384, 0, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 120881051971, 1714311493912, 0, 1105400337063, 1428985438754, 120881051972, 1601771242546, 59421455166, 1208406751039, 341459739686] := rfl
  have he : residualNumerators 66 8 1 = 1129166324661442 := rfl
  have hr : radiusNumerators 8 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_9_0 :
    integerResidualCheck 66 9 0 (dualNumerators066 9 0) ∧
    integerMassCheck 66 9 0 (dualNumerators066 9 0) := by
  have hn : dualNumerators066 9 0 = ![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 112780107974, 1599425486726, 0, 1031321016287, 1333220793899, 112780107975, 1494427213684, 55439277044, 1127424369963, 318576531911] := rfl
  have he : residualNumerators 66 9 0 = 1023549024918311 := rfl
  have hr : radiusNumerators 9 = 16350530 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_9_1 :
    integerResidualCheck 66 9 1 (dualNumerators066 9 1) ∧
    integerMassCheck 66 9 1 (dualNumerators066 9 1) := by
  have hn : dualNumerators066 9 1 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 66 9 1 = 33000000000000 := rfl
  have hr : radiusNumerators 9 = 16350530 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_10_0 :
    integerResidualCheck 66 10 0 (dualNumerators066 10 0) ∧
    integerMassCheck 66 10 0 (dualNumerators066 10 0) := by
  have hn : dualNumerators066 10 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 66 10 0 = 33000000000000 := rfl
  have hr : radiusNumerators 10 = 10683139 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_10_1 :
    integerResidualCheck 66 10 1 (dualNumerators066 10 1) ∧
    integerMassCheck 66 10 1 (dualNumerators066 10 1) := by
  have hn : dualNumerators066 10 1 = ![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 86215139428, 1222686285911, 0, 788396879662, 1019185197635, 86215139429, 1142419996822, 42380745027, 861863417206, 243536919859] := rfl
  have he : residualNumerators 66 10 1 = 775057688183679 := rfl
  have hr : radiusNumerators 10 = 10683139 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_11_0 :
    integerResidualCheck 66 11 0 (dualNumerators066 11 0) ∧
    integerMassCheck 66 11 0 (dualNumerators066 11 0) := by
  have hn : dualNumerators066 11 0 = ![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 53583766880, 759914527140, 0, 489998333105, 633436104137, 53583766880, 710028043730, 26340152980, 535658687508, 151361183509] := rfl
  have he : residualNumerators 66 11 0 = 509208583002968 := rfl
  have hr : radiusNumerators 11 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_11_1 :
    integerResidualCheck 66 11 1 (dualNumerators066 11 1) ∧
    integerMassCheck 66 11 1 (dualNumerators066 11 1) := by
  have hn : dualNumerators066 11 1 = ![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 48862235961, 692954696876, 0, 446822154676, 577620913742, 48862235962, 647463958437, 24019191727, 488459149252, 138024000452] := rfl
  have he : residualNumerators 66 11 1 = 463252337673565 := rfl
  have hr : radiusNumerators 11 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_12_0 :
    integerResidualCheck 66 12 0 (dualNumerators066 12 0) ∧
    integerMassCheck 66 12 0 (dualNumerators066 12 0) := by
  have hn : dualNumerators066 12 0 = ![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 112780107974, 1599425486726, 0, 1031321016287, 1333220793899, 112780107975, 1494427213684, 55439277044, 1127424369963, 318576531911] := rfl
  have he : residualNumerators 66 12 0 = 988147337483809 := rfl
  have hr : radiusNumerators 12 = 16348076 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_12_1 :
    integerResidualCheck 66 12 1 (dualNumerators066 12 1) ∧
    integerMassCheck 66 12 1 (dualNumerators066 12 1) := by
  have hn : dualNumerators066 12 1 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 66 12 1 = 66000000000000 := rfl
  have hr : radiusNumerators 12 = 16348076 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_13_0 :
    integerResidualCheck 66 13 0 (dualNumerators066 13 0) ∧
    integerMassCheck 66 13 0 (dualNumerators066 13 0) := by
  have hn : dualNumerators066 13 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 66 13 0 = 33000000000000 := rfl
  have hr : radiusNumerators 13 = 13962901 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_13_1 :
    integerResidualCheck 66 13 1 (dualNumerators066 13 1) ∧
    integerMassCheck 66 13 1 (dualNumerators066 13 1) := by
  have hn : dualNumerators066 13 1 = ![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 95245651777, 1350755250097, 0, 870976665588, 1125938658502, 95245651778, 1262081554611, 46819870729, 952138376845, 269045933435] := rfl
  have he : residualNumerators 66 13 1 = 860313388414246 := rfl
  have hr : radiusNumerators 13 = 13962901 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_14_0 :
    integerResidualCheck 66 14 0 (dualNumerators066 14 0) ∧
    integerMassCheck 66 14 0 (dualNumerators066 14 0) := by
  have hn : dualNumerators066 14 0 = ![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 112780107974, 1599425486727, 0, 1031321016288, 1333220793900, 112780107975, 1494427213685, 55439277044, 1127424369964, 318576531911] := rfl
  have he : residualNumerators 66 14 0 = 1052148802185920 := rfl
  have hr : radiusNumerators 14 = 20161291 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_14_1 :
    integerResidualCheck 66 14 1 (dualNumerators066 14 1) ∧
    integerMassCheck 66 14 1 (dualNumerators066 14 1) := by
  have hn : dualNumerators066 14 1 = ![561968834605, 103456879454, 561968834605, 0, 1, 844525275673, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 0, 1000000000000, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 95245651777, 1350755250096, 0, 870976665588, 1125938658501, 95245651778, 1262081554610, 46819870729, 952138376844, 269045933435] := rfl
  have he : residualNumerators 66 14 1 = 892735780703851 := rfl
  have hr : radiusNumerators 14 = 20161291 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_15_0 :
    integerResidualCheck 66 15 0 (dualNumerators066 15 0) ∧
    integerMassCheck 66 15 0 (dualNumerators066 15 0) := by
  have hn : dualNumerators066 15 0 = ![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819834, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819834, 475117180167, 0, 736368196709, 813498294019, 53583766880, 759914527140, 0, 489998333105, 633436104137, 53583766880, 710028043729, 26340152980, 535658687508, 151361183509] := rfl
  have he : residualNumerators 66 15 0 = 475342376985053 := rfl
  have hr : radiusNumerators 15 = 12900283 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_15_1 :
    integerResidualCheck 66 15 1 (dualNumerators066 15 1) ∧
    integerMassCheck 66 15 1 (dualNumerators066 15 1) := by
  have hn : dualNumerators066 15 1 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 66 15 1 = 33000000000000 := rfl
  have hr : radiusNumerators 15 = 12900283 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_16_0 :
    integerResidualCheck 66 16 0 (dualNumerators066 16 0) ∧
    integerMassCheck 66 16 0 (dualNumerators066 16 0) := by
  have hn : dualNumerators066 16 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 66 16 0 = 66000000000000 := rfl
  have hr : radiusNumerators 16 = 10683060 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_16_1 :
    integerResidualCheck 66 16 1 (dualNumerators066 16 1) ∧
    integerMassCheck 66 16 1 (dualNumerators066 16 1) := by
  have hn : dualNumerators066 16 1 = ![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 86215139428, 1222686285911, 0, 788396879662, 1019185197635, 86215139429, 1142419996822, 42380745027, 861863417206, 243536919859] := rfl
  have he : residualNumerators 66 16 1 = 741546684978254 := rfl
  have hr : radiusNumerators 16 = 10683060 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_17_0 :
    integerResidualCheck 66 17 0 (dualNumerators066 17 0) ∧
    integerMassCheck 66 17 0 (dualNumerators066 17 0) := by
  have hn : dualNumerators066 17 0 = ![602334801078, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546386, 0, 844525275676, 602334801077, 905187143137, 0, 1184097183123, 0, 1071829546386, 0, 0, 1000000000001, 2028622458797, 1713222941254, 933538524390, 1402919220984, 933538524390, 1105400337065, 905187143137, 0, 1184097183123, 0, 0, 0, 1402919220984, 1549866490728, 102087103740, 1447779386989, 0, 933538524390, 1206814321600, 102087103741, 1352736300180, 50182920805, 1020530044550, 288371380791] := rfl
  have he : residualNumerators 66 17 0 = 957012015845737 := rfl
  have hr : radiusNumerators 17 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_17_1 :
    integerResidualCheck 66 17 1 (dualNumerators066 17 1) ∧
    integerMassCheck 66 17 1 (dualNumerators066 17 1) := by
  have hn : dualNumerators066 17 1 = ![201148953074, 37030955649, 201148953074, 0, 1, 302286113723, 357936135756, 0, 282028158995, 201148953074, 0, 0, 0, 395427772555, 55650022034, 302286113723, 636234862349, 0, 677455931550, 572128657349, 311754022014, 468503118271, 311754022014, 369147059294, 0, 0, 0, 395427772555, 0, 302286113723, 468503118271, 517575975116, 34091860545, 483484114571, 0, 311754022014, 403014132522, 34091860545, 451744594666, 16758523606, 340804731313, 96301261755] := rfl
  have he : residualNumerators 66 17 1 = 327390631909333 := rfl
  have hr : radiusNumerators 17 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_18_0 :
    integerResidualCheck 66 18 0 (dualNumerators066 18 0) ∧
    integerMassCheck 66 18 0 (dualNumerators066 18 0) := by
  have hn : dualNumerators066 18 0 = ![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 170971222814, 1097425476614, 0, 763999473637, 900221849434, 170971222815, 953519106044, 33030453619, 835192545885, 236000526363] := rfl
  have he : residualNumerators 66 18 0 = 623128997634128 := rfl
  have hr : radiusNumerators 18 = 13565580 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_18_1 :
    integerResidualCheck 66 18 1 (dualNumerators066 18 1) ∧
    integerMassCheck 66 18 1 (dualNumerators066 18 1) := by
  have hn : dualNumerators066 18 1 = ![543792441172, 100110656623, 543792441172, 0, 1, 180671424657, 213932525007, 0, 71292007252, 50847095100, 180671424657, 0, 92181412018, 500721469249, 213932525007, 0, 0, 500721469250, 171249542446, 144624567044, 842805682483, 280016586907, 78806208846, 93314209907, 180671424657, 1, 92181412018, 500721469249, 0, 0, 280016586907, 776051426377, 0, 130834560290, 78806208846, 0, 110493093096, 1, 188935308970, 91081277938, 86149742858, 24343350238] := rfl
  have he : residualNumerators 66 18 1 = 259747327577377 := rfl
  have hr : radiusNumerators 18 = 13565580 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_19_0 :
    integerResidualCheck 66 19 0 (dualNumerators066 19 0) ∧
    integerMassCheck 66 19 0 (dualNumerators066 19 0) := by
  have hn : dualNumerators066 19 0 = ![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 230658067063, 840535005185, 0, 645216866088, 673991557577, 230658067064, 653752451905, 19962510160, 705341215054, 199308409586] := rfl
  have he : residualNumerators 66 19 0 = 632380721060320 := rfl
  have hr : radiusNumerators 19 = 8248658 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_19_1 :
    integerResidualCheck 66 19 1 (dualNumerators066 19 1) ∧
    integerMassCheck 66 19 1 (dualNumerators066 19 1) := by
  have hn : dualNumerators066 19 1 = ![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 1, 987477735649, 0, 0, 763999473637, 109777015093, 350406455885, 645216866088, 1, 838241775551, 149235960098, 503065535987, 142151330101] := rfl
  have he : residualNumerators 66 19 1 = 514021689200491 := rfl
  have hr : radiusNumerators 19 = 8248658 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_20_0 :
    integerResidualCheck 66 20 0 (dualNumerators066 20 0) ∧
    integerMassCheck 66 20 0 (dualNumerators066 20 0) := by
  have hn : dualNumerators066 20 0 = ![581614421967, 107073576748, 581614421967, 0, 2, 2066609823264, 2447066870339, 0, 815473519328, 581614421966, 2066609823265, 0, 177764221089, 965599897142, 2447066870339, 0, 0, 965599897145, 1958837637558, 1654287895858, 901424703130, 3202969314486, 901424703130, 1067374451772, 2066609823264, 2, 177764221088, 965599897144, 0, 0, 3202969314486, 1496550924034, 0, 1496550924034, 901424703130, 0, 1263875081678, 1, 2161136251736, 1041833062750, 985423706049, 278451375631] := rfl
  have he : residualNumerators 66 20 0 = 1317604543217083 := rfl
  have hr : radiusNumerators 20 = 35312013 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_20_1 :
    integerResidualCheck 66 20 1 (dualNumerators066 20 1) ∧
    integerMassCheck 66 20 1 (dualNumerators066 20 1) := by
  have hn : dualNumerators066 20 1 = ![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 25837005087, 1204076434982, 564110399358, 1160334187225, 0, 0, 1344522571906, 379922014678] := rfl
  have he : residualNumerators 66 20 1 = 855005206964392 := rfl
  have hr : radiusNumerators 20 = 35312013 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_21_0 :
    integerResidualCheck 66 21 0 (dualNumerators066 21 0) ∧
    integerMassCheck 66 21 0 (dualNumerators066 21 0) := by
  have hn : dualNumerators066 21 0 = ![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 1, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 604293255477, 704608169863, 851509250277, 798941670661, 1020530044549, 288371380791] := rfl
  have he : residualNumerators 66 21 0 = 754447652319646 := rfl
  have hr : radiusNumerators 21 = 11182451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_21_1 :
    integerResidualCheck 66 21 1 (dualNumerators066 21 1) ∧
    integerMassCheck 66 21 1 (dualNumerators066 21 1) := by
  have hn : dualNumerators066 21 1 = ![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 860003851037, 963321782180, 3460174706, 161253783489, 75547476522, 155395681176, 0, 0, 180062781238, 50880376460] := rfl
  have he : residualNumerators 66 21 1 = 375152244602780 := rfl
  have hr : radiusNumerators 21 = 11182451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_22_0 :
    integerResidualCheck 66 22 0 (dualNumerators066 22 0) ∧
    integerMassCheck 66 22 0 (dualNumerators066 22 0) := by
  have hn : dualNumerators066 22 0 = ![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 510506833659, 253492639979, 460183470977, 0, 194101336204, 451115529884, 310954038967, 490382041752, 503065535987, 142151330101] := rfl
  have he : residualNumerators 66 22 0 = 470345765638443 := rfl
  have hr : radiusNumerators 22 = 6465674 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_22_1 :
    integerResidualCheck 66 22 1 (dualNumerators066 22 1) ∧
    integerMassCheck 66 22 1 (dualNumerators066 22 1) := by
  have hn : dualNumerators066 22 1 = ![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 9522456419, 111749239332, 1534493418, 71511669319, 33503252091, 68913760194, 0, 0, 79852948501, 22564063785] := rfl
  have he : residualNumerators 66 22 1 = 91397125170083 := rfl
  have hr : radiusNumerators 22 = 6465674 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_23_0 :
    integerResidualCheck 66 23 0 (dualNumerators066 23 0) ∧
    integerMassCheck 66 23 0 (dualNumerators066 23 0) := by
  have hn : dualNumerators066 23 0 = ![581614421966, 107073576748, 581614421967, 0, 2, 2066609823263, 2447066870339, 0, 815473519327, 581614421966, 2066609823265, 0, 177764221089, 965599897142, 2447066870339, 0, 0, 965599897144, 1958837637556, 1654287895857, 901424703129, 3202969314485, 901424703129, 1067374451772, 2066609823263, 2, 177764221088, 965599897143, 0, 0, 3202969314485, 1496550924032, 1000000000000, 496550924033, 901424703129, 0, 1263875081678, 0, 2161136251736, 1041833062749, 985423706048, 278451375631] := rfl
  have he : residualNumerators 66 23 0 = 1319627796307240 := rfl
  have hr : radiusNumerators 23 = 35297932 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_23_1 :
    integerResidualCheck 66 23 1 (dualNumerators066 23 1) ∧
    integerMassCheck 66 23 1 (dualNumerators066 23 1) := by
  have hn : dualNumerators066 23 1 = ![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 160334187224, 1881575790198, 25837005087, 1204076434982, 564110399358, 1160334187225, 0, 0, 1344522571906, 379922014678] := rfl
  have he : residualNumerators 66 23 1 = 855005206964392 := rfl
  have hr : radiusNumerators 23 = 35297932 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_24_0 :
    integerResidualCheck 66 24 0 (dualNumerators066 24 0) ∧
    integerMassCheck 66 24 0 (dualNumerators066 24 0) := by
  have hn : dualNumerators066 24 0 = ![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 384946583730, 686246488518, 569308312247, 737522866658, 835192545885, 236000526363] := rfl
  have he : residualNumerators 66 24 0 = 667884906521377 := rfl
  have hr : radiusNumerators 24 = 9356857 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_24_1 :
    integerResidualCheck 66 24 1 (dualNumerators066 24 1) ∧
    integerMassCheck 66 24 1 (dualNumerators066 24 1) := by
  have hn : dualNumerators066 24 1 = ![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623507, 113117556459, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 690777049383, 178822020994, 48434165160, 99625565721, 0, 0, 115439864933, 32619865948] := rfl
  have he : residualNumerators 66 24 1 = 232345440638621 := rfl
  have hr : radiusNumerators 24 = 9356857 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_25_0 :
    integerResidualCheck 66 25 0 (dualNumerators066 25 0) ∧
    integerMassCheck 66 25 0 (dualNumerators066 25 0) := by
  have hn : dualNumerators066 25 0 = ![34423495944, 6337268637, 34423495944, 0, 1, 22181646803, 26265225496, 0, 631959902239, 450728300227, 515126992874, 0, 137760279295, 748301940085, 609960421212, 0, 0, 748301940086, 1518022121617, 1282008050738, 53351822857, 34378591088, 698568688945, 827173216796, 515126992874, 1, 137760279295, 748301940085, 0, 0, 798378064725, 1159768101884, 638738616250, 521029485635, 53351822857, 0, 340714859712, 638738616250, 34378591088, 0, 763664612251, 215788863711] := rfl
  have he : residualNumerators 66 25 0 = 508481259994804 := rfl
  have hr : radiusNumerators 25 = 8671199 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_25_1 :
    integerResidualCheck 66 25 1 (dualNumerators066 25 1) ∧
    integerMassCheck 66 25 1 (dualNumerators066 25 1) := by
  have hn : dualNumerators066 25 1 = ![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 1, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 415529968297, 599898615461, 0, 0] := rfl
  have he : residualNumerators 66 25 1 = 222935526651450 := rfl
  have hr : radiusNumerators 25 = 8671199 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_26_0 :
    integerResidualCheck 66 26 0 (dualNumerators066 26 0) ∧
    integerMassCheck 66 26 0 (dualNumerators066 26 0) := by
  have hn : dualNumerators066 26 0 = ![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 1, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0] := rfl
  have he : residualNumerators 66 26 0 = 398909472332109 := rfl
  have hr : radiusNumerators 26 = 15099566 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_26_1 :
    integerResidualCheck 66 26 1 (dualNumerators066 26 1) ∧
    integerMassCheck 66 26 1 (dualNumerators066 26 1) := by
  have hn : dualNumerators066 26 1 = ![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 1025837005087, 204076434982, 564110399358, 1160334187225, 0, 0, 1344522571906, 379922014678] := rfl
  have he : residualNumerators 66 26 1 = 855005206964392 := rfl
  have hr : radiusNumerators 26 = 15099566 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_27_0 :
    integerResidualCheck 66 27 0 (dualNumerators066 27 0) ∧
    integerMassCheck 66 27 0 (dualNumerators066 27 0) := by
  have hn : dualNumerators066 27 0 = ![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 1, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 286173900105, 455299762271, 595678484088, 168320989550] := rfl
  have he : residualNumerators 66 27 0 = 411871570759515 := rfl
  have hr : radiusNumerators 27 = 7338775 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_27_1 :
    integerResidualCheck 66 27 1 (dualNumerators066 27 1) ∧
    integerMassCheck 66 27 1 (dualNumerators066 27 1) := by
  have hn : dualNumerators066 27 1 = ![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583262, 988432197465, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 530765167249, 1001172773960, 0, 377837583379, 762995144865, 530765167250, 621055226706, 24161639382, 413046270426, 116714568052] := rfl
  have he : residualNumerators 66 27 1 = 548040961376557 := rfl
  have hr : radiusNumerators 27 = 7338775 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_28_0 :
    integerResidualCheck 66 28 0 (dualNumerators066 28 0) ∧
    integerMassCheck 66 28 0 (dualNumerators066 28 0) := by
  have hn : dualNumerators066 28 0 = ![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 1, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 450383711774, 395438493575, 503065535987, 142151330101] := rfl
  have he : residualNumerators 66 28 0 = 286784861133797 := rfl
  have hr : radiusNumerators 28 = 10335557 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_28_1 :
    integerResidualCheck 66 28 1 (dualNumerators066 28 1) ∧
    integerMassCheck 66 28 1 (dualNumerators066 28 1) := by
  have hn : dualNumerators066 28 1 = ![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 426731607120, 507685338329, 2156352207, 100492021777, 362407121329, 426731607121, 0, 0, 112213633330, 31708229033] := rfl
  have he : residualNumerators 66 28 1 = 299207140313493 := rfl
  have hr : radiusNumerators 28 = 10335557 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_29_0 :
    integerResidualCheck 66 29 0 (dualNumerators066 29 0) ∧
    integerMassCheck 66 29 0 (dualNumerators066 29 0) := by
  have hn : dualNumerators066 29 0 = ![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 1, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0] := rfl
  have he : residualNumerators 66 29 0 = 398909472332109 := rfl
  have hr : radiusNumerators 29 = 40352153 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_29_1 :
    integerResidualCheck 66 29 1 (dualNumerators066 29 1) ∧
    integerMassCheck 66 29 1 (dualNumerators066 29 1) := by
  have hn : dualNumerators066 29 1 = ![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 160334187224, 1881575790198, 25837005087, 1204076434982, 1564110399358, 160334187225, 0, 0, 1344522571906, 379922014678] := rfl
  have he : residualNumerators 66 29 1 = 855005206964392 := rfl
  have hr : radiusNumerators 29 = 40352153 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_30_0 :
    integerResidualCheck 66 30 0 (dualNumerators066 30 0) ∧
    integerMassCheck 66 30 0 (dualNumerators066 30 0) := by
  have hn : dualNumerators066 30 0 = ![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 115599349926, 0, 37915592377, 205954223378, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 1, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 21025270168, 298176279270, 0, 192266201784, 248548506366, 21025270168, 174289307832, 4874250969, 269573776534, 0] := rfl
  have he : residualNumerators 66 30 0 = 219402929692006 := rfl
  have hr : radiusNumerators 30 = 7680628 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_30_1 :
    integerResidualCheck 66 30 1 (dualNumerators066 30 1) ∧
    integerMassCheck 66 30 1 (dualNumerators066 30 1) := by
  have hn : dualNumerators066 30 1 = ![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195716, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 1, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 59587751998, 845061872643, 0, 544901951702, 704411721639, 59587751998, 893898125793, 34752663293, 536287180313, 227712293325] := rfl
  have he : residualNumerators 66 30 1 = 554712865621407 := rfl
  have hr : radiusNumerators 30 = 7680628 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_31_0 :
    integerResidualCheck 66 31 0 (dualNumerators066 31 0) ∧
    integerMassCheck 66 31 0 (dualNumerators066 31 0) := by
  have hn : dualNumerators066 31 0 = ![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1719079079316, 0, 1491143233587, 0, 2035556695381, 0, 1259308150413, 1, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079316, 0, 1491143233587, 0, 0, 0, 2664343059941, 1951759503826, 0, 1951759503826, 743462473285, 1537550536267, 1648310233016, 2, 1836249633286, 828093426656, 1648310233018, 0] := rfl
  have he : residualNumerators 66 31 0 = 1677990120061949 := rfl
  have hr : radiusNumerators 31 = 32891612 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_31_1 :
    integerResidualCheck 66 31 1 (dualNumerators066 31 1) ∧
    integerMassCheck 66 31 1 (dualNumerators066 31 1) := by
  have hn : dualNumerators066 31 1 = ![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 556963843680, 992902647048, 725570984152, 37986262977, 845258320866, 704608169862] := rfl
  have he : residualNumerators 66 31 1 = 650885257669374 := rfl
  have hr : radiusNumerators 31 = 32891612 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_32_0 :
    integerResidualCheck 66 32 0 (dualNumerators066 32 0) ∧
    integerMassCheck 66 32 0 (dualNumerators066 32 0) := by
  have hn : dualNumerators066 32 0 = ![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 0, 2079538667399, 1160276651773, 0, 382837210862, 2079538667397, 979882959195, 1, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 1160276651773, 0, 0, 0, 3223007296772, 1518687763292, 100033413308, 1418654349984, 0, 914758491801, 1182536788648, 100033413309, 3081882171380, 141125125392, 0, 1282570201956] := rfl
  have he : residualNumerators 66 32 0 = 1328270091501730 := rfl
  have hr : radiusNumerators 32 = 67647473 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck066_32_1 :
    integerResidualCheck 66 32 1 (dualNumerators066 32 1) ∧
    integerMassCheck 66 32 1 (dualNumerators066 32 1) := by
  have hn : dualNumerators066 32 1 = ![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1946401957496, 0, 638403098873, 3467750500271, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957494, 2, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 354012605063, 5020537693515, 0, 3237278684975, 4184930967463, 354012605067, 2934593059134, 82070112273, 4538943572529, 0] := rfl
  have he : residualNumerators 66 32 1 = 2884268411724383 := rfl
  have hr : radiusNumerators 32 = 67647473 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots066]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature066_entry]
    rw [hn, he, hr]
    decide

theorem integerChecks066 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 66 j s (dualNumerators066 j s) ∧
    integerMassCheck 66 j s (dualNumerators066 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck066_0_0
    · exact integerCheck066_0_1
  · fin_cases s
    · exact integerCheck066_1_0
    · exact integerCheck066_1_1
  · fin_cases s
    · exact integerCheck066_2_0
    · exact integerCheck066_2_1
  · fin_cases s
    · exact integerCheck066_3_0
    · exact integerCheck066_3_1
  · fin_cases s
    · exact integerCheck066_4_0
    · exact integerCheck066_4_1
  · fin_cases s
    · exact integerCheck066_5_0
    · exact integerCheck066_5_1
  · fin_cases s
    · exact integerCheck066_6_0
    · exact integerCheck066_6_1
  · fin_cases s
    · exact integerCheck066_7_0
    · exact integerCheck066_7_1
  · fin_cases s
    · exact integerCheck066_8_0
    · exact integerCheck066_8_1
  · fin_cases s
    · exact integerCheck066_9_0
    · exact integerCheck066_9_1
  · fin_cases s
    · exact integerCheck066_10_0
    · exact integerCheck066_10_1
  · fin_cases s
    · exact integerCheck066_11_0
    · exact integerCheck066_11_1
  · fin_cases s
    · exact integerCheck066_12_0
    · exact integerCheck066_12_1
  · fin_cases s
    · exact integerCheck066_13_0
    · exact integerCheck066_13_1
  · fin_cases s
    · exact integerCheck066_14_0
    · exact integerCheck066_14_1
  · fin_cases s
    · exact integerCheck066_15_0
    · exact integerCheck066_15_1
  · fin_cases s
    · exact integerCheck066_16_0
    · exact integerCheck066_16_1
  · fin_cases s
    · exact integerCheck066_17_0
    · exact integerCheck066_17_1
  · fin_cases s
    · exact integerCheck066_18_0
    · exact integerCheck066_18_1
  · fin_cases s
    · exact integerCheck066_19_0
    · exact integerCheck066_19_1
  · fin_cases s
    · exact integerCheck066_20_0
    · exact integerCheck066_20_1
  · fin_cases s
    · exact integerCheck066_21_0
    · exact integerCheck066_21_1
  · fin_cases s
    · exact integerCheck066_22_0
    · exact integerCheck066_22_1
  · fin_cases s
    · exact integerCheck066_23_0
    · exact integerCheck066_23_1
  · fin_cases s
    · exact integerCheck066_24_0
    · exact integerCheck066_24_1
  · fin_cases s
    · exact integerCheck066_25_0
    · exact integerCheck066_25_1
  · fin_cases s
    · exact integerCheck066_26_0
    · exact integerCheck066_26_1
  · fin_cases s
    · exact integerCheck066_27_0
    · exact integerCheck066_27_1
  · fin_cases s
    · exact integerCheck066_28_0
    · exact integerCheck066_28_1
  · fin_cases s
    · exact integerCheck066_29_0
    · exact integerCheck066_29_1
  · fin_cases s
    · exact integerCheck066_30_0
    · exact integerCheck066_30_1
  · fin_cases s
    · exact integerCheck066_31_0
    · exact integerCheck066_31_1
  · fin_cases s
    · exact integerCheck066_32_0
    · exact integerCheck066_32_1

end ElevenSquare.Tasks.T06
