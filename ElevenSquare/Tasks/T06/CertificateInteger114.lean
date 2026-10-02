import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.DataDual114
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
import ElevenSquare.Tasks.T06.SparseColumn32
import ElevenSquare.Tasks.T06.SparseColumn35
import ElevenSquare.Tasks.T06.SparseColumn36
import ElevenSquare.Tasks.T06.SparseColumn37
import ElevenSquare.Tasks.T06.SparseColumn38
import ElevenSquare.Tasks.T06.SparseColumn39
import ElevenSquare.Tasks.T06.SparseColumn40
import ElevenSquare.Tasks.T06.SparseColumn48
import ElevenSquare.Tasks.T06.SparseColumn54
import ElevenSquare.Tasks.T06.SparseColumn56
import ElevenSquare.Tasks.T06.SparseColumn58

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix114 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral43, roundedGradientLiteral44, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix114_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = branchIntegerMatrix114 := by
  change roundedGradients ∘ branchRows 114 = branchIntegerMatrix114
  rw [show branchRows 114 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 52, 53, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral43_eq, roundedGradientLiteral44_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix114]

theorem branchColumn114_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 0) i) = _
  rw [branchColumn114_0]
  exact sparseColumn00_sum n

theorem branchColumn114_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 1) i) = _
  rw [branchColumn114_1]
  exact sparseColumn01_sum n

theorem branchColumn114_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 2) i) = _
  rw [branchColumn114_2]
  exact sparseColumn02_sum n

theorem branchColumn114_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 3) i) = _
  rw [branchColumn114_3]
  exact sparseColumn03_sum n

theorem branchColumn114_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 4) i) = _
  rw [branchColumn114_4]
  exact sparseColumn04_sum n

theorem branchColumn114_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 5) i) = _
  rw [branchColumn114_5]
  exact sparseColumn05_sum n

theorem branchColumn114_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 6) i) = _
  rw [branchColumn114_6]
  exact sparseColumn06_sum n

theorem branchColumn114_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 7) i) = _
  rw [branchColumn114_7]
  exact sparseColumn07_sum n

theorem branchColumn114_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 8) i) = _
  rw [branchColumn114_8]
  exact sparseColumn08_sum n

theorem branchColumn114_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 9) i) = _
  rw [branchColumn114_9]
  exact sparseColumn09_sum n

theorem branchColumn114_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 10) i) = _
  rw [branchColumn114_10]
  exact sparseColumn10_sum n

theorem branchColumn114_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 11) i) = _
  rw [branchColumn114_11]
  exact sparseColumn11_sum n

theorem branchColumn114_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 12) i) = _
  rw [branchColumn114_12]
  exact sparseColumn35_sum n

theorem branchColumn114_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 13) i) = _
  rw [branchColumn114_13]
  exact sparseColumn36_sum n

theorem branchColumn114_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 14) = sparseColumn37 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 14) = sparseDot37 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 14) i) = _
  rw [branchColumn114_14]
  exact sparseColumn37_sum n

theorem branchColumn114_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 15) i) = _
  rw [branchColumn114_15]
  exact sparseColumn38_sum n

theorem branchColumn114_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 16) i) = _
  rw [branchColumn114_16]
  exact sparseColumn39_sum n

theorem branchColumn114_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 17) = sparseColumn40 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 17) = sparseDot40 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 17) i) = _
  rw [branchColumn114_17]
  exact sparseColumn40_sum n

theorem branchColumn114_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 18) i) = _
  rw [branchColumn114_18]
  exact sparseColumn18_sum n

theorem branchColumn114_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 19) i) = _
  rw [branchColumn114_19]
  exact sparseColumn19_sum n

theorem branchColumn114_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 20) = sparseColumn58 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 20) = sparseDot58 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 20) i) = _
  rw [branchColumn114_20]
  exact sparseColumn58_sum n

theorem branchColumn114_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 21) i) = _
  rw [branchColumn114_21]
  exact sparseColumn21_sum n

theorem branchColumn114_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 22) i) = _
  rw [branchColumn114_22]
  exact sparseColumn22_sum n

theorem branchColumn114_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 23) = sparseColumn54 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 23) = sparseDot54 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 23) i) = _
  rw [branchColumn114_23]
  exact sparseColumn54_sum n

theorem branchColumn114_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 24) i) = _
  rw [branchColumn114_24]
  exact sparseColumn24_sum n

theorem branchColumn114_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 25) i) = _
  rw [branchColumn114_25]
  exact sparseColumn25_sum n

theorem branchColumn114_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 26) = sparseColumn56 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 26) = sparseDot56 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 26) i) = _
  rw [branchColumn114_26]
  exact sparseColumn56_sum n

theorem branchColumn114_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 27) i) = _
  rw [branchColumn114_27]
  exact sparseColumn27_sum n

theorem branchColumn114_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 28) i) = _
  rw [branchColumn114_28]
  exact sparseColumn28_sum n

theorem branchColumn114_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 29) = sparseColumn48 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 29) = sparseDot48 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 29) i) = _
  rw [branchColumn114_29]
  exact sparseColumn48_sum n

theorem branchColumn114_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 30) i) = _
  rw [branchColumn114_30]
  exact sparseColumn30_sum n

theorem branchColumn114_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 31) i) = _
  rw [branchColumn114_31]
  exact sparseColumn31_sum n

theorem branchColumn114_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 114 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 114 i)) = _
  rw [branchIntegerMatrix114_eq]
  simp only [branchIntegerMatrix114, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot114_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 114 i) 32) i) = _
  rw [branchColumn114_32]
  exact sparseColumn32_sum n

def branchSparseDots114 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot37, sparseDot38, sparseDot39, sparseDot40, sparseDot18, sparseDot19, sparseDot58, sparseDot21, sparseDot22, sparseDot54, sparseDot24, sparseDot25, sparseDot56, sparseDot27, sparseDot28, sparseDot48, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot114_0 :
    branchSparseDots114 0 = sparseDot00 := rfl

private theorem branchSparseDot114_1 :
    branchSparseDots114 1 = sparseDot01 := rfl

private theorem branchSparseDot114_2 :
    branchSparseDots114 2 = sparseDot02 := rfl

private theorem branchSparseDot114_3 :
    branchSparseDots114 3 = sparseDot03 := rfl

private theorem branchSparseDot114_4 :
    branchSparseDots114 4 = sparseDot04 := rfl

private theorem branchSparseDot114_5 :
    branchSparseDots114 5 = sparseDot05 := rfl

private theorem branchSparseDot114_6 :
    branchSparseDots114 6 = sparseDot06 := rfl

private theorem branchSparseDot114_7 :
    branchSparseDots114 7 = sparseDot07 := rfl

private theorem branchSparseDot114_8 :
    branchSparseDots114 8 = sparseDot08 := rfl

private theorem branchSparseDot114_9 :
    branchSparseDots114 9 = sparseDot09 := rfl

private theorem branchSparseDot114_10 :
    branchSparseDots114 10 = sparseDot10 := rfl

private theorem branchSparseDot114_11 :
    branchSparseDots114 11 = sparseDot11 := rfl

private theorem branchSparseDot114_12 :
    branchSparseDots114 12 = sparseDot35 := rfl

private theorem branchSparseDot114_13 :
    branchSparseDots114 13 = sparseDot36 := rfl

private theorem branchSparseDot114_14 :
    branchSparseDots114 14 = sparseDot37 := rfl

private theorem branchSparseDot114_15 :
    branchSparseDots114 15 = sparseDot38 := rfl

private theorem branchSparseDot114_16 :
    branchSparseDots114 16 = sparseDot39 := rfl

private theorem branchSparseDot114_17 :
    branchSparseDots114 17 = sparseDot40 := rfl

private theorem branchSparseDot114_18 :
    branchSparseDots114 18 = sparseDot18 := rfl

private theorem branchSparseDot114_19 :
    branchSparseDots114 19 = sparseDot19 := rfl

private theorem branchSparseDot114_20 :
    branchSparseDots114 20 = sparseDot58 := rfl

private theorem branchSparseDot114_21 :
    branchSparseDots114 21 = sparseDot21 := rfl

private theorem branchSparseDot114_22 :
    branchSparseDots114 22 = sparseDot22 := rfl

private theorem branchSparseDot114_23 :
    branchSparseDots114 23 = sparseDot54 := rfl

private theorem branchSparseDot114_24 :
    branchSparseDots114 24 = sparseDot24 := rfl

private theorem branchSparseDot114_25 :
    branchSparseDots114 25 = sparseDot25 := rfl

private theorem branchSparseDot114_26 :
    branchSparseDots114 26 = sparseDot56 := rfl

private theorem branchSparseDot114_27 :
    branchSparseDots114 27 = sparseDot27 := rfl

private theorem branchSparseDot114_28 :
    branchSparseDots114 28 = sparseDot28 := rfl

private theorem branchSparseDot114_29 :
    branchSparseDots114 29 = sparseDot48 := rfl

private theorem branchSparseDot114_30 :
    branchSparseDots114 30 = sparseDot30 := rfl

private theorem branchSparseDot114_31 :
    branchSparseDots114 31 = sparseDot31 := rfl

private theorem branchSparseDot114_32 :
    branchSparseDots114 32 = sparseDot32 := rfl

theorem branchDots114 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 114 i) k) = branchSparseDots114 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot114_0 n
      _ = _ := congrFun branchSparseDot114_0.symm n
  · calc
      _ = sparseDot01 n := branchDot114_1 n
      _ = _ := congrFun branchSparseDot114_1.symm n
  · calc
      _ = sparseDot02 n := branchDot114_2 n
      _ = _ := congrFun branchSparseDot114_2.symm n
  · calc
      _ = sparseDot03 n := branchDot114_3 n
      _ = _ := congrFun branchSparseDot114_3.symm n
  · calc
      _ = sparseDot04 n := branchDot114_4 n
      _ = _ := congrFun branchSparseDot114_4.symm n
  · calc
      _ = sparseDot05 n := branchDot114_5 n
      _ = _ := congrFun branchSparseDot114_5.symm n
  · calc
      _ = sparseDot06 n := branchDot114_6 n
      _ = _ := congrFun branchSparseDot114_6.symm n
  · calc
      _ = sparseDot07 n := branchDot114_7 n
      _ = _ := congrFun branchSparseDot114_7.symm n
  · calc
      _ = sparseDot08 n := branchDot114_8 n
      _ = _ := congrFun branchSparseDot114_8.symm n
  · calc
      _ = sparseDot09 n := branchDot114_9 n
      _ = _ := congrFun branchSparseDot114_9.symm n
  · calc
      _ = sparseDot10 n := branchDot114_10 n
      _ = _ := congrFun branchSparseDot114_10.symm n
  · calc
      _ = sparseDot11 n := branchDot114_11 n
      _ = _ := congrFun branchSparseDot114_11.symm n
  · calc
      _ = sparseDot35 n := branchDot114_12 n
      _ = _ := congrFun branchSparseDot114_12.symm n
  · calc
      _ = sparseDot36 n := branchDot114_13 n
      _ = _ := congrFun branchSparseDot114_13.symm n
  · calc
      _ = sparseDot37 n := branchDot114_14 n
      _ = _ := congrFun branchSparseDot114_14.symm n
  · calc
      _ = sparseDot38 n := branchDot114_15 n
      _ = _ := congrFun branchSparseDot114_15.symm n
  · calc
      _ = sparseDot39 n := branchDot114_16 n
      _ = _ := congrFun branchSparseDot114_16.symm n
  · calc
      _ = sparseDot40 n := branchDot114_17 n
      _ = _ := congrFun branchSparseDot114_17.symm n
  · calc
      _ = sparseDot18 n := branchDot114_18 n
      _ = _ := congrFun branchSparseDot114_18.symm n
  · calc
      _ = sparseDot19 n := branchDot114_19 n
      _ = _ := congrFun branchSparseDot114_19.symm n
  · calc
      _ = sparseDot58 n := branchDot114_20 n
      _ = _ := congrFun branchSparseDot114_20.symm n
  · calc
      _ = sparseDot21 n := branchDot114_21 n
      _ = _ := congrFun branchSparseDot114_21.symm n
  · calc
      _ = sparseDot22 n := branchDot114_22 n
      _ = _ := congrFun branchSparseDot114_22.symm n
  · calc
      _ = sparseDot54 n := branchDot114_23 n
      _ = _ := congrFun branchSparseDot114_23.symm n
  · calc
      _ = sparseDot24 n := branchDot114_24 n
      _ = _ := congrFun branchSparseDot114_24.symm n
  · calc
      _ = sparseDot25 n := branchDot114_25 n
      _ = _ := congrFun branchSparseDot114_25.symm n
  · calc
      _ = sparseDot56 n := branchDot114_26 n
      _ = _ := congrFun branchSparseDot114_26.symm n
  · calc
      _ = sparseDot27 n := branchDot114_27 n
      _ = _ := congrFun branchSparseDot114_27.symm n
  · calc
      _ = sparseDot28 n := branchDot114_28 n
      _ = _ := congrFun branchSparseDot114_28.symm n
  · calc
      _ = sparseDot48 n := branchDot114_29 n
      _ = _ := congrFun branchSparseDot114_29.symm n
  · calc
      _ = sparseDot30 n := branchDot114_30 n
      _ = _ := congrFun branchSparseDot114_30.symm n
  · calc
      _ = sparseDot31 n := branchDot114_31 n
      _ = _ := congrFun branchSparseDot114_31.symm n
  · calc
      _ = sparseDot32 n := branchDot114_32 n
      _ = _ := congrFun branchSparseDot114_32.symm n

def branchIntegerCurvature114 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101955390, 101955390, 79086693, 79086693, 106371291, 106371291, 48290998, 48290998, 204734428, 204734428]

theorem branchIntegerCurvature114_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 114 i)) = branchIntegerCurvature114 := by
  change curvatureNumerators ∘ branchRows 114 = branchIntegerCurvature114
  rw [show branchRows 114 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 52, 53, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature114_entry (i : Fin 42) :
    curvatureNumerators (branchRows 114 i) = branchIntegerCurvature114 i :=
  congrFun branchIntegerCurvature114_eq i

theorem integerCheck114_0_0 :
    integerResidualCheck 114 0 0 (dualNumerators114 0 0) ∧
    integerMassCheck 114 0 0 (dualNumerators114 0 0) := by
  have hn : dualNumerators114 0 0 = ![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1901003851212, 272042472855, 74854042823, 1234047382517, 1835192545884, 0, 1821798773483, 145214820501, 1430871029972, 404321515913] := rfl
  have he : residualNumerators 114 0 0 = 1302007150786888 := rfl
  have hr : radiusNumerators 0 = 18767167 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_0_1 :
    integerResidualCheck 114 0 1 (dualNumerators114 0 1) ∧
    integerMassCheck 114 0 1 (dualNumerators114 0 1) := by
  have hn : dualNumerators114 0 1 = ![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 114 0 1 = 33000000000000 := rfl
  have hr : radiusNumerators 0 = 18767167 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_1_0 :
    integerResidualCheck 114 1 0 (dualNumerators114 1 0) ∧
    integerMassCheck 114 1 0 (dualNumerators114 1 0) := by
  have hn : dualNumerators114 1 0 = ![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 2250973305323, 322124725797, 88634461252, 1461232029476, 2173046324067, 0, 2157186795895, 171948459903, 1694290356000, 478755968067] := rfl
  have he : residualNumerators 114 1 0 = 1546830891322960 := rfl
  have hr : radiusNumerators 1 = 22176635 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_1_1 :
    integerResidualCheck 114 1 1 (dualNumerators114 1 1) ∧
    integerMassCheck 114 1 1 (dualNumerators114 1 1) := by
  have hn : dualNumerators114 1 1 = ![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 114 1 1 = 33000000000000 := rfl
  have hr : radiusNumerators 1 = 22176635 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_2_0 :
    integerResidualCheck 114 2 0 (dualNumerators114 2 0) ∧
    integerMassCheck 114 2 0 (dualNumerators114 2 0) := by
  have hn : dualNumerators114 2 0 = ![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 2250973305325, 322124725797, 88634461252, 1461232029477, 2173046324068, 0, 2157186795897, 171948459903, 1694290356001, 478755968068] := rfl
  have he : residualNumerators 114 2 0 = 1583623970800476 := rfl
  have hr : radiusNumerators 2 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_2_1 :
    integerResidualCheck 114 2 1 (dualNumerators114 2 1) ∧
    integerMassCheck 114 2 1 (dualNumerators114 2 1) := by
  have hn : dualNumerators114 2 1 = ![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1901003851211, 272042472855, 74854042823, 1234047382516, 1835192545883, 0, 1821798773482, 145214820501, 1430871029971, 404321515912] := rfl
  have he : residualNumerators 114 2 1 = 1336560055716508 := rfl
  have hr : radiusNumerators 2 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_3_0 :
    integerResidualCheck 114 3 0 (dualNumerators114 3 0) ∧
    integerMassCheck 114 3 0 (dualNumerators114 3 0) := by
  have hn : dualNumerators114 3 0 = ![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 114 3 0 = 33000000000000 := rfl
  have hr : radiusNumerators 3 = 16360330 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_3_1 :
    integerResidualCheck 114 3 1 (dualNumerators114 3 1) ∧
    integerMassCheck 114 3 1 (dualNumerators114 3 1) := by
  have hn : dualNumerators114 3 1 = ![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000000, 0, 203380245200, 1104743927907, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1497855519021, 214350075679, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 1127424369963, 318576531911] := rfl
  have he : residualNumerators 114 3 1 = 1025410356255042 := rfl
  have hr : radiusNumerators 3 = 16360330 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_4_0 :
    integerResidualCheck 114 4 0 (dualNumerators114 4 0) ∧
    integerMassCheck 114 4 0 (dualNumerators114 4 0) := by
  have hn : dualNumerators114 4 0 = ![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757645, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1264976845121, 181024056754, 49809804896, 821166860693, 1221184310279, 0, 1212271749715, 96629675624, 952138376845, 269045933435] := rfl
  have he : residualNumerators 114 4 0 = 862749299355796 := rfl
  have hr : radiusNumerators 4 = 13760362 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_4_1 :
    integerResidualCheck 114 4 1 (dualNumerators114 4 1) ∧
    integerMassCheck 114 4 1 (dualNumerators114 4 1) := by
  have hn : dualNumerators114 4 1 = ![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 114 4 1 = 33000000000000 := rfl
  have hr : radiusNumerators 4 = 13760362 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_5_0 :
    integerResidualCheck 114 5 0 (dualNumerators114 5 0) ∧
    integerMassCheck 114 5 0 (dualNumerators114 5 0) := by
  have hn : dualNumerators114 5 0 = ![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245201, 1104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000000, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1497855519022, 214350075679, 58979649669, 972341366620, 1446000901875, 0, 1435447564017, 114418926712, 1127424369964, 318576531911] := rfl
  have he : residualNumerators 114 5 0 = 1053772874639064 := rfl
  have hr : radiusNumerators 5 = 17641130 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_5_1 :
    integerResidualCheck 114 5 1 (dualNumerators114 5 1) ∧
    integerMassCheck 114 5 1 (dualNumerators114 5 1) := by
  have hn : dualNumerators114 5 1 = ![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170264, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1264976845120, 181024056754, 49809804896, 821166860692, 1221184310279, 0, 1212271749715, 96629675624, 952138376844, 269045933435] := rfl
  have he : residualNumerators 114 5 1 = 897145115500685 := rfl
  have hr : radiusNumerators 5 = 17641130 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_6_0 :
    integerResidualCheck 114 6 0 (dualNumerators114 6 0) ∧
    integerMassCheck 114 6 0 (dualNumerators114 6 0) := by
  have hn : dualNumerators114 6 0 = ![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 877488274356, 957704271528, 103906894360, 5439901403, 1430871029972, 404321515913] := rfl
  have he : residualNumerators 114 6 0 = 720686095128156 := rfl
  have hr : radiusNumerators 6 = 8962451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_6_1 :
    integerResidualCheck 114 6 1 (dualNumerators114 6 1) ∧
    integerMassCheck 114 6 1 (dualNumerators114 6 1) := by
  have hn : dualNumerators114 6 1 = ![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 1, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 760187607595, 1097479190627, 0, 0] := rfl
  have he : residualNumerators 114 6 1 = 627777238175137 := rfl
  have hr : radiusNumerators 6 = 8962451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_7_0 :
    integerResidualCheck 114 7 0 (dualNumerators114 7 0) ∧
    integerMassCheck 114 7 0 (dualNumerators114 7 0) := by
  have hn : dualNumerators114 7 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 114 7 0 = 33000000000000 := rfl
  have hr : radiusNumerators 7 = 10424794 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_7_1 :
    integerResidualCheck 114 7 1 (dualNumerators114 7 1) ∧
    integerMassCheck 114 7 1 (dualNumerators114 7 1) := by
  have hn : dualNumerators114 7 1 = ![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646810, 830103123887, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675220, 1, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 1125486652664, 161062362899, 44317230626, 730616014740, 1086523162035, 0, 1078593397950, 85974229952, 847145178002, 239377984034] := rfl
  have he : residualNumerators 114 7 1 = 762571983486996 := rfl
  have hr : radiusNumerators 7 = 10424794 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_8_0 :
    integerResidualCheck 114 8 0 (dualNumerators114 8 0) ∧
    integerMassCheck 114 8 0 (dualNumerators114 8 0) := by
  have hn : dualNumerators114 8 0 = ![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293619, 1660206247774, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350440, 2, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 2250973305327, 322124725797, 88634461252, 1461232029479, 2173046324070, 0, 2157186795899, 171948459903, 1694290356003, 478755968068] := rfl
  have he : residualNumerators 114 8 0 = 1579158280977669 := rfl
  have hr : radiusNumerators 8 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_8_1 :
    integerResidualCheck 114 8 1 (dualNumerators114 8 1) ∧
    integerMassCheck 114 8 1 (dualNumerators114 8 1) := by
  have hn : dualNumerators114 8 1 = ![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590429, 217988955956, 0, 1402086139075, 1269150346660, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546384, 0, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1605445801500, 229746744383, 63216131150, 1042184205913, 1549866490725, 0, 1538555111396, 122637586316, 1208406751039, 341459739686] := rfl
  have he : residualNumerators 114 8 1 = 1129569419091620 := rfl
  have hr : radiusNumerators 8 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_9_0 :
    integerResidualCheck 114 9 0 (dualNumerators114 9 0) ∧
    integerMassCheck 114 9 0 (dualNumerators114 9 0) := by
  have hn : dualNumerators114 9 0 = ![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 1497855519021, 214350075679, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 1127424369963, 318576531911] := rfl
  have he : residualNumerators 114 9 0 = 1025812043689577 := rfl
  have hr : radiusNumerators 9 = 16350530 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_9_1 :
    integerResidualCheck 114 9 1 (dualNumerators114 9 1) ∧
    integerMassCheck 114 9 1 (dualNumerators114 9 1) := by
  have hn : dualNumerators114 9 1 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 114 9 1 = 33000000000000 := rfl
  have hr : radiusNumerators 9 = 16350530 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_10_0 :
    integerResidualCheck 114 10 0 (dualNumerators114 10 0) ∧
    integerMassCheck 114 10 0 (dualNumerators114 10 0) := by
  have hn : dualNumerators114 10 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 114 10 0 = 33000000000000 := rfl
  have hr : radiusNumerators 10 = 10683139 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_10_1 :
    integerResidualCheck 114 10 1 (dualNumerators114 10 1) ∧
    integerMassCheck 114 10 1 (dualNumerators114 10 1) := by
  have hn : dualNumerators114 10 1 = ![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 1145040776568, 163860648772, 45087194994, 743309684668, 1105400337064, 0, 1097332801829, 87467940020, 861863417206, 243536919859] := rfl
  have he : residualNumerators 114 10 1 = 777652167735970 := rfl
  have hr : radiusNumerators 10 = 10683139 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_11_0 :
    integerResidualCheck 114 11 0 (dualNumerators114 11 0) ∧
    integerMassCheck 114 11 0 (dualNumerators114 11 0) := by
  have hn : dualNumerators114 11 0 = ![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 711656890494, 101841403525, 28022244838, 461976088268, 687019871017, 0, 682005798892, 54362397817, 535658687508, 151361183509] := rfl
  have he : residualNumerators 114 11 0 = 507222460245702 := rfl
  have hr : radiusNumerators 11 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_11_1 :
    integerResidualCheck 114 11 1 (dualNumerators114 11 1) ∧
    integerMassCheck 114 11 1 (dualNumerators114 11 1) := by
  have hn : dualNumerators114 11 1 = ![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 648949279451, 92867653386, 25553066146, 421269088530, 626483149703, 0, 621910892291, 49572257873, 488459149252, 138024000452] := rfl
  have he : residualNumerators 114 11 1 = 463924212764311 := rfl
  have hr : radiusNumerators 11 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_12_0 :
    integerResidualCheck 114 12 0 (dualNumerators114 12 0) ∧
    integerMassCheck 114 12 0 (dualNumerators114 12 0) := by
  have hn : dualNumerators114 12 0 = ![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1497855519021, 214350075679, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 1127424369963, 318576531911] := rfl
  have he : residualNumerators 114 12 0 = 990410356255075 := rfl
  have hr : radiusNumerators 12 = 16348076 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_12_1 :
    integerResidualCheck 114 12 1 (dualNumerators114 12 1) ∧
    integerMassCheck 114 12 1 (dualNumerators114 12 1) := by
  have hn : dualNumerators114 12 1 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 114 12 1 = 66000000000000 := rfl
  have hr : radiusNumerators 12 = 16348076 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_13_0 :
    integerResidualCheck 114 13 0 (dualNumerators114 13 0) ∧
    integerMassCheck 114 13 0 (dualNumerators114 13 0) := by
  have hn : dualNumerators114 13 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 114 13 0 = 33000000000000 := rfl
  have hr : radiusNumerators 13 = 13962901 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_13_1 :
    integerResidualCheck 114 13 1 (dualNumerators114 13 1) ∧
    integerMassCheck 114 13 1 (dualNumerators114 13 1) := by
  have hn : dualNumerators114 13 1 = ![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000001, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1264976845121, 181024056754, 49809804896, 821166860693, 1221184310279, 0, 1212271749715, 96629675624, 952138376845, 269045933435] := rfl
  have he : residualNumerators 114 13 1 = 862758930921171 := rfl
  have hr : radiusNumerators 13 = 13962901 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_14_0 :
    integerResidualCheck 114 14 0 (dualNumerators114 14 0) ∧
    integerMassCheck 114 14 0 (dualNumerators114 14 0) := by
  have hn : dualNumerators114 14 0 = ![665425714059, 122502999536, 665425714059, 0, 1, 1000000000001, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1497855519022, 214350075679, 58979649669, 972341366620, 1446000901875, 0, 1435447564017, 114418926712, 1127424369964, 318576531911] := rfl
  have he : residualNumerators 114 14 0 = 1054312612435497 := rfl
  have hr : radiusNumerators 14 = 20161291 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_14_1 :
    integerResidualCheck 114 14 1 (dualNumerators114 14 1) ∧
    integerMassCheck 114 14 1 (dualNumerators114 14 1) := by
  have hn : dualNumerators114 14 1 = ![561968834605, 103456879454, 561968834605, 0, 1, 844525275673, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 0, 1000000000000, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1264976845120, 181024056754, 49809804896, 821166860692, 1221184310279, 0, 1212271749715, 96629675624, 952138376844, 269045933435] := rfl
  have he : residualNumerators 114 14 1 = 895645115500718 := rfl
  have hr : radiusNumerators 14 = 20161291 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_15_0 :
    integerResidualCheck 114 15 0 (dualNumerators114 15 0) ∧
    integerMassCheck 114 15 0 (dualNumerators114 15 0) := by
  have hn : dualNumerators114 15 0 = ![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819834, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819834, 475117180167, 0, 736368196709, 813498294019, 711656890494, 101841403525, 28022244838, 461976088267, 687019871016, 0, 682005798892, 54362397817, 535658687508, 151361183509] := rfl
  have he : residualNumerators 114 15 0 = 473201592923990 := rfl
  have hr : radiusNumerators 15 = 12900283 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_15_1 :
    integerResidualCheck 114 15 1 (dualNumerators114 15 1) ∧
    integerMassCheck 114 15 1 (dualNumerators114 15 1) := by
  have hn : dualNumerators114 15 1 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 114 15 1 = 33000000000000 := rfl
  have hr : radiusNumerators 15 = 12900283 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_16_0 :
    integerResidualCheck 114 16 0 (dualNumerators114 16 0) ∧
    integerMassCheck 114 16 0 (dualNumerators114 16 0) := by
  have hn : dualNumerators114 16 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 114 16 0 = 66000000000000 := rfl
  have hr : radiusNumerators 16 = 10683060 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_16_1 :
    integerResidualCheck 114 16 1 (dualNumerators114 16 1) ∧
    integerMassCheck 114 16 1 (dualNumerators114 16 1) := by
  have hn : dualNumerators114 16 1 = ![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 1145040776568, 163860648772, 45087194994, 743309684668, 1105400337064, 0, 1097332801829, 87467940020, 861863417206, 243536919859] := rfl
  have he : residualNumerators 114 16 1 = 744141164530545 := rfl
  have hr : radiusNumerators 16 = 10683060 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_17_0 :
    integerResidualCheck 114 17 0 (dualNumerators114 17 0) ∧
    integerMassCheck 114 17 0 (dualNumerators114 17 0) := by
  have hn : dualNumerators114 17 0 = ![602334801078, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546386, 0, 844525275676, 602334801077, 905187143137, 0, 1184097183123, 0, 1071829546386, 0, 0, 1000000000001, 2028622458797, 1713222941254, 933538524390, 1402919220984, 933538524390, 1105400337065, 905187143137, 0, 1184097183123, 0, 0, 0, 1402919220984, 1549866490728, 1355839558094, 194026932635, 53387620587, 880150903803, 1308901425340, 0, 1299348679594, 103570541391, 1020530044550, 288371380791] := rfl
  have he : residualNumerators 114 17 0 = 956250086544093 := rfl
  have hr : radiusNumerators 17 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_17_1 :
    integerResidualCheck 114 17 1 (dualNumerators114 17 1) ∧
    integerMassCheck 114 17 1 (dualNumerators114 17 1) := by
  have hn : dualNumerators114 17 1 = ![201148953074, 37030955649, 201148953074, 0, 1, 302286113723, 357936135756, 0, 282028158995, 201148953074, 0, 0, 0, 395427772555, 55650022034, 302286113723, 636234862349, 0, 677455931550, 572128657349, 311754022014, 468503118271, 311754022014, 369147059294, 0, 0, 0, 395427772555, 0, 302286113723, 468503118271, 517575975116, 452780923763, 64795051354, 17828729087, 293925292927, 437105993067, 0, 433915865579, 34587252692, 340804731313, 96301261755] := rfl
  have he : residualNumerators 114 17 1 = 327465173210863 := rfl
  have hr : radiusNumerators 17 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_18_0 :
    integerResidualCheck 114 18 0 (dualNumerators114 18 0) ∧
    integerMassCheck 114 18 0 (dualNumerators114 18 0) := by
  have hn : dualNumerators114 18 0 = ![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 1065874698487, 202522000941, 0, 763999473637, 1027460955744, 43732116505, 953519106044, 33030453619, 835192545885, 236000526363] := rfl
  have he : residualNumerators 114 18 0 = 622286213849813 := rfl
  have hr : radiusNumerators 18 = 13565580 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_18_1 :
    integerResidualCheck 114 18 1 (dualNumerators114 18 1) ∧
    integerMassCheck 114 18 1 (dualNumerators114 18 1) := by
  have hn : dualNumerators114 18 1 = ![552774353318, 101764201348, 552774353318, 0, 1, 194169418432, 229915461414, 0, 83885421775, 59829007246, 194169418432, 0, 94926637302, 515633295911, 229915461414, 0, 0, 515633295912, 201500008915, 170171850577, 856726447141, 300936675152, 92726973504, 109797748126, 194169418432, 1, 94926637302, 515633295911, 0, 0, 300936675152, 799162766836, 134673498195, 19272402554, 92726973504, 0, 130011204269, 0, 195186313540, 105750361613, 101367709986, 28643494283] := rfl
  have he : residualNumerators 114 18 1 = 270529282436860 := rfl
  have hr : radiusNumerators 18 = 13565580 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_19_0 :
    integerResidualCheck 114 19 0 (dualNumerators114 19 0) ∧
    integerMassCheck 114 19 0 (dualNumerators114 19 0) := by
  have hn : dualNumerators114 19 0 = ![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 813889575590, 257303496658, 0, 645216866088, 781448198910, 123201425731, 653752451905, 19962510160, 705341215054, 199308409586] := rfl
  have he : residualNumerators 114 19 0 = 632221493436520 := rfl
  have hr : radiusNumerators 19 = 8248658 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_19_1 :
    integerResidualCheck 114 19 1 (dualNumerators114 19 1) ∧
    integerMassCheck 114 19 1 (dualNumerators114 19 1) := by
  have hn : dualNumerators114 19 1 = ![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 1, 987477735649, 0, 668354800182, 95644673455, 186417556881, 273765914097, 645216866088, 0, 761601233763, 225876501886, 503065535987, 142151330101] := rfl
  have he : residualNumerators 114 19 1 = 511373051897715 := rfl
  have hr : radiusNumerators 19 = 8248658 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_20_0 :
    integerResidualCheck 114 20 0 (dualNumerators114 20 0) ∧
    integerMassCheck 114 20 0 (dualNumerators114 20 0) := by
  have hn : dualNumerators114 20 0 = ![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476430, 1136168804325, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605064, 2, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 1540462609577, 220447348059, 1060657349048, 0, 1487132967409, 0, 2232638358246, 1209625354629, 1159494400494, 327638566915] := rfl
  have he : residualNumerators 114 20 0 = 1477282214030125 := rfl
  have hr : radiusNumerators 20 = 35312013 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_20_1 :
    integerResidualCheck 114 20 1 (dualNumerators114 20 1) ∧
    integerMassCheck 114 20 1 (dualNumerators114 20 1) := by
  have hn : dualNumerators114 20 1 = ![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678] := rfl
  have he : residualNumerators 114 20 1 = 854809793236492 := rfl
  have hr : radiusNumerators 20 = 35312013 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_21_0 :
    integerResidualCheck 114 21 0 (dualNumerators114 21 0) ∧
    integerMassCheck 114 21 0 (dualNumerators114 21 0) := by
  have hn : dualNumerators114 21 0 = ![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 1, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 759767979803, 549133445537, 851509250277, 798941670661, 1020530044549, 288371380791] := rfl
  have he : residualNumerators 114 21 0 = 754007348580946 := rfl
  have hr : radiusNumerators 21 = 11182451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_21_1 :
    integerResidualCheck 114 21 1 (dualNumerators114 21 1) ∧
    integerMassCheck 114 21 1 (dualNumerators114 21 1) := by
  have hn : dualNumerators114 21 1 = ![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 917967404853, 905358228364, 3460174706, 161253783489, 102979506989, 127963650709, 0, 0, 180062781238, 50880376460] := rfl
  have he : residualNumerators 114 21 1 = 374930863842880 := rfl
  have hr : radiusNumerators 21 = 11182451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_22_0 :
    integerResidualCheck 114 22 0 (dualNumerators114 22 0) ∧
    integerMassCheck 114 22 0 (dualNumerators114 22 0) := by
  have hn : dualNumerators114 22 0 = ![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 234488508312, 529510965326, 460183470977, 0, 270741877993, 374474988096, 310954038967, 490382041752, 503065535987, 142151330101] := rfl
  have he : residualNumerators 114 22 0 = 470648931664499 := rfl
  have hr : radiusNumerators 22 = 6465674 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_22_1 :
    integerResidualCheck 114 22 1 (dualNumerators114 22 1) ∧
    integerMassCheck 114 22 1 (dualNumerators114 22 1) := by
  have hn : dualNumerators114 22 1 = ![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 108732662288, 12539033463, 1534493418, 71511669319, 45668611868, 56748400418, 0, 0, 79852948501, 22564063785] := rfl
  have he : residualNumerators 114 22 1 = 90706651221511 := rfl
  have hr : radiusNumerators 22 = 6465674 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_23_0 :
    integerResidualCheck 114 23 0 (dualNumerators114 23 0) ∧
    integerMassCheck 114 23 0 (dualNumerators114 23 0) := by
  have hn : dualNumerators114 23 0 = ![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476430, 1136168804325, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605064, 2, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 540462609577, 1220447348059, 1060657349048, 0, 1487132967409, 0, 2232638358246, 1209625354629, 1159494400494, 327638566915] := rfl
  have he : residualNumerators 114 23 0 = 1477282214030125 := rfl
  have hr : radiusNumerators 23 = 35297932 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_23_1 :
    integerResidualCheck 114 23 1 (dualNumerators114 23 1) ∧
    integerMassCheck 114 23 1 (dualNumerators114 23 1) := by
  have hn : dualNumerators114 23 1 = ![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1830784228945, 211125748477, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678] := rfl
  have he : residualNumerators 114 23 1 = 854809793236492 := rfl
  have hr : radiusNumerators 23 = 35297932 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_24_0 :
    integerResidualCheck 114 24 0 (dualNumerators114 24 0) ∧
    integerMassCheck 114 24 0 (dualNumerators114 24 0) := by
  have hn : dualNumerators114 24 0 = ![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 512185690040, 559007382209, 569308312247, 737522866658, 835192545885, 236000526363] := rfl
  have he : residualNumerators 114 24 0 = 667873161486870 := rfl
  have hr : radiusNumerators 24 = 9356857 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_24_1 :
    integerResidualCheck 114 24 1 (dualNumerators114 24 1) ∧
    integerMassCheck 114 24 1 (dualNumerators114 24 1) := by
  have hn : dualNumerators114 24 1 = ![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623507, 113117556459, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 690777049383, 178822020994, 66021086067, 82038644814, 0, 0, 115439864933, 32619865948] := rfl
  have he : residualNumerators 114 24 1 = 232374054719059 := rfl
  have hr : radiusNumerators 24 = 9356857 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_25_0 :
    integerResidualCheck 114 25 0 (dualNumerators114 25 0) ∧
    integerMassCheck 114 25 0 (dualNumerators114 25 0) := by
  have hn : dualNumerators114 25 0 = ![34423495944, 6337268637, 34423495944, 0, 1, 22181646803, 26265225496, 0, 631959902239, 450728300227, 515126992874, 0, 137760279295, 748301940085, 609960421212, 0, 0, 748301940086, 1518022121617, 1282008050738, 53351822857, 34378591088, 698568688945, 827173216796, 515126992874, 1, 137760279295, 748301940085, 0, 0, 798378064725, 1159768101884, 492180793363, 667587308522, 53351822857, 0, 457056897559, 522396578403, 34378591088, 0, 763664612251, 215788863711] := rfl
  have he : residualNumerators 114 25 0 = 507362788409718 := rfl
  have hr : radiusNumerators 25 = 8671199 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_25_1 :
    integerResidualCheck 114 25 1 (dualNumerators114 25 1) ∧
    integerMassCheck 114 25 1 (dualNumerators114 25 1) := by
  have hn : dualNumerators114 25 1 = ![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 1, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 415529968297, 599898615461, 0, 0] := rfl
  have he : residualNumerators 114 25 1 = 222935526651450 := rfl
  have hr : radiusNumerators 25 = 8671199 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_26_0 :
    integerResidualCheck 114 26 0 (dualNumerators114 26 0) ∧
    integerMassCheck 114 26 0 (dualNumerators114 26 0) := by
  have hn : dualNumerators114 26 0 = ![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 1, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0] := rfl
  have he : residualNumerators 114 26 0 = 398909472332109 := rfl
  have hr : radiusNumerators 26 = 15099566 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_26_1 :
    integerResidualCheck 114 26 1 (dualNumerators114 26 1) ∧
    integerMassCheck 114 26 1 (dualNumerators114 26 1) := by
  have hn : dualNumerators114 26 1 = ![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 1025837005087, 204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678] := rfl
  have he : residualNumerators 114 26 1 = 854809793236492 := rfl
  have hr : radiusNumerators 26 = 15099566 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_27_0 :
    integerResidualCheck 114 27 0 (dualNumerators114 27 0) ∧
    integerMassCheck 114 27 0 (dualNumerators114 27 0) := by
  have hn : dualNumerators114 27 0 = ![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 1, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 286173900105, 455299762271, 595678484088, 168320989550] := rfl
  have he : residualNumerators 114 27 0 = 411871570759515 := rfl
  have hr : radiusNumerators 27 = 7338775 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_27_1 :
    integerResidualCheck 114 27 1 (dualNumerators114 27 1) ∧
    integerMassCheck 114 27 1 (dualNumerators114 27 1) := by
  have hn : dualNumerators114 27 1 = ![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583262, 988432197465, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 963066529984, 568871411225, 0, 377837583379, 916671368281, 377088943834, 621055226706, 24161639382, 413046270426, 116714568052] := rfl
  have he : residualNumerators 114 27 1 = 547859315217757 := rfl
  have hr : radiusNumerators 27 = 7338775 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_28_0 :
    integerResidualCheck 114 28 0 (dualNumerators114 28 0) ∧
    integerMassCheck 114 28 0 (dualNumerators114 28 0) := by
  have hn : dualNumerators114 28 0 = ![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 1, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 450383711774, 395438493575, 503065535987, 142151330101] := rfl
  have he : residualNumerators 114 28 0 = 286784861133797 := rfl
  have hr : radiusNumerators 28 = 10335557 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_28_1 :
    integerResidualCheck 114 28 1 (dualNumerators114 28 1) ∧
    integerMassCheck 114 28 1 (dualNumerators114 28 1) := by
  have hn : dualNumerators114 28 1 = ![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 484442151291, 449974794159, 2156352207, 100492021777, 456143077212, 332995651238, 0, 0, 112213633330, 31708229033] := rfl
  have he : residualNumerators 114 28 1 = 301267805415724 := rfl
  have hr : radiusNumerators 28 = 10335557 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_29_0 :
    integerResidualCheck 114 29 0 (dualNumerators114 29 0) ∧
    integerMassCheck 114 29 0 (dualNumerators114 29 0) := by
  have hn : dualNumerators114 29 0 = ![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 1, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0] := rfl
  have he : residualNumerators 114 29 0 = 398909472332109 := rfl
  have hr : radiusNumerators 29 = 40352153 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_29_1 :
    integerResidualCheck 114 29 1 (dualNumerators114 29 1) ∧
    integerMassCheck 114 29 1 (dualNumerators114 29 1) := by
  have hn : dualNumerators114 29 1 = ![814189538844, 149890000629, 814189538844, 0, 1, 31000670773, 36707806937, 0, 1141563866996, 814189538843, 31000670773, 0, 248848315523, 1351722559260, 36707806937, 0, 0, 1351722559261, 2742134741776, 2315802098733, 1261885083355, 48046900821, 1261885083355, 1494194572624, 31000670773, 0, 248848315523, 1351722559260, 0, 0, 48046900821, 2094989499358, 1832718917411, 262270581947, 72165251132, 1189719832223, 1769271584479, 0, 0, 48046900821, 1379473483620, 389798100860] := rfl
  have he : residualNumerators 114 29 1 = 891662691436227 := rfl
  have hr : radiusNumerators 29 = 40352153 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_30_0 :
    integerResidualCheck 114 30 0 (dualNumerators114 30 0) ∧
    integerMassCheck 114 30 0 (dualNumerators114 30 0) := by
  have hn : dualNumerators114 30 0 = ![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 115599349926, 0, 37915592377, 205954223378, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 1, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 279240883212, 39960666226, 10995405936, 181270795848, 269573776534, 0, 163293901896, 15869656905, 269573776534, 0] := rfl
  have he : residualNumerators 114 30 0 = 219330030122630 := rfl
  have hr : radiusNumerators 30 = 7680628 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_30_1 :
    integerResidualCheck 114 30 1 (dualNumerators114 30 1) ∧
    integerMassCheck 114 30 1 (dualNumerators114 30 1) := by
  have hn : dualNumerators114 30 1 = ![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195716, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 1, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 791397036221, 113252588419, 31162097647, 513739854055, 763999473637, 0, 862736028146, 65914760940, 536287180313, 227712293325] := rfl
  have he : residualNumerators 114 30 1 = 552647017525296 := rfl
  have hr : radiusNumerators 30 = 7680628 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_31_0 :
    integerResidualCheck 114 31 0 (dualNumerators114 31 0) ∧
    integerMassCheck 114 31 0 (dualNumerators114 31 0) := by
  have hn : dualNumerators114 31 0 = ![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1719079079316, 0, 1491143233587, 0, 2035556695381, 0, 1259308150413, 1, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079316, 0, 1491143233587, 0, 0, 0, 2664343059941, 1951759503826, 1707419806160, 244339697667, 939253060812, 1341759948741, 1648310233018, 0, 1640459045760, 1023884014182, 1648310233018, 0] := rfl
  have he : residualNumerators 114 31 0 = 1679604272728010 := rfl
  have hr : radiusNumerators 31 = 32891612 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_31_1 :
    integerResidualCheck 114 31 1 (dualNumerators114 31 1) ∧
    integerMassCheck 114 31 1 (dualNumerators114 31 1) := by
  have hn : dualNumerators114 31 1 = ![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 741061026801, 808805463926, 725570984152, 37986262977, 845258320866, 704608169862] := rfl
  have he : residualNumerators 114 31 1 = 650873120454598 := rfl
  have hr : radiusNumerators 31 = 32891612 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_32_0 :
    integerResidualCheck 114 32 0 (dualNumerators114 32 0) ∧
    integerMassCheck 114 32 0 (dualNumerators114 32 0) := by
  have hn : dualNumerators114 32 0 = ![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 0, 2079538667399, 1160276651773, 0, 382837210862, 2079538667397, 979882959195, 1, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 1160276651773, 0, 0, 0, 3223007296772, 1518687763292, 1328564078378, 190123684914, 52313619645, 862444872157, 1282570201956, 0, 3029568551736, 193438745037, 0, 1282570201956] := rfl
  have he : residualNumerators 114 32 0 = 1330357274743913 := rfl
  have hr : radiusNumerators 32 = 67647473 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck114_32_1 :
    integerResidualCheck 114 32 1 (dualNumerators114 32 1) ∧
    integerMassCheck 114 32 1 (dualNumerators114 32 1) := by
  have hn : dualNumerators114 32 1 = ![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1946401957496, 0, 638403098873, 3467750500271, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957494, 2, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 4701713305868, 672836992711, 185134947997, 3052143736978, 4538943572529, 0, 2749458111138, 267205060270, 4538943572529, 0] := rfl
  have he : residualNumerators 114 32 1 = 2885908019775983 := rfl
  have hr : radiusNumerators 32 = 67647473 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots114]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature114_entry]
    rw [hn, he, hr]
    decide

theorem integerChecks114 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 114 j s (dualNumerators114 j s) ∧
    integerMassCheck 114 j s (dualNumerators114 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck114_0_0
    · exact integerCheck114_0_1
  · fin_cases s
    · exact integerCheck114_1_0
    · exact integerCheck114_1_1
  · fin_cases s
    · exact integerCheck114_2_0
    · exact integerCheck114_2_1
  · fin_cases s
    · exact integerCheck114_3_0
    · exact integerCheck114_3_1
  · fin_cases s
    · exact integerCheck114_4_0
    · exact integerCheck114_4_1
  · fin_cases s
    · exact integerCheck114_5_0
    · exact integerCheck114_5_1
  · fin_cases s
    · exact integerCheck114_6_0
    · exact integerCheck114_6_1
  · fin_cases s
    · exact integerCheck114_7_0
    · exact integerCheck114_7_1
  · fin_cases s
    · exact integerCheck114_8_0
    · exact integerCheck114_8_1
  · fin_cases s
    · exact integerCheck114_9_0
    · exact integerCheck114_9_1
  · fin_cases s
    · exact integerCheck114_10_0
    · exact integerCheck114_10_1
  · fin_cases s
    · exact integerCheck114_11_0
    · exact integerCheck114_11_1
  · fin_cases s
    · exact integerCheck114_12_0
    · exact integerCheck114_12_1
  · fin_cases s
    · exact integerCheck114_13_0
    · exact integerCheck114_13_1
  · fin_cases s
    · exact integerCheck114_14_0
    · exact integerCheck114_14_1
  · fin_cases s
    · exact integerCheck114_15_0
    · exact integerCheck114_15_1
  · fin_cases s
    · exact integerCheck114_16_0
    · exact integerCheck114_16_1
  · fin_cases s
    · exact integerCheck114_17_0
    · exact integerCheck114_17_1
  · fin_cases s
    · exact integerCheck114_18_0
    · exact integerCheck114_18_1
  · fin_cases s
    · exact integerCheck114_19_0
    · exact integerCheck114_19_1
  · fin_cases s
    · exact integerCheck114_20_0
    · exact integerCheck114_20_1
  · fin_cases s
    · exact integerCheck114_21_0
    · exact integerCheck114_21_1
  · fin_cases s
    · exact integerCheck114_22_0
    · exact integerCheck114_22_1
  · fin_cases s
    · exact integerCheck114_23_0
    · exact integerCheck114_23_1
  · fin_cases s
    · exact integerCheck114_24_0
    · exact integerCheck114_24_1
  · fin_cases s
    · exact integerCheck114_25_0
    · exact integerCheck114_25_1
  · fin_cases s
    · exact integerCheck114_26_0
    · exact integerCheck114_26_1
  · fin_cases s
    · exact integerCheck114_27_0
    · exact integerCheck114_27_1
  · fin_cases s
    · exact integerCheck114_28_0
    · exact integerCheck114_28_1
  · fin_cases s
    · exact integerCheck114_29_0
    · exact integerCheck114_29_1
  · fin_cases s
    · exact integerCheck114_30_0
    · exact integerCheck114_30_1
  · fin_cases s
    · exact integerCheck114_31_0
    · exact integerCheck114_31_1
  · fin_cases s
    · exact integerCheck114_32_0
    · exact integerCheck114_32_1

end ElevenSquare.Tasks.T06
