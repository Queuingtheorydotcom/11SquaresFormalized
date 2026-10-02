import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.DataDual018
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
import ElevenSquare.Tasks.T06.SparseColumn20
import ElevenSquare.Tasks.T06.SparseColumn21
import ElevenSquare.Tasks.T06.SparseColumn22
import ElevenSquare.Tasks.T06.SparseColumn24
import ElevenSquare.Tasks.T06.SparseColumn25
import ElevenSquare.Tasks.T06.SparseColumn26
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
import ElevenSquare.Tasks.T06.SparseColumn47
import ElevenSquare.Tasks.T06.SparseColumn48

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix018 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral43, roundedGradientLiteral44, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix018_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = branchIntegerMatrix018 := by
  change roundedGradients ∘ branchRows 18 = branchIntegerMatrix018
  rw [show branchRows 18 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 34, 35, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral43_eq, roundedGradientLiteral44_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, branchIntegerMatrix018]

theorem branchColumn018_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 0) i) = _
  rw [branchColumn018_0]
  exact sparseColumn00_sum n

theorem branchColumn018_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 1) i) = _
  rw [branchColumn018_1]
  exact sparseColumn01_sum n

theorem branchColumn018_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 2) i) = _
  rw [branchColumn018_2]
  exact sparseColumn02_sum n

theorem branchColumn018_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 3) i) = _
  rw [branchColumn018_3]
  exact sparseColumn03_sum n

theorem branchColumn018_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 4) i) = _
  rw [branchColumn018_4]
  exact sparseColumn04_sum n

theorem branchColumn018_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 5) i) = _
  rw [branchColumn018_5]
  exact sparseColumn05_sum n

theorem branchColumn018_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 6) i) = _
  rw [branchColumn018_6]
  exact sparseColumn06_sum n

theorem branchColumn018_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 7) i) = _
  rw [branchColumn018_7]
  exact sparseColumn07_sum n

theorem branchColumn018_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 8) i) = _
  rw [branchColumn018_8]
  exact sparseColumn08_sum n

theorem branchColumn018_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 9) i) = _
  rw [branchColumn018_9]
  exact sparseColumn09_sum n

theorem branchColumn018_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 10) i) = _
  rw [branchColumn018_10]
  exact sparseColumn10_sum n

theorem branchColumn018_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 11) i) = _
  rw [branchColumn018_11]
  exact sparseColumn11_sum n

theorem branchColumn018_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 12) i) = _
  rw [branchColumn018_12]
  exact sparseColumn35_sum n

theorem branchColumn018_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 13) i) = _
  rw [branchColumn018_13]
  exact sparseColumn36_sum n

theorem branchColumn018_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 14) = sparseColumn37 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 14) = sparseDot37 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 14) i) = _
  rw [branchColumn018_14]
  exact sparseColumn37_sum n

theorem branchColumn018_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 15) i) = _
  rw [branchColumn018_15]
  exact sparseColumn38_sum n

theorem branchColumn018_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 16) i) = _
  rw [branchColumn018_16]
  exact sparseColumn39_sum n

theorem branchColumn018_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 17) = sparseColumn40 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 17) = sparseDot40 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 17) i) = _
  rw [branchColumn018_17]
  exact sparseColumn40_sum n

theorem branchColumn018_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 18) i) = _
  rw [branchColumn018_18]
  exact sparseColumn18_sum n

theorem branchColumn018_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 19) i) = _
  rw [branchColumn018_19]
  exact sparseColumn19_sum n

theorem branchColumn018_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 20) = sparseColumn20 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 20) = sparseDot20 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 20) i) = _
  rw [branchColumn018_20]
  exact sparseColumn20_sum n

theorem branchColumn018_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 21) i) = _
  rw [branchColumn018_21]
  exact sparseColumn21_sum n

theorem branchColumn018_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 22) i) = _
  rw [branchColumn018_22]
  exact sparseColumn22_sum n

theorem branchColumn018_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 23) = sparseColumn47 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 23) = sparseDot47 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 23) i) = _
  rw [branchColumn018_23]
  exact sparseColumn47_sum n

theorem branchColumn018_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 24) i) = _
  rw [branchColumn018_24]
  exact sparseColumn24_sum n

theorem branchColumn018_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 25) i) = _
  rw [branchColumn018_25]
  exact sparseColumn25_sum n

theorem branchColumn018_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 26) = sparseColumn26 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 26) = sparseDot26 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 26) i) = _
  rw [branchColumn018_26]
  exact sparseColumn26_sum n

theorem branchColumn018_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 27) i) = _
  rw [branchColumn018_27]
  exact sparseColumn27_sum n

theorem branchColumn018_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 28) i) = _
  rw [branchColumn018_28]
  exact sparseColumn28_sum n

theorem branchColumn018_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 29) = sparseColumn48 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 29) = sparseDot48 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 29) i) = _
  rw [branchColumn018_29]
  exact sparseColumn48_sum n

theorem branchColumn018_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 30) i) = _
  rw [branchColumn018_30]
  exact sparseColumn30_sum n

theorem branchColumn018_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 31) i) = _
  rw [branchColumn018_31]
  exact sparseColumn31_sum n

theorem branchColumn018_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 18 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 18 i)) = _
  rw [branchIntegerMatrix018_eq]
  simp only [branchIntegerMatrix018, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot018_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 18 i) 32) i) = _
  rw [branchColumn018_32]
  exact sparseColumn32_sum n

def branchSparseDots018 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot37, sparseDot38, sparseDot39, sparseDot40, sparseDot18, sparseDot19, sparseDot20, sparseDot21, sparseDot22, sparseDot47, sparseDot24, sparseDot25, sparseDot26, sparseDot27, sparseDot28, sparseDot48, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot018_0 :
    branchSparseDots018 0 = sparseDot00 := rfl

private theorem branchSparseDot018_1 :
    branchSparseDots018 1 = sparseDot01 := rfl

private theorem branchSparseDot018_2 :
    branchSparseDots018 2 = sparseDot02 := rfl

private theorem branchSparseDot018_3 :
    branchSparseDots018 3 = sparseDot03 := rfl

private theorem branchSparseDot018_4 :
    branchSparseDots018 4 = sparseDot04 := rfl

private theorem branchSparseDot018_5 :
    branchSparseDots018 5 = sparseDot05 := rfl

private theorem branchSparseDot018_6 :
    branchSparseDots018 6 = sparseDot06 := rfl

private theorem branchSparseDot018_7 :
    branchSparseDots018 7 = sparseDot07 := rfl

private theorem branchSparseDot018_8 :
    branchSparseDots018 8 = sparseDot08 := rfl

private theorem branchSparseDot018_9 :
    branchSparseDots018 9 = sparseDot09 := rfl

private theorem branchSparseDot018_10 :
    branchSparseDots018 10 = sparseDot10 := rfl

private theorem branchSparseDot018_11 :
    branchSparseDots018 11 = sparseDot11 := rfl

private theorem branchSparseDot018_12 :
    branchSparseDots018 12 = sparseDot35 := rfl

private theorem branchSparseDot018_13 :
    branchSparseDots018 13 = sparseDot36 := rfl

private theorem branchSparseDot018_14 :
    branchSparseDots018 14 = sparseDot37 := rfl

private theorem branchSparseDot018_15 :
    branchSparseDots018 15 = sparseDot38 := rfl

private theorem branchSparseDot018_16 :
    branchSparseDots018 16 = sparseDot39 := rfl

private theorem branchSparseDot018_17 :
    branchSparseDots018 17 = sparseDot40 := rfl

private theorem branchSparseDot018_18 :
    branchSparseDots018 18 = sparseDot18 := rfl

private theorem branchSparseDot018_19 :
    branchSparseDots018 19 = sparseDot19 := rfl

private theorem branchSparseDot018_20 :
    branchSparseDots018 20 = sparseDot20 := rfl

private theorem branchSparseDot018_21 :
    branchSparseDots018 21 = sparseDot21 := rfl

private theorem branchSparseDot018_22 :
    branchSparseDots018 22 = sparseDot22 := rfl

private theorem branchSparseDot018_23 :
    branchSparseDots018 23 = sparseDot47 := rfl

private theorem branchSparseDot018_24 :
    branchSparseDots018 24 = sparseDot24 := rfl

private theorem branchSparseDot018_25 :
    branchSparseDots018 25 = sparseDot25 := rfl

private theorem branchSparseDot018_26 :
    branchSparseDots018 26 = sparseDot26 := rfl

private theorem branchSparseDot018_27 :
    branchSparseDots018 27 = sparseDot27 := rfl

private theorem branchSparseDot018_28 :
    branchSparseDots018 28 = sparseDot28 := rfl

private theorem branchSparseDot018_29 :
    branchSparseDots018 29 = sparseDot48 := rfl

private theorem branchSparseDot018_30 :
    branchSparseDots018 30 = sparseDot30 := rfl

private theorem branchSparseDot018_31 :
    branchSparseDots018 31 = sparseDot31 := rfl

private theorem branchSparseDot018_32 :
    branchSparseDots018 32 = sparseDot32 := rfl

theorem branchDots018 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 18 i) k) = branchSparseDots018 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot018_0 n
      _ = _ := congrFun branchSparseDot018_0.symm n
  · calc
      _ = sparseDot01 n := branchDot018_1 n
      _ = _ := congrFun branchSparseDot018_1.symm n
  · calc
      _ = sparseDot02 n := branchDot018_2 n
      _ = _ := congrFun branchSparseDot018_2.symm n
  · calc
      _ = sparseDot03 n := branchDot018_3 n
      _ = _ := congrFun branchSparseDot018_3.symm n
  · calc
      _ = sparseDot04 n := branchDot018_4 n
      _ = _ := congrFun branchSparseDot018_4.symm n
  · calc
      _ = sparseDot05 n := branchDot018_5 n
      _ = _ := congrFun branchSparseDot018_5.symm n
  · calc
      _ = sparseDot06 n := branchDot018_6 n
      _ = _ := congrFun branchSparseDot018_6.symm n
  · calc
      _ = sparseDot07 n := branchDot018_7 n
      _ = _ := congrFun branchSparseDot018_7.symm n
  · calc
      _ = sparseDot08 n := branchDot018_8 n
      _ = _ := congrFun branchSparseDot018_8.symm n
  · calc
      _ = sparseDot09 n := branchDot018_9 n
      _ = _ := congrFun branchSparseDot018_9.symm n
  · calc
      _ = sparseDot10 n := branchDot018_10 n
      _ = _ := congrFun branchSparseDot018_10.symm n
  · calc
      _ = sparseDot11 n := branchDot018_11 n
      _ = _ := congrFun branchSparseDot018_11.symm n
  · calc
      _ = sparseDot35 n := branchDot018_12 n
      _ = _ := congrFun branchSparseDot018_12.symm n
  · calc
      _ = sparseDot36 n := branchDot018_13 n
      _ = _ := congrFun branchSparseDot018_13.symm n
  · calc
      _ = sparseDot37 n := branchDot018_14 n
      _ = _ := congrFun branchSparseDot018_14.symm n
  · calc
      _ = sparseDot38 n := branchDot018_15 n
      _ = _ := congrFun branchSparseDot018_15.symm n
  · calc
      _ = sparseDot39 n := branchDot018_16 n
      _ = _ := congrFun branchSparseDot018_16.symm n
  · calc
      _ = sparseDot40 n := branchDot018_17 n
      _ = _ := congrFun branchSparseDot018_17.symm n
  · calc
      _ = sparseDot18 n := branchDot018_18 n
      _ = _ := congrFun branchSparseDot018_18.symm n
  · calc
      _ = sparseDot19 n := branchDot018_19 n
      _ = _ := congrFun branchSparseDot018_19.symm n
  · calc
      _ = sparseDot20 n := branchDot018_20 n
      _ = _ := congrFun branchSparseDot018_20.symm n
  · calc
      _ = sparseDot21 n := branchDot018_21 n
      _ = _ := congrFun branchSparseDot018_21.symm n
  · calc
      _ = sparseDot22 n := branchDot018_22 n
      _ = _ := congrFun branchSparseDot018_22.symm n
  · calc
      _ = sparseDot47 n := branchDot018_23 n
      _ = _ := congrFun branchSparseDot018_23.symm n
  · calc
      _ = sparseDot24 n := branchDot018_24 n
      _ = _ := congrFun branchSparseDot018_24.symm n
  · calc
      _ = sparseDot25 n := branchDot018_25 n
      _ = _ := congrFun branchSparseDot018_25.symm n
  · calc
      _ = sparseDot26 n := branchDot018_26 n
      _ = _ := congrFun branchSparseDot018_26.symm n
  · calc
      _ = sparseDot27 n := branchDot018_27 n
      _ = _ := congrFun branchSparseDot018_27.symm n
  · calc
      _ = sparseDot28 n := branchDot018_28 n
      _ = _ := congrFun branchSparseDot018_28.symm n
  · calc
      _ = sparseDot48 n := branchDot018_29 n
      _ = _ := congrFun branchSparseDot018_29.symm n
  · calc
      _ = sparseDot30 n := branchDot018_30 n
      _ = _ := congrFun branchSparseDot018_30.symm n
  · calc
      _ = sparseDot31 n := branchDot018_31 n
      _ = _ := congrFun branchSparseDot018_31.symm n
  · calc
      _ = sparseDot32 n := branchDot018_32 n
      _ = _ := congrFun branchSparseDot018_32.symm n

def branchIntegerCurvature018 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101981296, 101981296, 44932602, 44932602, 106371291, 106371291, 48290998, 48290998, 204734428, 204734428]

theorem branchIntegerCurvature018_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 18 i)) = branchIntegerCurvature018 := by
  change curvatureNumerators ∘ branchRows 18 = branchIntegerCurvature018
  rw [show branchRows 18 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 34, 35, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature018_entry (i : Fin 42) :
    curvatureNumerators (branchRows 18 i) = branchIntegerCurvature018 i :=
  congrFun branchIntegerCurvature018_eq i

theorem integerCheck018_0_0 :
    integerResidualCheck 18 0 0 (dualNumerators018 0 0) ∧
    integerMassCheck 18 0 0 (dualNumerators018 0 0) := by
  have hn : dualNumerators018 0 0 = ![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 298609637458, 1874436686609, 0, 1308901425339, 1754571864380, 80620681505, 1741178091979, 225835502005, 1430871029972, 404321515913] := rfl
  have he : residualNumerators 18 0 0 = 1298163304576876 := rfl
  have hr : radiusNumerators 0 = 18767167 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_0_1 :
    integerResidualCheck 18 0 1 (dualNumerators018 0 1) ∧
    integerMassCheck 18 0 1 (dualNumerators018 0 1) := by
  have hn : dualNumerators018 0 1 = ![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 18 0 1 = 33000000000000 := rfl
  have hr : radiusNumerators 0 = 18767167 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_1_0 :
    integerResidualCheck 18 1 0 (dualNumerators018 1 0) ∧
    integerMassCheck 18 1 0 (dualNumerators018 1 0) := by
  have hn : dualNumerators018 1 0 = ![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 353582830567, 2219515200554, 0, 1549866490727, 2077583602197, 95462721871, 2061724074025, 267411181773, 1694290356000, 478755968067] := rfl
  have he : residualNumerators 18 1 0 = 1547157453816691 := rfl
  have hr : radiusNumerators 1 = 22176635 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_1_1 :
    integerResidualCheck 18 1 1 (dualNumerators018 1 1) ∧
    integerMassCheck 18 1 1 (dualNumerators018 1 1) := by
  have hn : dualNumerators018 1 1 = ![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 18 1 1 = 33000000000000 := rfl
  have hr : radiusNumerators 1 = 22176635 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_2_0 :
    integerResidualCheck 18 2 0 (dualNumerators018 2 0) ∧
    integerMassCheck 18 2 0 (dualNumerators018 2 0) := by
  have hn : dualNumerators018 2 0 = ![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 353582830567, 2219515200555, 0, 1549866490728, 2077583602198, 95462721871, 2061724074027, 267411181773, 1694290356001, 478755968068] := rfl
  have he : residualNumerators 18 2 0 = 1581690348075980 := rfl
  have hr : radiusNumerators 2 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_2_1 :
    integerResidualCheck 18 2 1 (dualNumerators018 2 1) ∧
    integerMassCheck 18 2 1 (dualNumerators018 2 1) := by
  have hn : dualNumerators018 2 1 = ![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 298609637458, 1874436686608, 0, 1308901425338, 1754571864379, 80620681504, 1741178091978, 225835502005, 1430871029971, 404321515912] := rfl
  have he : residualNumerators 18 2 1 = 1336404235365260 := rfl
  have hr : radiusNumerators 2 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_3_0 :
    integerResidualCheck 18 3 0 (dualNumerators018 3 0) ∧
    integerMassCheck 18 3 0 (dualNumerators018 3 0) := by
  have hn : dualNumerators018 3 0 = ![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 18 3 0 = 33000000000000 := rfl
  have hr : radiusNumerators 3 = 16360330 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_3_1 :
    integerResidualCheck 18 3 1 (dualNumerators018 3 1) ∧
    integerMassCheck 18 3 1 (dualNumerators018 3 1) := by
  have hn : dualNumerators018 3 1 = ![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000001, 0, 203380245200, 1104743927907, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 235283107509, 1476922487191, 0, 1031321016287, 1382477552007, 63523349867, 1371924214149, 177942276579, 1127424369963, 318576531911] := rfl
  have he : residualNumerators 18 3 1 = 1023552281487221 := rfl
  have hr : radiusNumerators 3 = 16360330 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_4_0 :
    integerResidualCheck 18 4 0 (dualNumerators018 4 0) ∧
    integerMassCheck 18 4 0 (dualNumerators018 4 0) := by
  have hn : dualNumerators018 4 0 = ![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757645, 932984170265, 1000000000001, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 198702531230, 1247298370644, 0, 870976665588, 1167537235722, 53647074558, 1158624675158, 150276750182, 952138376845, 269045933435] := rfl
  have he : residualNumerators 18 4 0 = 860600012724557 := rfl
  have hr : radiusNumerators 4 = 13760362 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_4_1 :
    integerResidualCheck 18 4 1 (dualNumerators018 4 1) ∧
    integerMassCheck 18 4 1 (dualNumerators018 4 1) := by
  have hn : dualNumerators018 4 1 = ![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 18 4 1 = 33000000000000 := rfl
  have hr : radiusNumerators 4 = 13760362 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_5_0 :
    integerResidualCheck 18 5 0 (dualNumerators018 5 0) ∧
    integerMassCheck 18 5 0 (dualNumerators018 5 0) := by
  have hn : dualNumerators018 5 0 = ![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245201, 1104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 235283107509, 1476922487193, 0, 1031321016288, 1382477552008, 63523349867, 1371924214150, 177942276579, 1127424369964, 318576531911] := rfl
  have he : residualNumerators 18 5 0 = 1056926536445316 := rfl
  have hr : radiusNumerators 5 = 17641130 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_5_1 :
    integerResidualCheck 18 5 1 (dualNumerators018 5 1) ∧
    integerMassCheck 18 5 1 (dualNumerators018 5 1) := by
  have hn : dualNumerators018 5 1 = ![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170264, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 198702531230, 1247298370643, 0, 870976665588, 1167537235721, 53647074558, 1158624675157, 150276750182, 952138376844, 269045933435] := rfl
  have he : residualNumerators 18 5 1 = 894666681988852 := rfl
  have hr : radiusNumerators 5 = 17641130 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_6_0 :
    integerResidualCheck 18 6 0 (dualNumerators018 6 0) ∧
    integerMassCheck 18 6 0 (dualNumerators018 6 0) := by
  have hn : dualNumerators018 6 0 = ![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 877488274356, 957704271528, 103906894360, 5439901403, 1430871029972, 404321515913] := rfl
  have he : residualNumerators 18 6 0 = 720386069516620 := rfl
  have hr : radiusNumerators 6 = 8962451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_6_1 :
    integerResidualCheck 18 6 1 (dualNumerators018 6 1) ∧
    integerMassCheck 18 6 1 (dualNumerators018 6 1) := by
  have hn : dualNumerators018 6 1 = ![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 1, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 760187607595, 1097479190627, 0, 0] := rfl
  have he : residualNumerators 18 6 1 = 625101700319887 := rfl
  have hr : radiusNumerators 6 = 8962451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_7_0 :
    integerResidualCheck 18 7 0 (dualNumerators018 7 0) ∧
    integerMassCheck 18 7 0 (dualNumerators018 7 0) := by
  have hn : dualNumerators018 7 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 18 7 0 = 33000000000000 := rfl
  have hr : radiusNumerators 7 = 10424794 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_7_1 :
    integerResidualCheck 18 7 1 (dualNumerators018 7 1) ∧
    integerMassCheck 18 7 1 (dualNumerators018 7 1) := by
  have hn : dualNumerators018 7 1 = ![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646810, 830103123887, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675220, 1, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 176791415284, 1109757600279, 0, 774933245365, 1038791801100, 47731360936, 1030862037014, 133705590887, 847145178002, 239377984034] := rfl
  have he : residualNumerators 18 7 1 = 759575858391577 := rfl
  have hr : radiusNumerators 7 = 10424794 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_8_0 :
    integerResidualCheck 18 8 0 (dualNumerators018 8 0) ∧
    integerMassCheck 18 8 0 (dualNumerators018 8 0) := by
  have hn : dualNumerators018 8 0 = ![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293619, 1660206247774, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350440, 2, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 353582830567, 2219515200557, 0, 1549866490730, 2077583602200, 95462721871, 2061724074028, 267411181773, 1694290356003, 478755968068] := rfl
  have he : residualNumerators 18 8 0 = 1575181711323438 := rfl
  have hr : radiusNumerators 8 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_8_1 :
    integerResidualCheck 18 8 1 (dualNumerators018 8 1) ∧
    integerMassCheck 18 8 1 (dualNumerators018 8 1) := by
  have hn : dualNumerators018 8 1 = ![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590429, 217988955956, 0, 1402086139075, 1269150346660, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546384, 0, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 252183386393, 1583009159490, 0, 1105400337063, 1481780287453, 68086203273, 1470468908124, 190723789588, 1208406751039, 341459739686] := rfl
  have he : residualNumerators 18 8 1 = 1129897640265416 := rfl
  have hr : radiusNumerators 8 = 22681452 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_9_0 :
    integerResidualCheck 18 9 0 (dualNumerators018 9 0) ∧
    integerMassCheck 18 9 0 (dualNumerators018 9 0) := by
  have hn : dualNumerators018 9 0 = ![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 235283107509, 1476922487191, 0, 1031321016287, 1382477552007, 63523349867, 1371924214149, 177942276579, 1127424369963, 318576531911] := rfl
  have he : residualNumerators 18 9 0 = 1024453968921723 := rfl
  have hr : radiusNumerators 9 = 16350530 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_9_1 :
    integerResidualCheck 18 9 1 (dualNumerators018 9 1) ∧
    integerMassCheck 18 9 1 (dualNumerators018 9 1) := by
  have hn : dualNumerators018 9 1 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 18 9 1 = 33000000000000 := rfl
  have hr : radiusNumerators 9 = 16350530 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_10_0 :
    integerResidualCheck 18 10 0 (dualNumerators018 10 0) ∧
    integerMassCheck 18 10 0 (dualNumerators018 10 0) := by
  have hn : dualNumerators018 10 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 18 10 0 = 33000000000000 := rfl
  have hr : radiusNumerators 10 = 10683139 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_10_1 :
    integerResidualCheck 18 10 1 (dualNumerators018 10 1) ∧
    integerMassCheck 18 10 1 (dualNumerators018 10 1) := by
  have hn : dualNumerators018 10 1 = ![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 179862976578, 1129038448761, 0, 788396879662, 1056839694908, 48560642157, 1048772159673, 136028582177, 861863417206, 243536919859] := rfl
  have he : residualNumerators 18 10 1 = 777451552176490 := rfl
  have hr : radiusNumerators 10 = 10683139 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_11_0 :
    integerResidualCheck 18 11 0 (dualNumerators018 11 0) ∧
    integerMassCheck 18 11 0 (dualNumerators018 11 0) := by
  have hn : dualNumerators018 11 0 = ![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 111787046581, 701711247439, 0, 489998333105, 656838836154, 30181034864, 651824764029, 84543432681, 535658687508, 151361183509] := rfl
  have he : residualNumerators 18 11 0 = 510623837324912 := rfl
  have hr : radiusNumerators 11 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_11_1 :
    integerResidualCheck 18 11 1 (dualNumerators018 11 1) ∧
    integerMassCheck 18 11 1 (dualNumerators018 11 1) := by
  have hn : dualNumerators018 11 1 = ![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 101936936604, 639879996233, 0, 446822154676, 598961515206, 27521634498, 594389257794, 77093892371, 488459149252, 138024000452] := rfl
  have he : residualNumerators 18 11 1 = 467045895818018 := rfl
  have hr : radiusNumerators 11 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_12_0 :
    integerResidualCheck 18 12 0 (dualNumerators018 12 0) ∧
    integerMassCheck 18 12 0 (dualNumerators018 12 0) := by
  have hn : dualNumerators018 12 0 = ![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 235283107509, 1476922487191, 0, 1031321016287, 1382477552007, 63523349867, 1371924214149, 177942276579, 1127424369963, 318576531911] := rfl
  have he : residualNumerators 18 12 0 = 989052281487221 := rfl
  have hr : radiusNumerators 12 = 16348076 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_12_1 :
    integerResidualCheck 18 12 1 (dualNumerators018 12 1) ∧
    integerMassCheck 18 12 1 (dualNumerators018 12 1) := by
  have hn : dualNumerators018 12 1 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 18 12 1 = 66000000000000 := rfl
  have hr : radiusNumerators 12 = 16348076 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_13_0 :
    integerResidualCheck 18 13 0 (dualNumerators018 13 0) ∧
    integerMassCheck 18 13 0 (dualNumerators018 13 0) := by
  have hn : dualNumerators018 13 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 18 13 0 = 33000000000000 := rfl
  have hr : radiusNumerators 13 = 13962901 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_13_1 :
    integerResidualCheck 18 13 1 (dualNumerators018 13 1) ∧
    integerMassCheck 18 13 1 (dualNumerators018 13 1) := by
  have hn : dualNumerators018 13 1 = ![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 198702531230, 1247298370644, 0, 870976665588, 1167537235722, 53647074558, 1158624675158, 150276750182, 952138376845, 269045933435] := rfl
  have he : residualNumerators 18 13 1 = 860590381159182 := rfl
  have hr : radiusNumerators 13 = 13962901 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_14_0 :
    integerResidualCheck 18 14 0 (dualNumerators018 14 0) ∧
    integerMassCheck 18 14 0 (dualNumerators018 14 0) := by
  have hn : dualNumerators018 14 0 = ![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 235283107509, 1476922487193, 0, 1031321016288, 1382477552008, 63523349867, 1371924214150, 177942276579, 1127424369964, 318576531911] := rfl
  have he : residualNumerators 18 14 0 = 1054886798648883 := rfl
  have hr : radiusNumerators 14 = 20161291 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_14_1 :
    integerResidualCheck 18 14 1 (dualNumerators018 14 1) ∧
    integerMassCheck 18 14 1 (dualNumerators018 14 1) := by
  have hn : dualNumerators018 14 1 = ![561968834605, 103456879454, 561968834605, 0, 1, 844525275673, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 0, 1000000000000, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 198702531230, 1247298370643, 0, 870976665588, 1167537235721, 53647074558, 1158624675157, 150276750182, 952138376844, 269045933435] := rfl
  have he : residualNumerators 18 14 1 = 893166681988885 := rfl
  have hr : radiusNumerators 14 = 20161291 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_15_0 :
    integerResidualCheck 18 15 0 (dualNumerators018 15 0) ∧
    integerMassCheck 18 15 0 (dualNumerators018 15 0) := by
  have hn : dualNumerators018 15 0 = ![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819834, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819834, 475117180167, 0, 736368196709, 813498294019, 111787046581, 701711247439, 0, 489998333105, 656838836153, 30181034864, 651824764029, 84543432681, 535658687508, 151361183509] := rfl
  have he : residualNumerators 18 15 0 = 476900815350166 := rfl
  have hr : radiusNumerators 15 = 12900283 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_15_1 :
    integerResidualCheck 18 15 1 (dualNumerators018 15 1) ∧
    integerMassCheck 18 15 1 (dualNumerators018 15 1) := by
  have hn : dualNumerators018 15 1 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 18 15 1 = 33000000000000 := rfl
  have hr : radiusNumerators 15 = 12900283 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_16_0 :
    integerResidualCheck 18 16 0 (dualNumerators018 16 0) ∧
    integerMassCheck 18 16 0 (dualNumerators018 16 0) := by
  have hn : dualNumerators018 16 0 = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have he : residualNumerators 18 16 0 = 66000000000000 := rfl
  have hr : radiusNumerators 16 = 10683060 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_16_1 :
    integerResidualCheck 18 16 1 (dualNumerators018 16 1) ∧
    integerMassCheck 18 16 1 (dualNumerators018 16 1) := by
  have hn : dualNumerators018 16 1 = ![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 179862976578, 1129038448761, 0, 788396879662, 1056839694908, 48560642157, 1048772159673, 136028582177, 861863417206, 243536919859] := rfl
  have he : residualNumerators 18 16 1 = 743940548971065 := rfl
  have hr : radiusNumerators 16 = 10683060 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_17_0 :
    integerResidualCheck 18 17 0 (dualNumerators018 17 0) ∧
    integerMassCheck 18 17 0 (dualNumerators018 17 0) := by
  have hn : dualNumerators018 17 0 = ![602334801078, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546386, 0, 844525275676, 602334801077, 905187143137, 0, 1184097183123, 0, 1071829546386, 0, 0, 1000000000001, 2028622458797, 1713222941254, 933538524390, 1402919220984, 933538524390, 1105400337065, 905187143137, 0, 1184097183123, 0, 0, 0, 1402919220984, 1549866490728, 212975243914, 1336891246815, 0, 933538524390, 1251400905752, 57500519589, 1241848160005, 161071060979, 1020530044550, 288371380791] := rfl
  have he : residualNumerators 18 17 0 = 953768612513882 := rfl
  have hr : radiusNumerators 17 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_17_1 :
    integerResidualCheck 18 17 1 (dualNumerators018 17 1) ∧
    integerMassCheck 18 17 1 (dualNumerators018 17 1) := by
  have hn : dualNumerators018 17 1 = ![201148953074, 37030955649, 201148953074, 0, 1, 302286113723, 357936135756, 0, 282028158995, 201148953074, 0, 0, 0, 395427772555, 55650022034, 302286113723, 636234862349, 0, 677455931550, 572128657349, 311754022014, 468503118271, 311754022014, 369147059294, 0, 0, 0, 395427772555, 0, 302286113723, 468503118271, 517575975116, 71122816194, 446453158923, 0, 311754022014, 417903766505, 19202226562, 414713639017, 53789479254, 340804731313, 96301261755] := rfl
  have he : residualNumerators 18 17 1 = 327198874758791 := rfl
  have hr : radiusNumerators 17 = 15120968 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_18_0 :
    integerResidualCheck 18 18 0 (dualNumerators018 18 0) ∧
    integerMassCheck 18 18 0 (dualNumerators018 18 0) := by
  have hn : dualNumerators018 18 0 = ![0, 0, 0, 0, 1, 636538415125, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 261721072458, 1006675626970, 0, 763999473637, 936711106099, 134481966149, 862769256399, 123780303264, 835192545885, 236000526363] := rfl
  have he : residualNumerators 18 18 0 = 622507176557421 := rfl
  have hr : radiusNumerators 18 = 13565580 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_18_1 :
    integerResidualCheck 18 18 1 (dualNumerators018 18 1) ∧
    integerMassCheck 18 18 1 (dualNumerators018 18 1) := by
  have hn : dualNumerators018 18 1 = ![546080038515, 100531796850, 546080038516, 0, 1, 184109219884, 218003208651, 0, 74499415779, 53134692444, 184109219884, 0, 92880591654, 504519352651, 218003208651, 0, 0, 504519352652, 178954014012, 151131188017, 846351152950, 285344710532, 82351679314, 97512391500, 184109219884, 1, 92880591654, 504519352652, 0, 0, 285344710532, 781937638598, 13715132590, 123005639922, 82351679314, 0, 115464148095, 0, 180745426040, 104599284492, 90025596976, 25438551119] := rfl
  have he : residualNumerators 18 18 1 = 261214833881709 := rfl
  have hr : radiusNumerators 18 = 13565580 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_19_0 :
    integerResidualCheck 18 19 0 (dualNumerators018 19 0) ∧
    integerMassCheck 18 19 0 (dualNumerators018 19 0) := by
  have hn : dualNumerators018 19 0 = ![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 307298608851, 763894463397, 0, 645216866088, 704807657121, 199841967519, 577111910116, 96603051948, 705341215054, 199308409586] := rfl
  have he : residualNumerators 18 19 0 = 627988796584033 := rfl
  have hr : radiusNumerators 19 = 8248658 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_19_1 :
    integerResidualCheck 18 19 1 (dualNumerators018 19 1) ∧
    integerMassCheck 18 19 1 (dualNumerators018 19 1) := by
  have hn : dualNumerators018 19 1 = ![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 1, 987477735649, 0, 76640541789, 687358931849, 131755764247, 328427706730, 645216866088, 0, 761601233763, 225876501886, 503065535987, 142151330101] := rfl
  have he : residualNumerators 18 19 1 = 511657317280620 := rfl
  have hr : radiusNumerators 19 = 8248658 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_20_0 :
    integerResidualCheck 18 20 0 (dualNumerators018 20 0) ∧
    integerMassCheck 18 20 0 (dualNumerators018 20 0) := by
  have hn : dualNumerators018 20 0 = ![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 2105933038876, 0, 185761786322, 1009041980814, 2493629379175, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038874, 2, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 156880523801, 1406999830004, 941979561817, 0, 1320736486917, 0, 2067456287976, 1196458760692, 1029757657634, 290978829284] := rfl
  have he : residualNumerators 18 20 0 = 1359257388341391 := rfl
  have hr : radiusNumerators 20 = 35312013 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_20_1 :
    integerResidualCheck 18 20 1 (dualNumerators018 20 1) ∧
    integerMassCheck 18 20 1 (dualNumerators018 20 1) := by
  have hn : dualNumerators018 20 1 = ![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 1301213128929, 890779360508, 0, 1320313360088, 769869471398, 1081323590019, 0, 135852760286, 1443346382594, 407846678822] := rfl
  have he : residualNumerators 18 20 1 = 951089437154861 := rfl
  have hr : radiusNumerators 20 = 35312013 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_21_0 :
    integerResidualCheck 18 21 0 (dualNumerators018 21 0) ∧
    integerMassCheck 18 21 0 (dualNumerators018 21 0) := by
  have hn : dualNumerators018 21 0 = ![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 1, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 759767979803, 549133445537, 851509250277, 798941670661, 1020530044549, 288371380791] := rfl
  have he : residualNumerators 18 21 0 = 756964694627754 := rfl
  have hr : radiusNumerators 21 = 11182451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_21_1 :
    integerResidualCheck 18 21 1 (dualNumerators018 21 1) ∧
    integerMassCheck 18 21 1 (dualNumerators018 21 1) := by
  have hn : dualNumerators018 21 1 = ![114087637157, 21003212630, 114087637157, 0, 1, 11738971135, 13900082653, 0, 159960694697, 114087637156, 11738971135, 0, 218966847953, 1189409008000, 13900082653, 0, 0, 1189409008001, 1568336550649, 324499857786, 176820605835, 18193837997, 176820605835, 209372781287, 11738971135, 0, 218966847953, 1189409008000, 0, 0, 18193837997, 1843425165269, 878870811393, 964554353877, 0, 176820605835, 103103392317, 144814328227, 0, 18193837997, 193297583373, 54620137172] := rfl
  have he : residualNumerators 18 21 1 = 392958808718086 := rfl
  have hr : radiusNumerators 21 = 11182451 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_22_0 :
    integerResidualCheck 18 22 0 (dualNumerators018 22 0) ∧
    integerMassCheck 18 22 0 (dualNumerators018 22 0) := by
  have hn : dualNumerators018 22 0 = ![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 565168626292, 198830847345, 460183470977, 0, 216080085359, 429136780729, 256292246333, 545043834385, 503065535987, 142151330101] := rfl
  have he : residualNumerators 18 22 0 = 465141710705329 := rfl
  have hr : radiusNumerators 22 = 6465674 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_22_1 :
    integerResidualCheck 18 22 1 (dualNumerators018 22 1) ∧
    integerMassCheck 18 22 1 (dualNumerators018 22 1) := by
  have hn : dualNumerators018 22 1 = ![50594765625, 9314353833, 50594765625, 0, 0, 5205914576, 6164308785, 0, 70938219592, 50594765625, 5205914576, 0, 15463748427, 83997745994, 6164308785, 0, 0, 83997745994, 1170399714012, 143906865451, 78415131848, 8068472555, 78415131848, 92851136735, 5205914576, 0, 15463748427, 83997745994, 0, 0, 8068472555, 130185291813, 17889440442, 112295851372, 0, 78415131848, 45723551643, 64221217814, 0, 8068472555, 85722223462, 24222545996] := rfl
  have he : residualNumerators 18 22 1 = 99159262343373 := rfl
  have hr : radiusNumerators 22 = 6465674 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_23_0 :
    integerResidualCheck 18 23 0 (dualNumerators018 23 0) ∧
    integerMassCheck 18 23 0 (dualNumerators018 23 0) := by
  have hn : dualNumerators018 23 0 = ![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 2105933038876, 0, 185761786322, 1009041980814, 2493629379175, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038874, 2, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 1156880523801, 406999830004, 941979561817, 0, 1320736486917, 0, 2067456287976, 1196458760692, 1029757657634, 290978829284] := rfl
  have he : residualNumerators 18 23 0 = 1359257388341391 := rfl
  have hr : radiusNumerators 23 = 35297932 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_23_1 :
    integerResidualCheck 18 23 1 (dualNumerators018 23 1) ∧
    integerMassCheck 18 23 1 (dualNumerators018 23 1) := by
  have hn : dualNumerators018 23 1 = ![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 301213128929, 1890779360508, 0, 1320313360088, 769869471398, 1081323590019, 0, 135852760286, 1443346382594, 407846678822] := rfl
  have he : residualNumerators 18 23 1 = 951089437154861 := rfl
  have hr : radiusNumerators 23 = 35297932 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_24_0 :
    integerResidualCheck 18 24 0 (dualNumerators018 24 0) ∧
    integerMassCheck 18 24 0 (dualNumerators018 24 0) := by
  have hn : dualNumerators018 24 0 = ![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 512185690040, 559007382209, 569308312247, 737522866658, 835192545885, 236000526363] := rfl
  have he : residualNumerators 18 24 0 = 669501998447499 := rfl
  have hr : radiusNumerators 24 = 9356857 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_24_1 :
    integerResidualCheck 18 24 1 (dualNumerators018 24 1) ∧
    integerMassCheck 18 24 1 (dualNumerators018 24 1) := by
  have hn : dualNumerators018 24 1 = ![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623507, 113117556459, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 587483804282, 282115266095, 66021086067, 82038644814, 0, 0, 115439864933, 32619865948] := rfl
  have he : residualNumerators 18 24 1 = 232063481461635 := rfl
  have hr : radiusNumerators 24 = 9356857 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_25_0 :
    integerResidualCheck 18 25 0 (dualNumerators018 25 0) ∧
    integerMassCheck 18 25 0 (dualNumerators018 25 0) := by
  have hn : dualNumerators018 25 0 = ![30936264063, 5695279071, 30936264063, 0, 1, 16941043971, 20059842445, 0, 627070502755, 447241068346, 509886390043, 0, 136694444207, 742512415928, 603755038162, 0, 0, 742512415929, 1506277362888, 1272089305134, 47947079019, 26256356369, 693163945107, 820773474842, 509886390043, 1, 136694444206, 742512415929, 0, 0, 790255830005, 1150795112397, 638438115729, 512356996669, 47947079019, 0, 448879356988, 522996202554, 26256356369, 0, 757756228906, 214119330636] := rfl
  have he : residualNumerators 18 25 0 = 503068864811526 := rfl
  have hr : radiusNumerators 25 = 8671199 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_25_1 :
    integerResidualCheck 18 25 1 (dualNumerators018 25 1) ∧
    integerMassCheck 18 25 1 (dualNumerators018 25 1) := by
  have hn : dualNumerators018 25 1 = ![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 1, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 415529968297, 599898615461, 0, 0] := rfl
  have he : residualNumerators 18 25 1 = 225581994926756 := rfl
  have hr : radiusNumerators 25 = 8671199 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_26_0 :
    integerResidualCheck 18 26 0 (dualNumerators018 26 0) ∧
    integerMassCheck 18 26 0 (dualNumerators018 26 0) := by
  have hn : dualNumerators018 26 0 = ![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 1, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0] := rfl
  have he : residualNumerators 18 26 0 = 398909472332109 := rfl
  have hr : radiusNumerators 26 = 15099566 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_26_1 :
    integerResidualCheck 18 26 1 (dualNumerators018 26 1) ∧
    integerMassCheck 18 26 1 (dualNumerators018 26 1) := by
  have hn : dualNumerators018 26 1 = ![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 879744679617, 350168760452, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678] := rfl
  have he : residualNumerators 18 26 1 = 855428726190664 := rfl
  have hr : radiusNumerators 26 = 15099566 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_27_0 :
    integerResidualCheck 18 27 0 (dualNumerators018 27 0) ∧
    integerMassCheck 18 27 0 (dualNumerators018 27 0) := by
  have hn : dualNumerators018 27 0 = ![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 1, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 286173900105, 455299762271, 595678484088, 168320989550] := rfl
  have he : residualNumerators 18 27 0 = 411706678433767 := rfl
  have hr : radiusNumerators 27 = 7338775 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_27_1 :
    integerResidualCheck 18 27 1 (dualNumerators018 27 1) ∧
    integerMassCheck 18 27 1 (dualNumerators018 27 1) := by
  have hn : dualNumerators018 27 1 = ![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583262, 988432197465, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 575645700633, 956292240576, 0, 377837583379, 871790834897, 421969477217, 576174693322, 69042172766, 413046270426, 116714568052] := rfl
  have he : residualNumerators 18 27 1 = 548313091737443 := rfl
  have hr : radiusNumerators 27 = 7338775 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_28_0 :
    integerResidualCheck 18 28 0 (dualNumerators018 28 0) ∧
    integerMassCheck 18 28 0 (dualNumerators018 28 0) := by
  have hn : dualNumerators018 28 0 = ![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 1, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 450383711774, 395438493575, 503065535987, 142151330101] := rfl
  have he : residualNumerators 18 28 0 = 286363467233393 := rfl
  have hr : radiusNumerators 28 = 10335557 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_28_1 :
    integerResidualCheck 18 28 1 (dualNumerators018 28 1) ∧
    integerMassCheck 18 28 1 (dualNumerators018 28 1) := by
  have hn : dualNumerators018 28 1 = ![71098470185, 13089028086, 71098470186, 0, 1, 500260975618, 592357612055, 0, 99686179557, 71098470185, 7315629546, 0, 112480335850, 610983470480, 8662416338, 0, 0, 610983470481, 1239454790169, 202225622679, 110193136482, 775337722729, 110193136482, 130479382508, 7315629546, 0, 112480335850, 610983470480, 0, 0, 11338249092, 946942807286, 438489340489, 508453466798, 0, 110193136482, 456220281523, 343496853848, 0, 11338249092, 120461452361, 34038816922] := rfl
  have he : residualNumerators 18 28 1 = 310940117259515 := rfl
  have hr : radiusNumerators 28 = 10335557 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_29_0 :
    integerResidualCheck 18 29 0 (dualNumerators018 29 0) ∧
    integerMassCheck 18 29 0 (dualNumerators018 29 0) := by
  have hn : dualNumerators018 29 0 = ![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 1, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0] := rfl
  have he : residualNumerators 18 29 0 = 398909472332109 := rfl
  have hr : radiusNumerators 29 = 40352153 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_29_1 :
    integerResidualCheck 18 29 1 (dualNumerators018 29 1) ∧
    integerMassCheck 18 29 1 (dualNumerators018 29 1) := by
  have hn : dualNumerators018 29 1 = ![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 301213128929, 1890779360508, 0, 1320313360088, 1769869471398, 81323590019, 0, 135852760286, 1443346382594, 407846678822] := rfl
  have he : residualNumerators 18 29 1 = 951089437154861 := rfl
  have hr : radiusNumerators 29 = 40352153 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_30_0 :
    integerResidualCheck 18 30 0 (dualNumerators018 30 0) ∧
    integerMassCheck 18 30 0 (dualNumerators018 30 0) := by
  have hn : dualNumerators018 30 0 = ![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 115599349926, 0, 37915592377, 205954223378, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 1, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 43863150959, 275338398478, 0, 192266201784, 257731301679, 11842474856, 151451427040, 27712131761, 269573776534, 0] := rfl
  have he : residualNumerators 18 30 0 = 218125140200267 := rfl
  have hr : radiusNumerators 30 = 7680628 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_30_1 :
    integerResidualCheck 18 30 1 (dualNumerators018 30 1) ∧
    integerMassCheck 18 30 1 (dualNumerators018 30 1) := by
  have hn : dualNumerators018 30 1 = ![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195716, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 1, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 124312626679, 780336997961, 0, 544901951702, 730436696602, 33562777035, 829173251111, 99477537975, 536287180313, 227712293325] := rfl
  have he : residualNumerators 18 30 1 = 552665977409454 := rfl
  have hr : radiusNumerators 30 = 7680628 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_31_0 :
    integerResidualCheck 18 31 0 (dualNumerators018 31 0) ∧
    integerMassCheck 18 31 0 (dualNumerators018 31 0) := by
  have hn : dualNumerators018 31 0 = ![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1719079079316, 0, 1491143233587, 0, 2035556695381, 0, 1259308150413, 1, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079316, 0, 1491143233587, 0, 0, 0, 2664343059941, 1951759503826, 195790587527, 1755968916300, 668308387684, 1612704621868, 1648310233018, 0, 1640459045760, 1023884014182, 1648310233018, 0] := rfl
  have he : residualNumerators 18 31 0 = 1679881755463230 := rfl
  have hr : radiusNumerators 31 = 32891612 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_31_1 :
    integerResidualCheck 18 31 1 (dualNumerators018 31 1) ∧
    integerMassCheck 18 31 1 (dualNumerators018 31 1) := by
  have hn : dualNumerators018 31 1 = ![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 741061026801, 808805463926, 725570984152, 37986262977, 845258320866, 704608169862] := rfl
  have he : residualNumerators 18 31 1 = 651014209790618 := rfl
  have hr : radiusNumerators 31 = 32891612 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_32_0 :
    integerResidualCheck 18 32 0 (dualNumerators018 32 0) ∧
    integerMassCheck 18 32 0 (dualNumerators018 32 0) := by
  have hn : dualNumerators018 32 0 = ![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 0, 2079538667399, 1160276651773, 0, 382837210862, 2079538667397, 979882959195, 1, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 1160276651773, 0, 0, 0, 3223007296772, 1518687763292, 208690812242, 1309996951051, 0, 914758491801, 1226226422667, 56343779290, 2973224772447, 249782524326, 0, 1282570201956] := rfl
  have he : residualNumerators 18 32 0 = 1331802984767358 := rfl
  have hr : radiusNumerators 32 = 67647473 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerCheck018_32_1 :
    integerResidualCheck 18 32 1 (dualNumerators018 32 1) ∧
    integerMassCheck 18 32 1 (dualNumerators018 32 1) := by
  have hn : dualNumerators018 32 1 = ![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1946401957496, 0, 638403098873, 3467750500271, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957494, 2, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 738545008627, 4636005289951, 0, 3237278684975, 4339546116961, 199397455568, 2550060655570, 466602515837, 4538943572529, 0] := rfl
  have he : residualNumerators 18 32 1 = 2881676191205415 := rfl
  have hr : radiusNumerators 32 = 67647473 := rfl
  constructor
  · unfold integerResidualCheck
    simp_rw [branchDots018]
    rw [hn, he]
    decide
  · unfold integerMassCheck
    simp_rw [branchIntegerCurvature018_entry]
    rw [hn, he, hr]
    decide

theorem integerChecks018 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 18 j s (dualNumerators018 j s) ∧
    integerMassCheck 18 j s (dualNumerators018 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck018_0_0
    · exact integerCheck018_0_1
  · fin_cases s
    · exact integerCheck018_1_0
    · exact integerCheck018_1_1
  · fin_cases s
    · exact integerCheck018_2_0
    · exact integerCheck018_2_1
  · fin_cases s
    · exact integerCheck018_3_0
    · exact integerCheck018_3_1
  · fin_cases s
    · exact integerCheck018_4_0
    · exact integerCheck018_4_1
  · fin_cases s
    · exact integerCheck018_5_0
    · exact integerCheck018_5_1
  · fin_cases s
    · exact integerCheck018_6_0
    · exact integerCheck018_6_1
  · fin_cases s
    · exact integerCheck018_7_0
    · exact integerCheck018_7_1
  · fin_cases s
    · exact integerCheck018_8_0
    · exact integerCheck018_8_1
  · fin_cases s
    · exact integerCheck018_9_0
    · exact integerCheck018_9_1
  · fin_cases s
    · exact integerCheck018_10_0
    · exact integerCheck018_10_1
  · fin_cases s
    · exact integerCheck018_11_0
    · exact integerCheck018_11_1
  · fin_cases s
    · exact integerCheck018_12_0
    · exact integerCheck018_12_1
  · fin_cases s
    · exact integerCheck018_13_0
    · exact integerCheck018_13_1
  · fin_cases s
    · exact integerCheck018_14_0
    · exact integerCheck018_14_1
  · fin_cases s
    · exact integerCheck018_15_0
    · exact integerCheck018_15_1
  · fin_cases s
    · exact integerCheck018_16_0
    · exact integerCheck018_16_1
  · fin_cases s
    · exact integerCheck018_17_0
    · exact integerCheck018_17_1
  · fin_cases s
    · exact integerCheck018_18_0
    · exact integerCheck018_18_1
  · fin_cases s
    · exact integerCheck018_19_0
    · exact integerCheck018_19_1
  · fin_cases s
    · exact integerCheck018_20_0
    · exact integerCheck018_20_1
  · fin_cases s
    · exact integerCheck018_21_0
    · exact integerCheck018_21_1
  · fin_cases s
    · exact integerCheck018_22_0
    · exact integerCheck018_22_1
  · fin_cases s
    · exact integerCheck018_23_0
    · exact integerCheck018_23_1
  · fin_cases s
    · exact integerCheck018_24_0
    · exact integerCheck018_24_1
  · fin_cases s
    · exact integerCheck018_25_0
    · exact integerCheck018_25_1
  · fin_cases s
    · exact integerCheck018_26_0
    · exact integerCheck018_26_1
  · fin_cases s
    · exact integerCheck018_27_0
    · exact integerCheck018_27_1
  · fin_cases s
    · exact integerCheck018_28_0
    · exact integerCheck018_28_1
  · fin_cases s
    · exact integerCheck018_29_0
    · exact integerCheck018_29_1
  · fin_cases s
    · exact integerCheck018_30_0
    · exact integerCheck018_30_1
  · fin_cases s
    · exact integerCheck018_31_0
    · exact integerCheck018_31_1
  · fin_cases s
    · exact integerCheck018_32_0
    · exact integerCheck018_32_1

end ElevenSquare.Tasks.T06
