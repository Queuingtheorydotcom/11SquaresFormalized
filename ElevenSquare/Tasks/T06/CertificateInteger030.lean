import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual030
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
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn44
import ElevenSquare.Tasks.T06.SparseColumn47
import ElevenSquare.Tasks.T06.SparseColumn51

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix030 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral43, roundedGradientLiteral44, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix030_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = branchIntegerMatrix030 := by
  change roundedGradients ∘ branchRows 30 = branchIntegerMatrix030
  rw [show branchRows 30 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 34, 35, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral43_eq, roundedGradientLiteral44_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, branchIntegerMatrix030]

theorem branchColumn030_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 0) i) = _
  rw [branchColumn030_0]
  exact sparseColumn00_sum n

theorem branchColumn030_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 1) i) = _
  rw [branchColumn030_1]
  exact sparseColumn01_sum n

theorem branchColumn030_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 2) i) = _
  rw [branchColumn030_2]
  exact sparseColumn02_sum n

theorem branchColumn030_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 3) i) = _
  rw [branchColumn030_3]
  exact sparseColumn03_sum n

theorem branchColumn030_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 4) i) = _
  rw [branchColumn030_4]
  exact sparseColumn04_sum n

theorem branchColumn030_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 5) i) = _
  rw [branchColumn030_5]
  exact sparseColumn05_sum n

theorem branchColumn030_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 6) i) = _
  rw [branchColumn030_6]
  exact sparseColumn06_sum n

theorem branchColumn030_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 7) i) = _
  rw [branchColumn030_7]
  exact sparseColumn07_sum n

theorem branchColumn030_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 8) i) = _
  rw [branchColumn030_8]
  exact sparseColumn08_sum n

theorem branchColumn030_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 9) i) = _
  rw [branchColumn030_9]
  exact sparseColumn09_sum n

theorem branchColumn030_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 10) i) = _
  rw [branchColumn030_10]
  exact sparseColumn10_sum n

theorem branchColumn030_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 11) i) = _
  rw [branchColumn030_11]
  exact sparseColumn11_sum n

theorem branchColumn030_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 12) i) = _
  rw [branchColumn030_12]
  exact sparseColumn35_sum n

theorem branchColumn030_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 13) i) = _
  rw [branchColumn030_13]
  exact sparseColumn36_sum n

theorem branchColumn030_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 14) = sparseColumn37 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 14) = sparseDot37 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 14) i) = _
  rw [branchColumn030_14]
  exact sparseColumn37_sum n

theorem branchColumn030_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 15) i) = _
  rw [branchColumn030_15]
  exact sparseColumn38_sum n

theorem branchColumn030_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 16) i) = _
  rw [branchColumn030_16]
  exact sparseColumn39_sum n

theorem branchColumn030_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 17) = sparseColumn40 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 17) = sparseDot40 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 17) i) = _
  rw [branchColumn030_17]
  exact sparseColumn40_sum n

theorem branchColumn030_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 18) i) = _
  rw [branchColumn030_18]
  exact sparseColumn18_sum n

theorem branchColumn030_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 19) i) = _
  rw [branchColumn030_19]
  exact sparseColumn19_sum n

theorem branchColumn030_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 20) = sparseColumn20 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 20) = sparseDot20 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 20) i) = _
  rw [branchColumn030_20]
  exact sparseColumn20_sum n

theorem branchColumn030_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 21) i) = _
  rw [branchColumn030_21]
  exact sparseColumn21_sum n

theorem branchColumn030_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 22) i) = _
  rw [branchColumn030_22]
  exact sparseColumn22_sum n

theorem branchColumn030_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 23) = sparseColumn47 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 23) = sparseDot47 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 23) i) = _
  rw [branchColumn030_23]
  exact sparseColumn47_sum n

theorem branchColumn030_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 24) i) = _
  rw [branchColumn030_24]
  exact sparseColumn24_sum n

theorem branchColumn030_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 25) i) = _
  rw [branchColumn030_25]
  exact sparseColumn25_sum n

theorem branchColumn030_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 26) = sparseColumn44 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 26) = sparseDot44 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 26) i) = _
  rw [branchColumn030_26]
  exact sparseColumn44_sum n

theorem branchColumn030_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 27) i) = _
  rw [branchColumn030_27]
  exact sparseColumn27_sum n

theorem branchColumn030_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 28) i) = _
  rw [branchColumn030_28]
  exact sparseColumn28_sum n

theorem branchColumn030_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 29) = sparseColumn51 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 29) = sparseDot51 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 29) i) = _
  rw [branchColumn030_29]
  exact sparseColumn51_sum n

theorem branchColumn030_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 30) i) = _
  rw [branchColumn030_30]
  exact sparseColumn30_sum n

theorem branchColumn030_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 31) i) = _
  rw [branchColumn030_31]
  exact sparseColumn31_sum n

theorem branchColumn030_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 30 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 30 i)) = _
  rw [branchIntegerMatrix030_eq]
  simp only [branchIntegerMatrix030, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot030_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 30 i) 32) i) = _
  rw [branchColumn030_32]
  exact sparseColumn43_sum n

def branchSparseDots030 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot37, sparseDot38, sparseDot39, sparseDot40, sparseDot18, sparseDot19, sparseDot20, sparseDot21, sparseDot22, sparseDot47, sparseDot24, sparseDot25, sparseDot44, sparseDot27, sparseDot28, sparseDot51, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot030_0 :
    branchSparseDots030 0 = sparseDot00 := rfl

private theorem branchSparseDot030_1 :
    branchSparseDots030 1 = sparseDot01 := rfl

private theorem branchSparseDot030_2 :
    branchSparseDots030 2 = sparseDot02 := rfl

private theorem branchSparseDot030_3 :
    branchSparseDots030 3 = sparseDot03 := rfl

private theorem branchSparseDot030_4 :
    branchSparseDots030 4 = sparseDot04 := rfl

private theorem branchSparseDot030_5 :
    branchSparseDots030 5 = sparseDot05 := rfl

private theorem branchSparseDot030_6 :
    branchSparseDots030 6 = sparseDot06 := rfl

private theorem branchSparseDot030_7 :
    branchSparseDots030 7 = sparseDot07 := rfl

private theorem branchSparseDot030_8 :
    branchSparseDots030 8 = sparseDot08 := rfl

private theorem branchSparseDot030_9 :
    branchSparseDots030 9 = sparseDot09 := rfl

private theorem branchSparseDot030_10 :
    branchSparseDots030 10 = sparseDot10 := rfl

private theorem branchSparseDot030_11 :
    branchSparseDots030 11 = sparseDot11 := rfl

private theorem branchSparseDot030_12 :
    branchSparseDots030 12 = sparseDot35 := rfl

private theorem branchSparseDot030_13 :
    branchSparseDots030 13 = sparseDot36 := rfl

private theorem branchSparseDot030_14 :
    branchSparseDots030 14 = sparseDot37 := rfl

private theorem branchSparseDot030_15 :
    branchSparseDots030 15 = sparseDot38 := rfl

private theorem branchSparseDot030_16 :
    branchSparseDots030 16 = sparseDot39 := rfl

private theorem branchSparseDot030_17 :
    branchSparseDots030 17 = sparseDot40 := rfl

private theorem branchSparseDot030_18 :
    branchSparseDots030 18 = sparseDot18 := rfl

private theorem branchSparseDot030_19 :
    branchSparseDots030 19 = sparseDot19 := rfl

private theorem branchSparseDot030_20 :
    branchSparseDots030 20 = sparseDot20 := rfl

private theorem branchSparseDot030_21 :
    branchSparseDots030 21 = sparseDot21 := rfl

private theorem branchSparseDot030_22 :
    branchSparseDots030 22 = sparseDot22 := rfl

private theorem branchSparseDot030_23 :
    branchSparseDots030 23 = sparseDot47 := rfl

private theorem branchSparseDot030_24 :
    branchSparseDots030 24 = sparseDot24 := rfl

private theorem branchSparseDot030_25 :
    branchSparseDots030 25 = sparseDot25 := rfl

private theorem branchSparseDot030_26 :
    branchSparseDots030 26 = sparseDot44 := rfl

private theorem branchSparseDot030_27 :
    branchSparseDots030 27 = sparseDot27 := rfl

private theorem branchSparseDot030_28 :
    branchSparseDots030 28 = sparseDot28 := rfl

private theorem branchSparseDot030_29 :
    branchSparseDots030 29 = sparseDot51 := rfl

private theorem branchSparseDot030_30 :
    branchSparseDots030 30 = sparseDot30 := rfl

private theorem branchSparseDot030_31 :
    branchSparseDots030 31 = sparseDot31 := rfl

private theorem branchSparseDot030_32 :
    branchSparseDots030 32 = sparseDot43 := rfl

theorem branchDots030 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 30 i) k) = branchSparseDots030 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot030_0 n
      _ = _ := congrFun branchSparseDot030_0.symm n
  · calc
      _ = sparseDot01 n := branchDot030_1 n
      _ = _ := congrFun branchSparseDot030_1.symm n
  · calc
      _ = sparseDot02 n := branchDot030_2 n
      _ = _ := congrFun branchSparseDot030_2.symm n
  · calc
      _ = sparseDot03 n := branchDot030_3 n
      _ = _ := congrFun branchSparseDot030_3.symm n
  · calc
      _ = sparseDot04 n := branchDot030_4 n
      _ = _ := congrFun branchSparseDot030_4.symm n
  · calc
      _ = sparseDot05 n := branchDot030_5 n
      _ = _ := congrFun branchSparseDot030_5.symm n
  · calc
      _ = sparseDot06 n := branchDot030_6 n
      _ = _ := congrFun branchSparseDot030_6.symm n
  · calc
      _ = sparseDot07 n := branchDot030_7 n
      _ = _ := congrFun branchSparseDot030_7.symm n
  · calc
      _ = sparseDot08 n := branchDot030_8 n
      _ = _ := congrFun branchSparseDot030_8.symm n
  · calc
      _ = sparseDot09 n := branchDot030_9 n
      _ = _ := congrFun branchSparseDot030_9.symm n
  · calc
      _ = sparseDot10 n := branchDot030_10 n
      _ = _ := congrFun branchSparseDot030_10.symm n
  · calc
      _ = sparseDot11 n := branchDot030_11 n
      _ = _ := congrFun branchSparseDot030_11.symm n
  · calc
      _ = sparseDot35 n := branchDot030_12 n
      _ = _ := congrFun branchSparseDot030_12.symm n
  · calc
      _ = sparseDot36 n := branchDot030_13 n
      _ = _ := congrFun branchSparseDot030_13.symm n
  · calc
      _ = sparseDot37 n := branchDot030_14 n
      _ = _ := congrFun branchSparseDot030_14.symm n
  · calc
      _ = sparseDot38 n := branchDot030_15 n
      _ = _ := congrFun branchSparseDot030_15.symm n
  · calc
      _ = sparseDot39 n := branchDot030_16 n
      _ = _ := congrFun branchSparseDot030_16.symm n
  · calc
      _ = sparseDot40 n := branchDot030_17 n
      _ = _ := congrFun branchSparseDot030_17.symm n
  · calc
      _ = sparseDot18 n := branchDot030_18 n
      _ = _ := congrFun branchSparseDot030_18.symm n
  · calc
      _ = sparseDot19 n := branchDot030_19 n
      _ = _ := congrFun branchSparseDot030_19.symm n
  · calc
      _ = sparseDot20 n := branchDot030_20 n
      _ = _ := congrFun branchSparseDot030_20.symm n
  · calc
      _ = sparseDot21 n := branchDot030_21 n
      _ = _ := congrFun branchSparseDot030_21.symm n
  · calc
      _ = sparseDot22 n := branchDot030_22 n
      _ = _ := congrFun branchSparseDot030_22.symm n
  · calc
      _ = sparseDot47 n := branchDot030_23 n
      _ = _ := congrFun branchSparseDot030_23.symm n
  · calc
      _ = sparseDot24 n := branchDot030_24 n
      _ = _ := congrFun branchSparseDot030_24.symm n
  · calc
      _ = sparseDot25 n := branchDot030_25 n
      _ = _ := congrFun branchSparseDot030_25.symm n
  · calc
      _ = sparseDot44 n := branchDot030_26 n
      _ = _ := congrFun branchSparseDot030_26.symm n
  · calc
      _ = sparseDot27 n := branchDot030_27 n
      _ = _ := congrFun branchSparseDot030_27.symm n
  · calc
      _ = sparseDot28 n := branchDot030_28 n
      _ = _ := congrFun branchSparseDot030_28.symm n
  · calc
      _ = sparseDot51 n := branchDot030_29 n
      _ = _ := congrFun branchSparseDot030_29.symm n
  · calc
      _ = sparseDot30 n := branchDot030_30 n
      _ = _ := congrFun branchSparseDot030_30.symm n
  · calc
      _ = sparseDot31 n := branchDot030_31 n
      _ = _ := congrFun branchSparseDot030_31.symm n
  · calc
      _ = sparseDot43 n := branchDot030_32 n
      _ = _ := congrFun branchSparseDot030_32.symm n

def branchIntegerCurvature030 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101981296, 101981296, 44932602, 44932602, 106371291, 106371291, 88123140, 88123140, 289103692, 289103692]

theorem branchIntegerCurvature030_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 30 i)) = branchIntegerCurvature030 := by
  change curvatureNumerators ∘ branchRows 30 = branchIntegerCurvature030
  rw [show branchRows 30 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 32, 33, 34, 35, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature030_entry (i : Fin 42) :
    curvatureNumerators (branchRows 30 i) = branchIntegerCurvature030 i :=
  congrFun branchIntegerCurvature030_eq i

def branchResiduals030 : Fin 33 → Fin 2 → ℕ := ![![1300358336468381, 33000000000000], ![1546816113778914, 33000000000000], ![1581653545167794, 1336893010626554], ![33000000000000, 1026199967847106], ![859891589261805, 33000000000000], ![1054307365133946, 892416068851973], ![720684911205881, 625122527367431], ![33000000000000, 759838294761607], ![1580856237574572, 1130657903197592], ![1026601655281641, 33000000000000], ![33000000000000, 777248020565494], ![506225412439127, 465887304914862], ![991199967847139, 66000000000000], ![33000000000000, 859881957696430], ![1054307365133946, 890916068852006], ![472006214678094, 33000000000000], ![66000000000000, 743737017360069], ![956814815390115, 326696721106769], ![622401112200789, 265008284230372], ![632916882910007, 508587812833503], ![1358631289954845, 948060882882844], ![756727018943422, 387586934288278], ![471055853251425, 104116699803623], ![1358631289954845, 948060882882844], ![672506328062528, 232003409392821], ![504097306550387, 225581994926756], ![401579096206218, 852454589586214], ![411819502736388, 551427497466098], ![286791123956719, 306738571147157], ![401579096206218, 948060882882844], ![104116699803623, 554743292407025], ![966853661322335, 651147106671326], ![2024565785685905, 948060882882844]]

theorem branchResiduals030_eq : residualNumerators 30 = branchResiduals030 := rfl

theorem integerCheck030_0_0 :
    integerResidualCheck 30 0 0 (dualNumerators030 0 0) ∧
    integerMassCheck 30 0 0 (dualNumerators030 0 0) := by
  apply integerChecks_of_simple 30 0 0 (dualNumerators030 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1607511062796, 565535261271, 1308901425339, 0, 445670439042, 1389522106843, 1485808378804, 481205215181, 818327875519, 1016864670366]) (branchResiduals030 0 0) 18767167
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck030_0_1 :
    integerResidualCheck 30 0 1 (dualNumerators030 0 1) ∧
    integerMassCheck 30 0 1 (dualNumerators030 0 1) := by
  apply integerChecks_of_simple 30 0 1 (dualNumerators030 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals030 0 1) 18767167
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck030_1_0 :
    integerResidualCheck 30 1 0 (dualNumerators030 1 0) ∧
    integerMassCheck 30 1 0 (dualNumerators030 1 0) := by
  apply integerChecks_of_simple 30 1 0 (dualNumerators030 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 1903449321293, 669648709827, 1549866490727, 0, 527717111470, 1645329212598, 1759341515999, 569793739799, 968979732271, 1204066591796]) (branchResiduals030 1 0) 22176635
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck030_1_1 :
    integerResidualCheck 30 1 1 (dualNumerators030 1 1) ∧
    integerMassCheck 30 1 1 (dualNumerators030 1 1) := by
  apply integerChecks_of_simple 30 1 1 (dualNumerators030 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals030 1 1) 22176635
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck030_2_0 :
    integerResidualCheck 30 2 0 (dualNumerators030 2 0) ∧
    integerMassCheck 30 2 0 (dualNumerators030 2 0) := by
  apply integerChecks_of_simple 30 2 0 (dualNumerators030 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 1903449321295, 669648709827, 1549866490728, 0, 527717111470, 1645329212599, 1759341516001, 569793739799, 968979732272, 1204066591797]) (branchResiduals030 2 0) 22681452
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck030_2_1 :
    integerResidualCheck 30 2 1 (dualNumerators030 2 1) ∧
    integerMassCheck 30 2 1 (dualNumerators030 2 1) := by
  apply integerChecks_of_simple 30 2 1 (dualNumerators030 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1607511062795, 565535261271, 1308901425338, 0, 445670439042, 1389522106842, 1485808378803, 481205215180, 818327875518, 1016864670365]) (branchResiduals030 2 1) 22681452
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck030_3_0 :
    integerResidualCheck 30 3 0 (dualNumerators030 3 0) ∧
    integerMassCheck 30 3 0 (dualNumerators030 3 0) := by
  apply integerChecks_of_simple 30 3 0 (dualNumerators030 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals030 3 0) 16360330
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck030_3_1 :
    integerResidualCheck 30 3 1 (dualNumerators030 3 1) ∧
    integerMassCheck 30 3 1 (dualNumerators030 3 1) := by
  apply integerChecks_of_simple 30 3 1 (dualNumerators030 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000000, 0, 203380245200, 1104743927907, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 351156535721, 1094844366154, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals030 3 1) 16360330
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck030_4_0 :
    integerResidualCheck 30 4 0 (dualNumerators030 4 0) ∧
    integerMassCheck 30 4 0 (dualNumerators030 4 0) := by
  apply integerChecks_of_simple 30 4 0 (dualNumerators030 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757645, 932984170265, 1000000000001, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1069679196818, 376321705057, 870976665588, 0, 296560570134, 924623740146, 988695101419, 320206323920, 544536410901, 676647899379]) (branchResiduals030 4 0) 13760362
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck030_4_1 :
    integerResidualCheck 30 4 1 (dualNumerators030 4 1) ∧
    integerMassCheck 30 4 1 (dualNumerators030 4 1) := by
  apply integerChecks_of_simple 30 4 1 (dualNumerators030 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals030 4 1) 13760362
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck030_5_0 :
    integerResidualCheck 30 5 0 (dualNumerators030 5 0) ∧
    integerMassCheck 30 5 0 (dualNumerators030 5 0) := by
  apply integerChecks_of_simple 30 5 0 (dualNumerators030 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245201, 1104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000000, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1266604123796, 445601470905, 1031321016288, 0, 351156535721, 1094844366155, 1170711084557, 379155406172, 644784030255, 801216871620]) (branchResiduals030 5 0) 17641130
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck030_5_1 :
    integerResidualCheck 30 5 1 (dualNumerators030 5 1) ∧
    integerMassCheck 30 5 1 (dualNumerators030 5 1) := by
  apply integerChecks_of_simple 30 5 1 (dualNumerators030 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170264, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1069679196817, 376321705056, 870976665588, 0, 296560570134, 924623740145, 988695101418, 320206323920, 544536410901, 676647899378]) (branchResiduals030 5 1) 17641130
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck030_6_0 :
    integerResidualCheck 30 6 0 (dualNumerators030 6 0) ∧
    integerMassCheck 30 6 0 (dualNumerators030 6 0) := by
  apply integerChecks_of_simple 30 6 0 (dualNumerators030 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 877488274356, 957704271528, 2719950702, 106626845062, 818327875519, 1016864670366]) (branchResiduals030 6 0) 8962451
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck030_6_1 :
    integerResidualCheck 30 6 1 (dualNumerators030 6 1) ∧
    integerMassCheck 30 6 1 (dualNumerators030 6 1) := by
  apply integerChecks_of_simple 30 6 1 (dualNumerators030 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 1, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals030 6 1) 8962451
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck030_7_0 :
    integerResidualCheck 30 7 0 (dualNumerators030 7 0) ∧
    integerMassCheck 30 7 0 (dualNumerators030 7 0) := by
  apply integerChecks_of_simple 30 7 0 (dualNumerators030 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals030 7 0) 10424794
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck030_7_1 :
    integerResidualCheck 30 7 1 (dualNumerators030 7 1) ∧
    integerMassCheck 30 7 1 (dualNumerators030 7 1) := by
  apply integerChecks_of_simple 30 7 1 (dualNumerators030 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646810, 830103123887, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675220, 1, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 951724660649, 334824354914, 774933245365, 0, 263858555736, 822664606300, 879670758001, 284896869900, 484489866137, 602033295899]) (branchResiduals030 7 1) 10424794
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck030_8_0 :
    integerResidualCheck 30 8 0 (dualNumerators030 8 0) ∧
    integerMassCheck 30 8 0 (dualNumerators030 8 0) := by
  apply integerChecks_of_simple 30 8 0 (dualNumerators030 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293619, 1660206247774, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350440, 2, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 1903449321297, 669648709828, 1549866490730, 0, 527717111471, 1645329212600, 1759341516002, 569793739800, 968979732273, 1204066591798]) (branchResiduals030 8 0) 22681452
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck030_8_1 :
    integerResidualCheck 30 8 1 (dualNumerators030 8 1) ∧
    integerMassCheck 30 8 1 (dualNumerators030 8 1) := by
  apply integerChecks_of_simple 30 8 1 (dualNumerators030 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590429, 217988955956, 0, 1402086139075, 1269150346660, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546384, 0, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1357583723455, 477608822428, 1105400337063, 0, 376379950391, 1173486540335, 1254802730706, 406389967006, 691098574663, 858767916063]) (branchResiduals030 8 1) 22681452
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck030_9_0 :
    integerResidualCheck 30 9 0 (dualNumerators030 9 0) ∧
    integerMassCheck 30 9 0 (dualNumerators030 9 0) := by
  apply integerChecks_of_simple 30 9 0 (dualNumerators030 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 351156535721, 1094844366154, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals030 9 0) 16350530
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck030_9_1 :
    integerResidualCheck 30 9 1 (dualNumerators030 9 1) ∧
    integerMassCheck 30 9 1 (dualNumerators030 9 1) := by
  apply integerChecks_of_simple 30 9 1 (dualNumerators030 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals030 9 1) 16350530
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck030_10_0 :
    integerResidualCheck 30 10 0 (dualNumerators030 10 0) ∧
    integerMassCheck 30 10 0 (dualNumerators030 10 0) := by
  apply integerChecks_of_simple 30 10 0 (dualNumerators030 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals030 10 0) 10683139
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck030_10_1 :
    integerResidualCheck 30 10 1 (dualNumerators030 10 1) ∧
    integerMassCheck 30 10 1 (dualNumerators030 10 1) := by
  apply integerChecks_of_simple 30 10 1 (dualNumerators030 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 968259856239, 340641569100, 788396879662, 0, 268442815247, 836957521818, 894954094286, 289846647564, 492907358117, 612492978948]) (branchResiduals030 10 1) 10683139
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck030_11_0 :
    integerResidualCheck 30 11 0 (dualNumerators030 11 0) ∧
    integerMassCheck 30 11 0 (dualNumerators030 11 0) := by
  apply integerChecks_of_simple 30 11 0 (dualNumerators030 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 601785379685, 211712914335, 489998333105, 0, 166840503049, 520179367968, 556224949284, 180143247425, 306347970271, 380671900746]) (branchResiduals030 11 0) 15120968
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck030_11_1 :
    integerResidualCheck 30 11 1 (dualNumerators030 11 1) ∧
    integerMassCheck 30 11 1 (dualNumerators030 11 1) := by
  apply integerChecks_of_simple 30 11 1 (dualNumerators030 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 548759091280, 193057841557, 446822154676, 0, 152139360530, 474343789173, 507213215908, 164269934257, 279354134309, 347129015395]) (branchResiduals030 11 1) 15120968
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck030_12_0 :
    integerResidualCheck 30 12 0 (dualNumerators030 12 0) ∧
    integerMassCheck 30 12 0 (dualNumerators030 12 0) := by
  apply integerChecks_of_simple 30 12 0 (dualNumerators030 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 351156535721, 1094844366154, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals030 12 0) 16348076
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck030_12_1 :
    integerResidualCheck 30 12 1 (dualNumerators030 12 1) ∧
    integerMassCheck 30 12 1 (dualNumerators030 12 1) := by
  apply integerChecks_of_simple 30 12 1 (dualNumerators030 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals030 12 1) 16348076
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck030_13_0 :
    integerResidualCheck 30 13 0 (dualNumerators030 13 0) ∧
    integerMassCheck 30 13 0 (dualNumerators030 13 0) := by
  apply integerChecks_of_simple 30 13 0 (dualNumerators030 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals030 13 0) 13962901
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck030_13_1 :
    integerResidualCheck 30 13 1 (dualNumerators030 13 1) ∧
    integerMassCheck 30 13 1 (dualNumerators030 13 1) := by
  apply integerChecks_of_simple 30 13 1 (dualNumerators030 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1069679196818, 376321705057, 870976665588, 0, 296560570134, 924623740146, 988695101419, 320206323920, 544536410901, 676647899379]) (branchResiduals030 13 1) 13962901
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck030_14_0 :
    integerResidualCheck 30 14 0 (dualNumerators030 14 0) ∧
    integerMassCheck 30 14 0 (dualNumerators030 14 0) := by
  apply integerChecks_of_simple 30 14 0 (dualNumerators030 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1266604123796, 445601470905, 1031321016288, 0, 351156535721, 1094844366155, 1170711084557, 379155406172, 644784030255, 801216871620]) (branchResiduals030 14 0) 20161291
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck030_14_1 :
    integerResidualCheck 30 14 1 (dualNumerators030 14 1) ∧
    integerMassCheck 30 14 1 (dualNumerators030 14 1) := by
  apply integerChecks_of_simple 30 14 1 (dualNumerators030 14 1)
    (![561968834605, 103456879454, 561968834605, 0, 1, 844525275673, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 0, 1000000000000, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1069679196817, 376321705056, 870976665588, 0, 296560570134, 924623740145, 988695101418, 320206323920, 544536410901, 676647899378]) (branchResiduals030 14 1) 20161291
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck030_15_0 :
    integerResidualCheck 30 15 0 (dualNumerators030 15 0) ∧
    integerMassCheck 30 15 0 (dualNumerators030 15 0) := by
  apply integerChecks_of_simple 30 15 0 (dualNumerators030 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819834, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819834, 475117180167, 0, 736368196709, 813498294019, 601785379685, 211712914334, 489998333105, 0, 166840503049, 520179367968, 556224949284, 180143247425, 306347970271, 380671900746]) (branchResiduals030 15 0) 12900283
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck030_15_1 :
    integerResidualCheck 30 15 1 (dualNumerators030 15 1) ∧
    integerMassCheck 30 15 1 (dualNumerators030 15 1) := by
  apply integerChecks_of_simple 30 15 1 (dualNumerators030 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals030 15 1) 12900283
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck030_16_0 :
    integerResidualCheck 30 16 0 (dualNumerators030 16 0) ∧
    integerMassCheck 30 16 0 (dualNumerators030 16 0) := by
  apply integerChecks_of_simple 30 16 0 (dualNumerators030 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals030 16 0) 10683060
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck030_16_1 :
    integerResidualCheck 30 16 1 (dualNumerators030 16 1) ∧
    integerMassCheck 30 16 1 (dualNumerators030 16 1) := by
  apply integerChecks_of_simple 30 16 1 (dualNumerators030 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 968259856239, 340641569100, 788396879662, 0, 268442815247, 836957521818, 894954094286, 289846647564, 492907358117, 612492978948]) (branchResiduals030 16 1) 10683060
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck030_17_0 :
    integerResidualCheck 30 17 0 (dualNumerators030 17 0) ∧
    integerMassCheck 30 17 0 (dualNumerators030 17 0) := by
  apply integerChecks_of_simple 30 17 0 (dualNumerators030 17 0)
    (![602334801078, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546386, 0, 844525275676, 602334801077, 905187143137, 0, 1184097183123, 0, 1071829546386, 0, 0, 1000000000001, 2028622458797, 1713222941254, 933538524390, 1402919220984, 933538524390, 1105400337065, 905187143137, 0, 1184097183123, 0, 0, 0, 1402919220984, 1549866490728, 1146513768303, 403352722426, 933538524390, 0, 317862381363, 991039043978, 1059712622068, 343206598917, 583650214286, 725251211054]) (branchResiduals030 17 0) 15120968
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck030_17_1 :
    integerResidualCheck 30 17 1 (dualNumerators030 17 1) ∧
    integerMassCheck 30 17 1 (dualNumerators030 17 1) := by
  apply integerChecks_of_simple 30 17 1 (dualNumerators030 17 1)
    (![201148953074, 37030955649, 201148953074, 0, 1, 302286113723, 357936135756, 0, 282028158995, 201148953074, 0, 0, 0, 395427772555, 55650022034, 302286113723, 636234862349, 0, 677455931550, 572128657349, 311754022014, 468503118271, 311754022014, 369147059294, 0, 0, 0, 395427772555, 0, 302286113723, 468503118271, 517575975116, 382876838207, 134699136909, 311754022014, 0, 106149744492, 330956248576, 353889704043, 114613414229, 194909258696, 242196734371]) (branchResiduals030 17 1) 15120968
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck030_18_0 :
    integerResidualCheck 30 18 0 (dualNumerators030 18 0) ∧
    integerMassCheck 30 18 0 (dualNumerators030 18 0) := by
  apply integerChecks_of_simple 30 18 0 (dualNumerators030 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 1025720546095, 242676153333, 763999473637, 0, 172711632462, 898481439786, 863239815324, 123309744339, 477654049462, 593539022787]) (branchResiduals030 18 0) 13565580
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck030_18_1 :
    integerResidualCheck 30 18 1 (dualNumerators030 18 1) ∧
    integerMassCheck 30 18 1 (dualNumerators030 18 1) := by
  apply integerChecks_of_simple 30 18 1 (dualNumerators030 18 1)
    (![546080038515, 100531796850, 546080038516, 0, 1, 184109219884, 218003208651, 0, 74499415779, 53134692444, 184109219884, 0, 92880591654, 504519352651, 218003208651, 0, 0, 504519352652, 178954014012, 151131188017, 846351152950, 285344710532, 82351679314, 97512391500, 184109219884, 1, 92880591654, 504519352652, 0, 0, 285344710532, 781937638598, 13715132590, 123005639922, 82351679314, 0, 115464148095, 0, 97501467496, 187843243037, 51486440059, 63977708037]) (branchResiduals030 18 1) 13565580
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck030_19_0 :
    integerResidualCheck 30 19 0 (dualNumerators030 19 0) ∧
    integerMassCheck 30 19 0 (dualNumerators030 19 0) := by
  apply integerChecks_of_simple 30 19 0 (dualNumerators030 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 901168865389, 170024206859, 593870256538, 51346609551, 110937400584, 793712224057, 673714962064, 0, 403390917798, 501258706842]) (branchResiduals030 19 0) 8248658
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck030_19_1 :
    integerResidualCheck 30 19 1 (dualNumerators030 19 1) ∧
    integerMassCheck 30 19 1 (dualNumerators030 19 1) := by
  apply integerChecks_of_simple 30 19 1 (dualNumerators030 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 1, 987477735649, 0, 405068248518, 358931225119, 460183470977, 0, 316789159358, 328427706730, 529741159093, 457736576556, 287707656866, 357509209222]) (branchResiduals030 19 1) 8248658
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck030_20_0 :
    integerResidualCheck 30 20 0 (dualNumerators030 20 0) ∧
    integerMassCheck 30 20 0 (dualNumerators030 20 0) := by
  apply integerChecks_of_simple 30 20 0 (dualNumerators030 20 0)
    (![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 2105933038876, 0, 185761786322, 1009041980814, 2493629379175, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038874, 2, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 156880523801, 1406999830004, 941979561817, 0, 1320736486917, 0, 1115270391492, 2148644657176, 588927568327, 731808918591]) (branchResiduals030 20 0) 35312013
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck030_20_1 :
    integerResidualCheck 30 20 1 (dualNumerators030 20 1) ∧
    integerMassCheck 30 20 1 (dualNumerators030 20 1) := by
  apply integerChecks_of_simple 30 20 1 (dualNumerators030 20 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 85258653367, 0, 259883317327, 1411663736071, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 0, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 1300649428514, 887240892199, 0, 1317842481106, 766557277936, 1081171398308, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals030 20 1) 35312013
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck030_21_0 :
    integerResidualCheck 30 21 0 (dualNumerators030 21 0) ∧
    integerMassCheck 30 21 0 (dualNumerators030 21 0) := by
  apply integerChecks_of_simple 30 21 0 (dualNumerators030 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 1, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 759767979803, 549133445537, 757887471419, 892563449519, 583650214286, 725251211053]) (branchResiduals030 21 0) 11182451
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck030_21_1 :
    integerResidualCheck 30 21 1 (dualNumerators030 21 1) ∧
    integerMassCheck 30 21 1 (dualNumerators030 21 1) := by
  apply integerChecks_of_simple 30 21 1 (dualNumerators030 21 1)
    (![113874129702, 20963906509, 113874129702, 0, 1, 11418112698, 13520155082, 0, 159661338854, 113874129702, 11418112698, 0, 218901591686, 1189054541590, 13520155082, 0, 0, 1189054541591, 1567617472129, 323892577801, 176489697786, 17696550257, 176489697786, 208980953998, 11418112698, 0, 218901591686, 1189054541590, 0, 0, 17696550257, 1842875789658, 878795318822, 964080470836, 0, 176489697786, 102659812730, 144793946225, 17696550257, 0, 110341723711, 137112035244]) (branchResiduals030 21 1) 11182451
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck030_22_0 :
    integerResidualCheck 30 22 0 (dualNumerators030 22 0) ∧
    integerMassCheck 30 22 0 (dualNumerators030 22 0) := by
  apply integerChecks_of_simple 30 22 0 (dualNumerators030 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 136031845564, 627967628074, 31046690248, 429136780729, 645216866088, 0, 95974191249, 705361889470, 287707656866, 357509209222]) (branchResiduals030 22 0) 6465674
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck030_22_1 :
    integerResidualCheck 30 22 1 (dualNumerators030 22 1) ∧
    integerMassCheck 30 22 1 (dualNumerators030 22 1) := by
  apply integerChecks_of_simple 30 22 1 (dualNumerators030 22 1)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 5063622582, 0, 15434809046, 83840549778, 5995821236, 0, 0, 83840549778, 1170080822236, 143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 17855961539, 112085697126, 0, 78268383123, 45526836155, 64212178950, 7847938961, 0, 48933554844, 60805460262]) (branchResiduals030 22 1) 6465674
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck030_23_0 :
    integerResidualCheck 30 23 0 (dualNumerators030 23 0) ∧
    integerMassCheck 30 23 0 (dualNumerators030 23 0) := by
  apply integerChecks_of_simple 30 23 0 (dualNumerators030 23 0)
    (![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 2105933038876, 0, 185761786322, 1009041980814, 2493629379175, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038874, 2, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 1156880523801, 406999830004, 941979561817, 0, 1320736486917, 0, 1115270391492, 2148644657176, 588927568327, 731808918591]) (branchResiduals030 23 0) 35297932
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck030_23_1 :
    integerResidualCheck 30 23 1 (dualNumerators030 23 1) ∧
    integerMassCheck 30 23 1 (dualNumerators030 23 1) := by
  apply integerChecks_of_simple 30 23 1 (dualNumerators030 23 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 85258653367, 0, 259883317327, 1411663736071, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 0, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 766557277936, 1081171398308, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals030 23 1) 35297932
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck030_24_0 :
    integerResidualCheck 30 24 0 (dualNumerators030 24 0) ∧
    integerMassCheck 30 24 0 (dualNumerators030 24 0) := by
  apply integerChecks_of_simple 30 24 0 (dualNumerators030 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 512185690040, 559007382209, 705016048726, 601815130180, 477654049462, 593539022787]) (branchResiduals030 24 0) 9356857
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck030_24_1 :
    integerResidualCheck 30 24 1 (dualNumerators030 24 1) ∧
    integerMassCheck 30 24 1 (dualNumerators030 24 1) := by
  apply integerChecks_of_simple 30 24 1 (dualNumerators030 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623507, 113117556459, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 587483804282, 282115266095, 66021086067, 82038644814, 0, 0, 66021086067, 82038644814]) (branchResiduals030 24 1) 9356857
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck030_25_0 :
    integerResidualCheck 30 25 0 (dualNumerators030 25 0) ∧
    integerMassCheck 30 25 0 (dualNumerators030 25 0) := by
  apply integerChecks_of_simple 30 25 0 (dualNumerators030 25 0)
    (![31307490826, 5763620872, 31307490826, 0, 1, 17498922567, 20720424919, 0, 627590994654, 447612295109, 510444268639, 0, 136807905692, 743128728920, 604415620636, 0, 0, 743128728921, 1507527629264, 1273145186690, 48522430940, 27120993710, 693739297027, 821454747430, 510444268639, 1, 136807905692, 743128728920, 0, 0, 791120467347, 1151750315250, 639144727059, 512605588192, 48522430940, 0, 449075259703, 523606992792, 0, 27120993710, 433727241876, 538955010618]) (branchResiduals030 25 0) 8671199
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck030_25_1 :
    integerResidualCheck 30 25 1 (dualNumerators030 25 1) ∧
    integerMassCheck 30 25 1 (dualNumerators030 25 1) := by
  apply integerChecks_of_simple 30 25 1 (dualNumerators030 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 1, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals030 25 1) 8671199
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck030_26_0 :
    integerResidualCheck 30 26 0 (dualNumerators030 26 0) ∧
    integerMassCheck 30 26 0 (dualNumerators030 26 0) := by
  apply integerChecks_of_simple 30 26 0 (dualNumerators030 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 1, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals030 26 0) 15099566
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck030_26_1 :
    integerResidualCheck 30 26 1 (dualNumerators030 26 1) ∧
    integerMassCheck 30 26 1 (dualNumerators030 26 1) := by
  apply integerChecks_of_simple 30 26 1 (dualNumerators030 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 879744679617, 350168760452, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals030 26 1) 15099566
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck030_27_0 :
    integerResidualCheck 30 27 0 (dualNumerators030 27 0) ∧
    integerMassCheck 30 27 0 (dualNumerators030 27 0) := by
  apply integerChecks_of_simple 30 27 0 (dualNumerators030 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 1, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 436855949686, 304617712691, 340673826058, 423325647580]) (branchResiduals030 27 0) 7338775
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck030_27_1 :
    integerResidualCheck 30 27 1 (dualNumerators030 27 1) ∧
    integerMassCheck 30 27 1 (dualNumerators030 27 1) := by
  apply integerChecks_of_simple 30 27 1 (dualNumerators030 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583262, 988432197465, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 953483284011, 578454657198, 377837583379, 0, 493953251519, 799807060596, 430830286610, 214386579479, 236224837801, 293536000677]) (branchResiduals030 27 1) 7338775
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck030_28_0 :
    integerResidualCheck 30 28 0 (dualNumerators030 28 0) ∧
    integerMassCheck 30 28 0 (dualNumerators030 28 0) := by
  apply integerChecks_of_simple 30 28 0 (dualNumerators030 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 1, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 374399059503, 471423145846, 287707656866, 357509209222]) (branchResiduals030 28 0) 10335557
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck030_28_1 :
    integerResidualCheck 30 28 1 (dualNumerators030 28 1) ∧
    integerMassCheck 30 28 1 (dualNumerators030 28 1) := by
  apply integerChecks_of_simple 30 28 1 (dualNumerators030 28 1)
    (![70965414109, 13064532837, 70965414109, 0, 1, 500061019298, 592120844340, 0, 99499623476, 70965414109, 7115673227, 0, 112439668685, 610762569950, 8425648624, 0, 0, 610762569951, 1239006666393, 201847170824, 109986917328, 775027817129, 109986917328, 130235198988, 7115673227, 0, 112439668685, 610762569950, 0, 0, 11028343493, 946600440957, 438442294144, 508158146813, 0, 109986917328, 455943846399, 343484151953, 11028343493, 0, 68764047964, 85447084301]) (branchResiduals030 28 1) 10335557
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck030_29_0 :
    integerResidualCheck 30 29 0 (dualNumerators030 29 0) ∧
    integerMassCheck 30 29 0 (dualNumerators030 29 0) := by
  apply integerChecks_of_simple 30 29 0 (dualNumerators030 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 1, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals030 29 0) 40352153
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck030_29_1 :
    integerResidualCheck 30 29 1 (dualNumerators030 29 1) ∧
    integerMassCheck 30 29 1 (dualNumerators030 29 1) := by
  apply integerChecks_of_simple 30 29 1 (dualNumerators030 29 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 85258653367, 0, 259883317327, 1411663736071, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 0, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 1766557277936, 81171398308, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals030 29 1) 40352153
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck030_30_0 :
    integerResidualCheck 30 30 0 (dualNumerators030 30 0) ∧
    integerMassCheck 30 30 0 (dualNumerators030 30 0) := by
  apply integerChecks_of_simple 30 30 0 (dualNumerators030 30 0)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 5063622582, 0, 15434809046, 83840549778, 5995821236, 0, 0, 83840549778, 170080822236, 1143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 17855961539, 112085697126, 0, 78268383123, 104918139930, 4820875175, 7847938961, 0, 108324858619, 1414156487]) (branchResiduals030 30 0) 7680628
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck030_30_1 :
    integerResidualCheck 30 30 1 (dualNumerators030 30 1) ∧
    integerMassCheck 30 30 1 (dualNumerators030 30 1) := by
  apply integerChecks_of_simple 30 30 1 (dualNumerators030 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195716, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 1, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 669214578381, 235435046259, 544901951702, 0, 185534744901, 578464728737, 621279733097, 307371055990, 281282522283, 482716951355]) (branchResiduals030 30 1) 7680628
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck030_31_0 :
    integerResidualCheck 30 31 0 (dualNumerators030 31 0) ∧
    integerMassCheck 30 31 0 (dualNumerators030 31 0) := by
  apply integerChecks_of_simple 30 31 0 (dualNumerators030 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 1032415642124, 2, 592902192609, 0, 1222480453651, 0, 500720887661, 0, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642124, 1, 592902192609, 0, 0, 0, 1600106408231, 776050524992, 77849441973, 698201083019, 711927549445, 860915026216, 655394283556, 0, 905514817789, 694591590443, 655394283556, 0]) (branchResiduals030 31 0) 32891612
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck030_31_1 :
    integerResidualCheck 30 31 1 (dualNumerators030 31 1) ∧
    integerMassCheck 30 31 1 (dualNumerators030 31 1) := by
  apply integerChecks_of_simple 30 31 1 (dualNumerators030 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 741061026801, 808805463926, 18993131489, 744564115640, 327950144489, 1221916346239]) (branchResiduals030 31 1) 32891612
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck030_32_0 :
    integerResidualCheck 30 32 0 (dualNumerators030 32 0) ∧
    integerMassCheck 30 32 0 (dualNumerators030 32 0) := by
  apply integerChecks_of_simple 30 32 0 (dualNumerators030 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 0, 2743468108582, 2028778803022, 0, 505064750776, 2743468108580, 1713354977902, 2, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 2028778803022, 0, 0, 0, 4252009289869, 2655471466972, 364902194330, 2290569272643, 0, 1599482877825, 2144093971220, 98518801469, 262156886566, 3989852403304, 0, 2242612772688]) (branchResiduals030 32 0) 67647473
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck030_32_1 :
    integerResidualCheck 30 32 1 (dualNumerators030 32 1) ∧
    integerMassCheck 30 32 1 (dualNumerators030 32 1) := by
  apply integerChecks_of_simple 30 32 1 (dualNumerators030 32 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 85258653367, 0, 259883317327, 1411663736071, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 0, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 1766557277936, 81171398308, 132139529898, 0, 1823917842058, 23810834186]) (branchResiduals030 32 1) 67647473
    branchSparseDots030 branchIntegerCurvature030 branchDots030
    branchIntegerCurvature030_entry rfl
    (congrFun (congrFun branchResiduals030_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks030 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 30 j s (dualNumerators030 j s) ∧
    integerMassCheck 30 j s (dualNumerators030 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck030_0_0
    · exact integerCheck030_0_1
  · fin_cases s
    · exact integerCheck030_1_0
    · exact integerCheck030_1_1
  · fin_cases s
    · exact integerCheck030_2_0
    · exact integerCheck030_2_1
  · fin_cases s
    · exact integerCheck030_3_0
    · exact integerCheck030_3_1
  · fin_cases s
    · exact integerCheck030_4_0
    · exact integerCheck030_4_1
  · fin_cases s
    · exact integerCheck030_5_0
    · exact integerCheck030_5_1
  · fin_cases s
    · exact integerCheck030_6_0
    · exact integerCheck030_6_1
  · fin_cases s
    · exact integerCheck030_7_0
    · exact integerCheck030_7_1
  · fin_cases s
    · exact integerCheck030_8_0
    · exact integerCheck030_8_1
  · fin_cases s
    · exact integerCheck030_9_0
    · exact integerCheck030_9_1
  · fin_cases s
    · exact integerCheck030_10_0
    · exact integerCheck030_10_1
  · fin_cases s
    · exact integerCheck030_11_0
    · exact integerCheck030_11_1
  · fin_cases s
    · exact integerCheck030_12_0
    · exact integerCheck030_12_1
  · fin_cases s
    · exact integerCheck030_13_0
    · exact integerCheck030_13_1
  · fin_cases s
    · exact integerCheck030_14_0
    · exact integerCheck030_14_1
  · fin_cases s
    · exact integerCheck030_15_0
    · exact integerCheck030_15_1
  · fin_cases s
    · exact integerCheck030_16_0
    · exact integerCheck030_16_1
  · fin_cases s
    · exact integerCheck030_17_0
    · exact integerCheck030_17_1
  · fin_cases s
    · exact integerCheck030_18_0
    · exact integerCheck030_18_1
  · fin_cases s
    · exact integerCheck030_19_0
    · exact integerCheck030_19_1
  · fin_cases s
    · exact integerCheck030_20_0
    · exact integerCheck030_20_1
  · fin_cases s
    · exact integerCheck030_21_0
    · exact integerCheck030_21_1
  · fin_cases s
    · exact integerCheck030_22_0
    · exact integerCheck030_22_1
  · fin_cases s
    · exact integerCheck030_23_0
    · exact integerCheck030_23_1
  · fin_cases s
    · exact integerCheck030_24_0
    · exact integerCheck030_24_1
  · fin_cases s
    · exact integerCheck030_25_0
    · exact integerCheck030_25_1
  · fin_cases s
    · exact integerCheck030_26_0
    · exact integerCheck030_26_1
  · fin_cases s
    · exact integerCheck030_27_0
    · exact integerCheck030_27_1
  · fin_cases s
    · exact integerCheck030_28_0
    · exact integerCheck030_28_1
  · fin_cases s
    · exact integerCheck030_29_0
    · exact integerCheck030_29_1
  · fin_cases s
    · exact integerCheck030_30_0
    · exact integerCheck030_30_1
  · fin_cases s
    · exact integerCheck030_31_0
    · exact integerCheck030_31_1
  · fin_cases s
    · exact integerCheck030_32_0
    · exact integerCheck030_32_1

end ElevenSquare.Tasks.T06
