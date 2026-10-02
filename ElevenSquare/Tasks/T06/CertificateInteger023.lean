import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual023
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
import ElevenSquare.Tasks.T06.SparseColumn35
import ElevenSquare.Tasks.T06.SparseColumn36
import ElevenSquare.Tasks.T06.SparseColumn38
import ElevenSquare.Tasks.T06.SparseColumn39
import ElevenSquare.Tasks.T06.SparseColumn41
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn47
import ElevenSquare.Tasks.T06.SparseColumn49

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix023 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix023_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = branchIntegerMatrix023 := by
  change roundedGradients ∘ branchRows 23 = branchIntegerMatrix023
  rw [show branchRows 23 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 34, 35, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, branchIntegerMatrix023]

theorem branchColumn023_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 0) i) = _
  rw [branchColumn023_0]
  exact sparseColumn00_sum n

theorem branchColumn023_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 1) i) = _
  rw [branchColumn023_1]
  exact sparseColumn01_sum n

theorem branchColumn023_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 2) i) = _
  rw [branchColumn023_2]
  exact sparseColumn02_sum n

theorem branchColumn023_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 3) i) = _
  rw [branchColumn023_3]
  exact sparseColumn03_sum n

theorem branchColumn023_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 4) i) = _
  rw [branchColumn023_4]
  exact sparseColumn04_sum n

theorem branchColumn023_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 5) i) = _
  rw [branchColumn023_5]
  exact sparseColumn05_sum n

theorem branchColumn023_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 6) i) = _
  rw [branchColumn023_6]
  exact sparseColumn06_sum n

theorem branchColumn023_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 7) i) = _
  rw [branchColumn023_7]
  exact sparseColumn07_sum n

theorem branchColumn023_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 8) i) = _
  rw [branchColumn023_8]
  exact sparseColumn08_sum n

theorem branchColumn023_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 9) i) = _
  rw [branchColumn023_9]
  exact sparseColumn09_sum n

theorem branchColumn023_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 10) i) = _
  rw [branchColumn023_10]
  exact sparseColumn10_sum n

theorem branchColumn023_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 11) i) = _
  rw [branchColumn023_11]
  exact sparseColumn11_sum n

theorem branchColumn023_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 12) i) = _
  rw [branchColumn023_12]
  exact sparseColumn35_sum n

theorem branchColumn023_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 13) i) = _
  rw [branchColumn023_13]
  exact sparseColumn36_sum n

theorem branchColumn023_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 14) i) = _
  rw [branchColumn023_14]
  exact sparseColumn41_sum n

theorem branchColumn023_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 15) i) = _
  rw [branchColumn023_15]
  exact sparseColumn38_sum n

theorem branchColumn023_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 16) i) = _
  rw [branchColumn023_16]
  exact sparseColumn39_sum n

theorem branchColumn023_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 17) i) = _
  rw [branchColumn023_17]
  exact sparseColumn17_sum n

theorem branchColumn023_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 18) i) = _
  rw [branchColumn023_18]
  exact sparseColumn18_sum n

theorem branchColumn023_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 19) i) = _
  rw [branchColumn023_19]
  exact sparseColumn19_sum n

theorem branchColumn023_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 20) = sparseColumn20 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 20) = sparseDot20 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 20) i) = _
  rw [branchColumn023_20]
  exact sparseColumn20_sum n

theorem branchColumn023_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 21) i) = _
  rw [branchColumn023_21]
  exact sparseColumn21_sum n

theorem branchColumn023_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 22) i) = _
  rw [branchColumn023_22]
  exact sparseColumn22_sum n

theorem branchColumn023_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 23) = sparseColumn47 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 23) = sparseDot47 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 23) i) = _
  rw [branchColumn023_23]
  exact sparseColumn47_sum n

theorem branchColumn023_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 24) i) = _
  rw [branchColumn023_24]
  exact sparseColumn24_sum n

theorem branchColumn023_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 25) i) = _
  rw [branchColumn023_25]
  exact sparseColumn25_sum n

theorem branchColumn023_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 26) = sparseColumn26 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 26) = sparseDot26 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 26) i) = _
  rw [branchColumn023_26]
  exact sparseColumn26_sum n

theorem branchColumn023_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 27) i) = _
  rw [branchColumn023_27]
  exact sparseColumn27_sum n

theorem branchColumn023_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 28) i) = _
  rw [branchColumn023_28]
  exact sparseColumn28_sum n

theorem branchColumn023_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 29) = sparseColumn49 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 29) = sparseDot49 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 29) i) = _
  rw [branchColumn023_29]
  exact sparseColumn49_sum n

theorem branchColumn023_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 30) i) = _
  rw [branchColumn023_30]
  exact sparseColumn30_sum n

theorem branchColumn023_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 31) i) = _
  rw [branchColumn023_31]
  exact sparseColumn31_sum n

theorem branchColumn023_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 23 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 23 i)) = _
  rw [branchIntegerMatrix023_eq]
  simp only [branchIntegerMatrix023, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot023_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 23 i) 32) i) = _
  rw [branchColumn023_32]
  exact sparseColumn43_sum n

def branchSparseDots023 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot20, sparseDot21, sparseDot22, sparseDot47, sparseDot24, sparseDot25, sparseDot26, sparseDot27, sparseDot28, sparseDot49, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot023_0 :
    branchSparseDots023 0 = sparseDot00 := rfl

private theorem branchSparseDot023_1 :
    branchSparseDots023 1 = sparseDot01 := rfl

private theorem branchSparseDot023_2 :
    branchSparseDots023 2 = sparseDot02 := rfl

private theorem branchSparseDot023_3 :
    branchSparseDots023 3 = sparseDot03 := rfl

private theorem branchSparseDot023_4 :
    branchSparseDots023 4 = sparseDot04 := rfl

private theorem branchSparseDot023_5 :
    branchSparseDots023 5 = sparseDot05 := rfl

private theorem branchSparseDot023_6 :
    branchSparseDots023 6 = sparseDot06 := rfl

private theorem branchSparseDot023_7 :
    branchSparseDots023 7 = sparseDot07 := rfl

private theorem branchSparseDot023_8 :
    branchSparseDots023 8 = sparseDot08 := rfl

private theorem branchSparseDot023_9 :
    branchSparseDots023 9 = sparseDot09 := rfl

private theorem branchSparseDot023_10 :
    branchSparseDots023 10 = sparseDot10 := rfl

private theorem branchSparseDot023_11 :
    branchSparseDots023 11 = sparseDot11 := rfl

private theorem branchSparseDot023_12 :
    branchSparseDots023 12 = sparseDot35 := rfl

private theorem branchSparseDot023_13 :
    branchSparseDots023 13 = sparseDot36 := rfl

private theorem branchSparseDot023_14 :
    branchSparseDots023 14 = sparseDot41 := rfl

private theorem branchSparseDot023_15 :
    branchSparseDots023 15 = sparseDot38 := rfl

private theorem branchSparseDot023_16 :
    branchSparseDots023 16 = sparseDot39 := rfl

private theorem branchSparseDot023_17 :
    branchSparseDots023 17 = sparseDot17 := rfl

private theorem branchSparseDot023_18 :
    branchSparseDots023 18 = sparseDot18 := rfl

private theorem branchSparseDot023_19 :
    branchSparseDots023 19 = sparseDot19 := rfl

private theorem branchSparseDot023_20 :
    branchSparseDots023 20 = sparseDot20 := rfl

private theorem branchSparseDot023_21 :
    branchSparseDots023 21 = sparseDot21 := rfl

private theorem branchSparseDot023_22 :
    branchSparseDots023 22 = sparseDot22 := rfl

private theorem branchSparseDot023_23 :
    branchSparseDots023 23 = sparseDot47 := rfl

private theorem branchSparseDot023_24 :
    branchSparseDots023 24 = sparseDot24 := rfl

private theorem branchSparseDot023_25 :
    branchSparseDots023 25 = sparseDot25 := rfl

private theorem branchSparseDot023_26 :
    branchSparseDots023 26 = sparseDot26 := rfl

private theorem branchSparseDot023_27 :
    branchSparseDots023 27 = sparseDot27 := rfl

private theorem branchSparseDot023_28 :
    branchSparseDots023 28 = sparseDot28 := rfl

private theorem branchSparseDot023_29 :
    branchSparseDots023 29 = sparseDot49 := rfl

private theorem branchSparseDot023_30 :
    branchSparseDots023 30 = sparseDot30 := rfl

private theorem branchSparseDot023_31 :
    branchSparseDots023 31 = sparseDot31 := rfl

private theorem branchSparseDot023_32 :
    branchSparseDots023 32 = sparseDot43 := rfl

theorem branchDots023 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 23 i) k) = branchSparseDots023 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot023_0 n
      _ = _ := congrFun branchSparseDot023_0.symm n
  · calc
      _ = sparseDot01 n := branchDot023_1 n
      _ = _ := congrFun branchSparseDot023_1.symm n
  · calc
      _ = sparseDot02 n := branchDot023_2 n
      _ = _ := congrFun branchSparseDot023_2.symm n
  · calc
      _ = sparseDot03 n := branchDot023_3 n
      _ = _ := congrFun branchSparseDot023_3.symm n
  · calc
      _ = sparseDot04 n := branchDot023_4 n
      _ = _ := congrFun branchSparseDot023_4.symm n
  · calc
      _ = sparseDot05 n := branchDot023_5 n
      _ = _ := congrFun branchSparseDot023_5.symm n
  · calc
      _ = sparseDot06 n := branchDot023_6 n
      _ = _ := congrFun branchSparseDot023_6.symm n
  · calc
      _ = sparseDot07 n := branchDot023_7 n
      _ = _ := congrFun branchSparseDot023_7.symm n
  · calc
      _ = sparseDot08 n := branchDot023_8 n
      _ = _ := congrFun branchSparseDot023_8.symm n
  · calc
      _ = sparseDot09 n := branchDot023_9 n
      _ = _ := congrFun branchSparseDot023_9.symm n
  · calc
      _ = sparseDot10 n := branchDot023_10 n
      _ = _ := congrFun branchSparseDot023_10.symm n
  · calc
      _ = sparseDot11 n := branchDot023_11 n
      _ = _ := congrFun branchSparseDot023_11.symm n
  · calc
      _ = sparseDot35 n := branchDot023_12 n
      _ = _ := congrFun branchSparseDot023_12.symm n
  · calc
      _ = sparseDot36 n := branchDot023_13 n
      _ = _ := congrFun branchSparseDot023_13.symm n
  · calc
      _ = sparseDot41 n := branchDot023_14 n
      _ = _ := congrFun branchSparseDot023_14.symm n
  · calc
      _ = sparseDot38 n := branchDot023_15 n
      _ = _ := congrFun branchSparseDot023_15.symm n
  · calc
      _ = sparseDot39 n := branchDot023_16 n
      _ = _ := congrFun branchSparseDot023_16.symm n
  · calc
      _ = sparseDot17 n := branchDot023_17 n
      _ = _ := congrFun branchSparseDot023_17.symm n
  · calc
      _ = sparseDot18 n := branchDot023_18 n
      _ = _ := congrFun branchSparseDot023_18.symm n
  · calc
      _ = sparseDot19 n := branchDot023_19 n
      _ = _ := congrFun branchSparseDot023_19.symm n
  · calc
      _ = sparseDot20 n := branchDot023_20 n
      _ = _ := congrFun branchSparseDot023_20.symm n
  · calc
      _ = sparseDot21 n := branchDot023_21 n
      _ = _ := congrFun branchSparseDot023_21.symm n
  · calc
      _ = sparseDot22 n := branchDot023_22 n
      _ = _ := congrFun branchSparseDot023_22.symm n
  · calc
      _ = sparseDot47 n := branchDot023_23 n
      _ = _ := congrFun branchSparseDot023_23.symm n
  · calc
      _ = sparseDot24 n := branchDot023_24 n
      _ = _ := congrFun branchSparseDot023_24.symm n
  · calc
      _ = sparseDot25 n := branchDot023_25 n
      _ = _ := congrFun branchSparseDot023_25.symm n
  · calc
      _ = sparseDot26 n := branchDot023_26 n
      _ = _ := congrFun branchSparseDot023_26.symm n
  · calc
      _ = sparseDot27 n := branchDot023_27 n
      _ = _ := congrFun branchSparseDot023_27.symm n
  · calc
      _ = sparseDot28 n := branchDot023_28 n
      _ = _ := congrFun branchSparseDot023_28.symm n
  · calc
      _ = sparseDot49 n := branchDot023_29 n
      _ = _ := congrFun branchSparseDot023_29.symm n
  · calc
      _ = sparseDot30 n := branchDot023_30 n
      _ = _ := congrFun branchSparseDot023_30.symm n
  · calc
      _ = sparseDot31 n := branchDot023_31 n
      _ = _ := congrFun branchSparseDot023_31.symm n
  · calc
      _ = sparseDot43 n := branchDot023_32 n
      _ = _ := congrFun branchSparseDot023_32.symm n

def branchIntegerCurvature023 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101981296, 101981296, 44932602, 44932602, 106371291, 106371291, 48290998, 48290998, 289103692, 289103692]

theorem branchIntegerCurvature023_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 23 i)) = branchIntegerCurvature023 := by
  change curvatureNumerators ∘ branchRows 23 = branchIntegerCurvature023
  rw [show branchRows 23 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 34, 35, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature023_entry (i : Fin 42) :
    curvatureNumerators (branchRows 23 i) = branchIntegerCurvature023 i :=
  congrFun branchIntegerCurvature023_eq i

def branchResiduals023 : Fin 33 → Fin 2 → ℕ := ![![1298358832191850, 33000000000000], ![1547529695615547, 33000000000000], ![1581477104202934, 1336169701694202], ![33000000000000, 1021850142642802], ![857852058590927, 33000000000000], ![1054811092855473, 893734484283997], ![719547090372426, 622101700319854], ![33000000000000, 760393496402263], ![1573860755220955, 1129128913475471], ![1024568102337989, 33000000000000], ![33000000000000, 776809554931532], ![510296708326570, 466533010970020], ![989166414903487, 66000000000000], ![33000000000000, 860590381159182], ![1054771355059073, 485774701264587], ![475834814781294, 33000000000000], ![66000000000000, 743298551726107], ![659158273403361, 460854703064482], ![621647906664315, 260546318464641], ![624991160999686, 508980010832119], ![1358640162907542, 950532272207649], ![753830467458193, 389929718199708], ![465236954635985, 96988275581957], ![1358640162907542, 950532272207649], ![669000005539485, 230003409392788], ![500485136134307, 221360137673294], ![396136216194598, 852454589586214], ![407212648413384, 545871445383728], ![283466941102630, 310389248400057], ![396136216194598, 950532272207649], ![96988275581957, 550593448214882], ![966784501534449, 648577798406985], ![2022565257300386, 950532272207649]]

theorem branchResiduals023_eq : residualNumerators 23 = branchResiduals023 := rfl

theorem integerCheck023_0_0 :
    integerResidualCheck 23 0 0 (dualNumerators023 0 0) ∧
    integerMassCheck 23 0 0 (dualNumerators023 0 0) := by
  apply integerChecks_of_simple 23 0 0 (dualNumerators023 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 298609637458, 1874436686609, 0, 1308901425339, 1754571864380, 80620681505, 1741178091979, 225835502005, 818327875519, 1016864670366]) (branchResiduals023 0 0) 18767167
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck023_0_1 :
    integerResidualCheck 23 0 1 (dualNumerators023 0 1) ∧
    integerMassCheck 23 0 1 (dualNumerators023 0 1) := by
  apply integerChecks_of_simple 23 0 1 (dualNumerators023 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals023 0 1) 18767167
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck023_1_0 :
    integerResidualCheck 23 1 0 (dualNumerators023 1 0) ∧
    integerMassCheck 23 1 0 (dualNumerators023 1 0) := by
  apply integerChecks_of_simple 23 1 0 (dualNumerators023 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 353582830567, 2219515200554, 0, 1549866490727, 2077583602197, 95462721871, 2061724074025, 267411181773, 968979732271, 1204066591796]) (branchResiduals023 1 0) 22176635
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck023_1_1 :
    integerResidualCheck 23 1 1 (dualNumerators023 1 1) ∧
    integerMassCheck 23 1 1 (dualNumerators023 1 1) := by
  apply integerChecks_of_simple 23 1 1 (dualNumerators023 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals023 1 1) 22176635
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck023_2_0 :
    integerResidualCheck 23 2 0 (dualNumerators023 2 0) ∧
    integerMassCheck 23 2 0 (dualNumerators023 2 0) := by
  apply integerChecks_of_simple 23 2 0 (dualNumerators023 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 353582830567, 2219515200555, 0, 1549866490728, 2077583602198, 95462721871, 2061724074027, 267411181773, 968979732272, 1204066591797]) (branchResiduals023 2 0) 22681452
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck023_2_1 :
    integerResidualCheck 23 2 1 (dualNumerators023 2 1) ∧
    integerMassCheck 23 2 1 (dualNumerators023 2 1) := by
  apply integerChecks_of_simple 23 2 1 (dualNumerators023 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 298609637458, 1874436686608, 0, 1308901425338, 1754571864379, 80620681504, 1741178091978, 225835502005, 818327875518, 1016864670365]) (branchResiduals023 2 1) 22681452
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck023_3_0 :
    integerResidualCheck 23 3 0 (dualNumerators023 3 0) ∧
    integerMassCheck 23 3 0 (dualNumerators023 3 0) := by
  apply integerChecks_of_simple 23 3 0 (dualNumerators023 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals023 3 0) 16360330
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck023_3_1 :
    integerResidualCheck 23 3 1 (dualNumerators023 3 1) ∧
    integerMassCheck 23 3 1 (dualNumerators023 3 1) := by
  apply integerChecks_of_simple 23 3 1 (dualNumerators023 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000000, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 235283107509, 1476922487191, 0, 1031321016287, 1382477552007, 63523349867, 1371924214149, 177942276579, 644784030255, 801216871619]) (branchResiduals023 3 1) 16360330
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck023_4_0 :
    integerResidualCheck 23 4 0 (dualNumerators023 4 0) ∧
    integerMassCheck 23 4 0 (dualNumerators023 4 0) := by
  apply integerChecks_of_simple 23 4 0 (dualNumerators023 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000001, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 198702531230, 1247298370644, 0, 870976665588, 1167537235722, 53647074558, 1158624675158, 150276750182, 544536410901, 676647899379]) (branchResiduals023 4 0) 13760362
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck023_4_1 :
    integerResidualCheck 23 4 1 (dualNumerators023 4 1) ∧
    integerMassCheck 23 4 1 (dualNumerators023 4 1) := by
  apply integerChecks_of_simple 23 4 1 (dualNumerators023 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals023 4 1) 13760362
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck023_5_0 :
    integerResidualCheck 23 5 0 (dualNumerators023 5 0) ∧
    integerMassCheck 23 5 0 (dualNumerators023 5 0) := by
  apply integerChecks_of_simple 23 5 0 (dualNumerators023 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 235283107509, 1476922487193, 0, 1031321016288, 1382477552008, 63523349867, 1371924214150, 177942276579, 644784030255, 801216871620]) (branchResiduals023 5 0) 17641130
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck023_5_1 :
    integerResidualCheck 23 5 1 (dualNumerators023 5 1) ∧
    integerMassCheck 23 5 1 (dualNumerators023 5 1) := by
  apply integerChecks_of_simple 23 5 1 (dualNumerators023 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 198702531230, 1247298370643, 0, 870976665588, 1167537235721, 53647074558, 1158624675157, 150276750182, 544536410901, 676647899378]) (branchResiduals023 5 1) 17641130
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck023_6_0 :
    integerResidualCheck 23 6 0 (dualNumerators023 6 0) ∧
    integerMassCheck 23 6 0 (dualNumerators023 6 0) := by
  apply integerChecks_of_simple 23 6 0 (dualNumerators023 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 877488274356, 957704271528, 103906894360, 5439901403, 818327875519, 1016864670366]) (branchResiduals023 6 0) 8962451
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck023_6_1 :
    integerResidualCheck 23 6 1 (dualNumerators023 6 1) ∧
    integerMassCheck 23 6 1 (dualNumerators023 6 1) := by
  apply integerChecks_of_simple 23 6 1 (dualNumerators023 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 760187607595, 1097479190627, 0, 0]) (branchResiduals023 6 1) 8962451
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck023_7_0 :
    integerResidualCheck 23 7 0 (dualNumerators023 7 0) ∧
    integerMassCheck 23 7 0 (dualNumerators023 7 0) := by
  apply integerChecks_of_simple 23 7 0 (dualNumerators023 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals023 7 0) 10424794
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck023_7_1 :
    integerResidualCheck 23 7 1 (dualNumerators023 7 1) ∧
    integerMassCheck 23 7 1 (dualNumerators023 7 1) := by
  apply integerChecks_of_simple 23 7 1 (dualNumerators023 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 176791415284, 1109757600279, 0, 774933245365, 1038791801100, 47731360936, 1030862037014, 133705590887, 484489866137, 602033295899]) (branchResiduals023 7 1) 10424794
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck023_8_0 :
    integerResidualCheck 23 8 0 (dualNumerators023 8 0) ∧
    integerMassCheck 23 8 0 (dualNumerators023 8 0) := by
  apply integerChecks_of_simple 23 8 0 (dualNumerators023 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 353582830567, 2219515200557, 0, 1549866490730, 2077583602200, 95462721871, 2061724074028, 267411181773, 968979732273, 1204066591798]) (branchResiduals023 8 0) 22681452
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck023_8_1 :
    integerResidualCheck 23 8 1 (dualNumerators023 8 1) ∧
    integerMassCheck 23 8 1 (dualNumerators023 8 1) := by
  apply integerChecks_of_simple 23 8 1 (dualNumerators023 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 252183386393, 1583009159490, 0, 1105400337063, 1481780287453, 68086203273, 1470468908124, 190723789588, 691098574663, 858767916063]) (branchResiduals023 8 1) 22681452
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck023_9_0 :
    integerResidualCheck 23 9 0 (dualNumerators023 9 0) ∧
    integerMassCheck 23 9 0 (dualNumerators023 9 0) := by
  apply integerChecks_of_simple 23 9 0 (dualNumerators023 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 235283107509, 1476922487191, 0, 1031321016287, 1382477552007, 63523349867, 1371924214149, 177942276579, 644784030255, 801216871619]) (branchResiduals023 9 0) 16350530
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck023_9_1 :
    integerResidualCheck 23 9 1 (dualNumerators023 9 1) ∧
    integerMassCheck 23 9 1 (dualNumerators023 9 1) := by
  apply integerChecks_of_simple 23 9 1 (dualNumerators023 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals023 9 1) 16350530
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck023_10_0 :
    integerResidualCheck 23 10 0 (dualNumerators023 10 0) ∧
    integerMassCheck 23 10 0 (dualNumerators023 10 0) := by
  apply integerChecks_of_simple 23 10 0 (dualNumerators023 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals023 10 0) 10683139
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck023_10_1 :
    integerResidualCheck 23 10 1 (dualNumerators023 10 1) ∧
    integerMassCheck 23 10 1 (dualNumerators023 10 1) := by
  apply integerChecks_of_simple 23 10 1 (dualNumerators023 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 179862976578, 1129038448761, 0, 788396879662, 1056839694908, 48560642157, 1048772159673, 136028582177, 492907358117, 612492978948]) (branchResiduals023 10 1) 10683139
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck023_11_0 :
    integerResidualCheck 23 11 0 (dualNumerators023 11 0) ∧
    integerMassCheck 23 11 0 (dualNumerators023 11 0) := by
  apply integerChecks_of_simple 23 11 0 (dualNumerators023 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 111787046581, 701711247439, 0, 489998333105, 656838836154, 30181034864, 651824764029, 84543432681, 306347970271, 380671900746]) (branchResiduals023 11 0) 15120968
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck023_11_1 :
    integerResidualCheck 23 11 1 (dualNumerators023 11 1) ∧
    integerMassCheck 23 11 1 (dualNumerators023 11 1) := by
  apply integerChecks_of_simple 23 11 1 (dualNumerators023 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 101936936604, 639879996233, 0, 446822154676, 598961515206, 27521634498, 594389257794, 77093892371, 279354134309, 347129015395]) (branchResiduals023 11 1) 15120968
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck023_12_0 :
    integerResidualCheck 23 12 0 (dualNumerators023 12 0) ∧
    integerMassCheck 23 12 0 (dualNumerators023 12 0) := by
  apply integerChecks_of_simple 23 12 0 (dualNumerators023 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 235283107509, 1476922487191, 0, 1031321016287, 1382477552007, 63523349867, 1371924214149, 177942276579, 644784030255, 801216871619]) (branchResiduals023 12 0) 16348076
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck023_12_1 :
    integerResidualCheck 23 12 1 (dualNumerators023 12 1) ∧
    integerMassCheck 23 12 1 (dualNumerators023 12 1) := by
  apply integerChecks_of_simple 23 12 1 (dualNumerators023 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals023 12 1) 16348076
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck023_13_0 :
    integerResidualCheck 23 13 0 (dualNumerators023 13 0) ∧
    integerMassCheck 23 13 0 (dualNumerators023 13 0) := by
  apply integerChecks_of_simple 23 13 0 (dualNumerators023 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals023 13 0) 13962901
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck023_13_1 :
    integerResidualCheck 23 13 1 (dualNumerators023 13 1) ∧
    integerMassCheck 23 13 1 (dualNumerators023 13 1) := by
  apply integerChecks_of_simple 23 13 1 (dualNumerators023 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 198702531230, 1247298370644, 0, 870976665588, 1167537235722, 53647074558, 1158624675158, 150276750182, 544536410901, 676647899379]) (branchResiduals023 13 1) 13962901
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck023_14_0 :
    integerResidualCheck 23 14 0 (dualNumerators023 14 0) ∧
    integerMassCheck 23 14 0 (dualNumerators023 14 0) := by
  apply integerChecks_of_simple 23 14 0 (dualNumerators023 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 235283107509, 1476922487193, 0, 1031321016288, 1382477552008, 63523349867, 1371924214150, 177942276579, 644784030255, 801216871620]) (branchResiduals023 14 0) 20161291
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck023_14_1 :
    integerResidualCheck 23 14 1 (dualNumerators023 14 1) ∧
    integerMassCheck 23 14 1 (dualNumerators023 14 1) := by
  apply integerChecks_of_simple 23 14 1 (dualNumerators023 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 107725567034, 676216469947, 0, 472195570901, 632974376182, 29084488712, 628142476787, 81471776052, 295217646558, 366841218336]) (branchResiduals023 14 1) 20161291
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck023_15_0 :
    integerResidualCheck 23 15 0 (dualNumerators023 15 0) ∧
    integerMassCheck 23 15 0 (dualNumerators023 15 0) := by
  apply integerChecks_of_simple 23 15 0 (dualNumerators023 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 111787046581, 701711247439, 0, 489998333105, 656838836153, 30181034864, 651824764029, 84543432681, 306347970271, 380671900746]) (branchResiduals023 15 0) 12900283
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck023_15_1 :
    integerResidualCheck 23 15 1 (dualNumerators023 15 1) ∧
    integerMassCheck 23 15 1 (dualNumerators023 15 1) := by
  apply integerChecks_of_simple 23 15 1 (dualNumerators023 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals023 15 1) 12900283
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck023_16_0 :
    integerResidualCheck 23 16 0 (dualNumerators023 16 0) ∧
    integerMassCheck 23 16 0 (dualNumerators023 16 0) := by
  apply integerChecks_of_simple 23 16 0 (dualNumerators023 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals023 16 0) 10683060
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck023_16_1 :
    integerResidualCheck 23 16 1 (dualNumerators023 16 1) ∧
    integerMassCheck 23 16 1 (dualNumerators023 16 1) := by
  apply integerChecks_of_simple 23 16 1 (dualNumerators023 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 179862976578, 1129038448761, 0, 788396879662, 1056839694908, 48560642157, 1048772159673, 136028582177, 492907358117, 612492978948]) (branchResiduals023 16 1) 10683060
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck023_17_0 :
    integerResidualCheck 23 17 0 (dualNumerators023 17 0) ∧
    integerMassCheck 23 17 0 (dualNumerators023 17 0) := by
  apply integerChecks_of_simple 23 17 0 (dualNumerators023 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 146617228716, 920347764841, 0, 642670147151, 861494178583, 39584726736, 854917840966, 110885153378, 401798703857, 499280201462]) (branchResiduals023 17 0) 15120968
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck023_17_1 :
    integerResidualCheck 23 17 1 (dualNumerators023 17 1) ∧
    integerMassCheck 23 17 1 (dualNumerators023 17 1) := by
  apply integerChecks_of_simple 23 17 1 (dualNumerators023 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 101936936604, 639879996232, 0, 446822154676, 598961515206, 27521634498, 594389257794, 77093892370, 279354134309, 347129015395]) (branchResiduals023 17 1) 15120968
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck023_18_0 :
    integerResidualCheck 23 18 0 (dualNumerators023 18 0) ∧
    integerMassCheck 23 18 0 (dualNumerators023 18 0) := by
  apply integerChecks_of_simple 23 18 0 (dualNumerators023 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 261721072458, 1006675626970, 0, 763999473637, 936711106099, 134481966149, 862769256399, 123780303264, 477654049462, 593539022787]) (branchResiduals023 18 0) 13565580
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck023_18_1 :
    integerResidualCheck 23 18 1 (dualNumerators023 18 1) ∧
    integerMassCheck 23 18 1 (dualNumerators023 18 1) := by
  apply integerChecks_of_simple 23 18 1 (dualNumerators023 18 1)
    (![546080038515, 100531796850, 546080038516, 0, 1, 184109219884, 218003208651, 0, 74499415779, 53134692444, 184109219884, 0, 92880591654, 504519352652, 218003208651, 0, 0, 504519352652, 178954014012, 151131188017, 846351152950, 285344710532, 82351679314, 97512391500, 184109219884, 0, 92880591654, 504519352652, 0, 0, 285344710532, 781937638598, 13715132590, 123005639922, 82351679314, 0, 115464148095, 0, 180745426040, 104599284492, 51486440059, 63977708037]) (branchResiduals023 18 1) 13565580
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck023_19_0 :
    integerResidualCheck 23 19 0 (dualNumerators023 19 0) ∧
    integerMassCheck 23 19 0 (dualNumerators023 19 0) := by
  apply integerChecks_of_simple 23 19 0 (dualNumerators023 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 307298608851, 763894463397, 0, 645216866088, 704807657121, 199841967519, 577111910116, 96603051948, 403390917798, 501258706842]) (branchResiduals023 19 0) 8248658
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck023_19_1 :
    integerResidualCheck 23 19 1 (dualNumerators023 19 1) ∧
    integerMassCheck 23 19 1 (dualNumerators023 19 1) := by
  apply integerChecks_of_simple 23 19 1 (dualNumerators023 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 76640541789, 687358931849, 131755764247, 328427706730, 645216866088, 0, 761601233763, 225876501886, 287707656866, 357509209222]) (branchResiduals023 19 1) 8248658
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck023_20_0 :
    integerResidualCheck 23 20 0 (dualNumerators023 20 0) ∧
    integerMassCheck 23 20 0 (dualNumerators023 20 0) := by
  apply integerChecks_of_simple 23 20 0 (dualNumerators023 20 0)
    (![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 2105933038876, 0, 185761786321, 1009041980816, 2493629379175, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038876, 0, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 156880523801, 1406999830004, 941979561817, 0, 1320736486917, 0, 2067456287976, 1196458760692, 588927568327, 731808918591]) (branchResiduals023 20 0) 35312013
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck023_20_1 :
    integerResidualCheck 23 20 1 (dualNumerators023 20 1) ∧
    integerMassCheck 23 20 1 (dualNumerators023 20 1) := by
  apply integerChecks_of_simple 23 20 1 (dualNumerators023 20 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 1301213128929, 890779360508, 0, 1320313360088, 769869471398, 1081323590019, 0, 135852760286, 825462640703, 1025730420714]) (branchResiduals023 20 1) 35312013
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck023_21_0 :
    integerResidualCheck 23 21 0 (dualNumerators023 21 0) ∧
    integerMassCheck 23 21 0 (dualNumerators023 21 0) := by
  apply integerChecks_of_simple 23 21 0 (dualNumerators023 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 759767979803, 549133445537, 851509250277, 798941670661, 583650214286, 725251211053]) (branchResiduals023 21 0) 11182451
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck023_21_1 :
    integerResidualCheck 23 21 1 (dualNumerators023 21 1) ∧
    integerMassCheck 23 21 1 (dualNumerators023 21 1) := by
  apply integerChecks_of_simple 23 21 1 (dualNumerators023 21 1)
    (![114087637157, 21003212630, 114087637157, 0, 1, 11738971135, 13900082653, 0, 159960694697, 114087637156, 11738971135, 0, 218966847953, 1189409008000, 13900082653, 0, 0, 1189409008001, 1568336550649, 324499857786, 176820605835, 18193837997, 176820605835, 209372781287, 11738971135, 0, 218966847953, 1189409008000, 0, 0, 18193837997, 1843425165269, 878870811393, 964554353877, 0, 176820605835, 103103392317, 144814328227, 0, 18193837997, 110548608107, 137369112437]) (branchResiduals023 21 1) 11182451
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck023_22_0 :
    integerResidualCheck 23 22 0 (dualNumerators023 22 0) ∧
    integerMassCheck 23 22 0 (dualNumerators023 22 0) := by
  apply integerChecks_of_simple 23 22 0 (dualNumerators023 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 565168626292, 198830847345, 460183470977, 0, 216080085359, 429136780729, 256292246333, 545043834385, 287707656866, 357509209222]) (branchResiduals023 22 0) 6465674
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck023_22_1 :
    integerResidualCheck 23 22 1 (dualNumerators023 22 1) ∧
    integerMassCheck 23 22 1 (dualNumerators023 22 1) := by
  apply integerChecks_of_simple 23 22 1 (dualNumerators023 22 1)
    (![50594765625, 9314353833, 50594765625, 0, 0, 5205914576, 6164308785, 0, 70938219592, 50594765625, 5205914576, 0, 15463748427, 83997745994, 6164308785, 0, 0, 83997745994, 1170399714012, 143906865451, 78415131848, 8068472555, 78415131848, 92851136735, 5205914576, 0, 15463748427, 83997745994, 0, 0, 8068472555, 130185291813, 17889440442, 112295851372, 0, 78415131848, 45723551643, 64221217814, 0, 8068472555, 49025302449, 60919467008]) (branchResiduals023 22 1) 6465674
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck023_23_0 :
    integerResidualCheck 23 23 0 (dualNumerators023 23 0) ∧
    integerMassCheck 23 23 0 (dualNumerators023 23 0) := by
  apply integerChecks_of_simple 23 23 0 (dualNumerators023 23 0)
    (![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 2105933038876, 0, 185761786321, 1009041980816, 2493629379175, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038876, 0, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 1156880523801, 406999830004, 941979561817, 0, 1320736486917, 0, 2067456287976, 1196458760692, 588927568327, 731808918591]) (branchResiduals023 23 0) 35297932
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck023_23_1 :
    integerResidualCheck 23 23 1 (dualNumerators023 23 1) ∧
    integerMassCheck 23 23 1 (dualNumerators023 23 1) := by
  apply integerChecks_of_simple 23 23 1 (dualNumerators023 23 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 301213128929, 1890779360508, 0, 1320313360088, 769869471398, 1081323590019, 0, 135852760286, 825462640703, 1025730420714]) (branchResiduals023 23 1) 35297932
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck023_24_0 :
    integerResidualCheck 23 24 0 (dualNumerators023 24 0) ∧
    integerMassCheck 23 24 0 (dualNumerators023 24 0) := by
  apply integerChecks_of_simple 23 24 0 (dualNumerators023 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 512185690040, 559007382209, 569308312247, 737522866658, 477654049462, 593539022787]) (branchResiduals023 24 0) 9356857
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck023_24_1 :
    integerResidualCheck 23 24 1 (dualNumerators023 24 1) ∧
    integerMassCheck 23 24 1 (dualNumerators023 24 1) := by
  apply integerChecks_of_simple 23 24 1 (dualNumerators023 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 587483804282, 282115266095, 66021086067, 82038644814, 0, 0, 66021086067, 82038644814]) (branchResiduals023 24 1) 9356857
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck023_25_0 :
    integerResidualCheck 23 25 0 (dualNumerators023 25 0) ∧
    integerMassCheck 23 25 0 (dualNumerators023 25 0) := by
  apply integerChecks_of_simple 23 25 0 (dualNumerators023 25 0)
    (![30936264063, 5695279071, 30936264063, 0, 1, 16941043971, 20059842445, 0, 627070502755, 447241068346, 509886390043, 0, 136694444206, 742512415929, 603755038162, 0, 0, 742512415929, 1506277362888, 1272089305134, 47947079019, 26256356369, 693163945107, 820773474842, 509886390043, 0, 136694444206, 742512415929, 0, 0, 790255830005, 1150795112397, 638438115729, 512356996669, 47947079019, 0, 448879356988, 522996202554, 26256356369, 0, 433367530667, 538508028875]) (branchResiduals023 25 0) 8671199
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck023_25_1 :
    integerResidualCheck 23 25 1 (dualNumerators023 25 1) ∧
    integerMassCheck 23 25 1 (dualNumerators023 25 1) := by
  apply integerChecks_of_simple 23 25 1 (dualNumerators023 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 415529968297, 599898615461, 0, 0]) (branchResiduals023 25 1) 8671199
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck023_26_0 :
    integerResidualCheck 23 26 0 (dualNumerators023 26 0) ∧
    integerMassCheck 23 26 0 (dualNumerators023 26 0) := by
  apply integerChecks_of_simple 23 26 0 (dualNumerators023 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0]) (branchResiduals023 26 0) 15099566
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck023_26_1 :
    integerResidualCheck 23 26 1 (dualNumerators023 26 1) ∧
    integerMassCheck 23 26 1 (dualNumerators023 26 1) := by
  apply integerChecks_of_simple 23 26 1 (dualNumerators023 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 879744679617, 350168760452, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals023 26 1) 15099566
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck023_27_0 :
    integerResidualCheck 23 27 0 (dualNumerators023 27 0) ∧
    integerMassCheck 23 27 0 (dualNumerators023 27 0) := by
  apply integerChecks_of_simple 23 27 0 (dualNumerators023 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 286173900105, 455299762271, 340673826058, 423325647580]) (branchResiduals023 27 0) 7338775
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck023_27_1 :
    integerResidualCheck 23 27 1 (dualNumerators023 27 1) ∧
    integerMassCheck 23 27 1 (dualNumerators023 27 1) := by
  apply integerChecks_of_simple 23 27 1 (dualNumerators023 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 575645700633, 956292240576, 0, 377837583379, 871790834897, 421969477217, 576174693322, 69042172766, 236224837801, 293536000677]) (branchResiduals023 27 1) 7338775
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck023_28_0 :
    integerResidualCheck 23 28 0 (dualNumerators023 28 0) ∧
    integerMassCheck 23 28 0 (dualNumerators023 28 0) := by
  apply integerChecks_of_simple 23 28 0 (dualNumerators023 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 450383711774, 395438493575, 287707656866, 357509209222]) (branchResiduals023 28 0) 10335557
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck023_28_1 :
    integerResidualCheck 23 28 1 (dualNumerators023 28 1) ∧
    integerMassCheck 23 28 1 (dualNumerators023 28 1) := by
  apply integerChecks_of_simple 23 28 1 (dualNumerators023 28 1)
    (![71098470185, 13089028086, 71098470186, 0, 1, 500260975618, 592357612055, 0, 99686179557, 71098470185, 7315629546, 0, 112480335850, 610983470480, 8662416338, 0, 0, 610983470481, 1239454790169, 202225622679, 110193136482, 775337722729, 110193136482, 130479382508, 7315629546, 0, 112480335850, 610983470480, 0, 0, 11338249092, 946942807286, 438489340489, 508453466798, 0, 110193136482, 456220281523, 343496853848, 0, 11338249092, 68892976605, 85607292678]) (branchResiduals023 28 1) 10335557
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck023_29_0 :
    integerResidualCheck 23 29 0 (dualNumerators023 29 0) ∧
    integerMassCheck 23 29 0 (dualNumerators023 29 0) := by
  apply integerChecks_of_simple 23 29 0 (dualNumerators023 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0]) (branchResiduals023 29 0) 40352153
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck023_29_1 :
    integerResidualCheck 23 29 1 (dualNumerators023 29 1) ∧
    integerMassCheck 23 29 1 (dualNumerators023 29 1) := by
  apply integerChecks_of_simple 23 29 1 (dualNumerators023 29 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 301213128929, 1890779360508, 0, 1320313360088, 1769869471398, 81323590019, 0, 135852760286, 825462640703, 1025730420714]) (branchResiduals023 29 1) 40352153
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck023_30_0 :
    integerResidualCheck 23 30 0 (dualNumerators023 30 0) ∧
    integerMassCheck 23 30 0 (dualNumerators023 30 0) := by
  apply integerChecks_of_simple 23 30 0 (dualNumerators023 30 0)
    (![50594765625, 9314353833, 50594765625, 0, 0, 5205914576, 6164308785, 0, 70938219592, 50594765625, 5205914576, 0, 15463748427, 83997745994, 6164308785, 0, 0, 83997745994, 170399714012, 1143906865451, 78415131848, 8068472555, 78415131848, 92851136735, 5205914576, 0, 15463748427, 83997745994, 0, 0, 8068472555, 130185291813, 17889440442, 112295851372, 0, 78415131848, 105114855418, 4829914039, 0, 8068472555, 108416606224, 1528163233]) (branchResiduals023 30 0) 7680628
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck023_30_1 :
    integerResidualCheck 23 30 1 (dualNumerators023 30 1) ∧
    integerMassCheck 23 30 1 (dualNumerators023 30 1) := by
  apply integerChecks_of_simple 23 30 1 (dualNumerators023 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 124312626679, 780336997961, 0, 544901951702, 730436696602, 33562777035, 829173251111, 99477537975, 281282522283, 482716951355]) (branchResiduals023 30 1) 7680628
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck023_31_0 :
    integerResidualCheck 23 31 0 (dualNumerators023 31 0) ∧
    integerMassCheck 23 31 0 (dualNumerators023 31 0) := by
  apply integerChecks_of_simple 23 31 0 (dualNumerators023 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 1032415642125, 1, 592902192609, 0, 1222480453651, 0, 500720887661, 0, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642125, 0, 592902192609, 0, 0, 0, 1600106408231, 776050524992, 77849441973, 698201083019, 711927549445, 860915026216, 655394283556, 0, 654789687546, 945316720686, 655394283556, 0]) (branchResiduals023 31 0) 32891612
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck023_31_1 :
    integerResidualCheck 23 31 1 (dualNumerators023 31 1) ∧
    integerMassCheck 23 31 1 (dualNumerators023 31 1) := by
  apply integerChecks_of_simple 23 31 1 (dualNumerators023 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 741061026801, 808805463926, 725570984152, 37986262977, 327950144489, 1221916346239]) (branchResiduals023 31 1) 32891612
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck023_32_0 :
    integerResidualCheck 23 32 0 (dualNumerators023 32 0) ∧
    integerMassCheck 23 32 0 (dualNumerators023 32 0) := by
  apply integerChecks_of_simple 23 32 0 (dualNumerators023 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 0, 2743468108582, 2028778803022, 0, 505064750776, 2743468108580, 1713354977902, 2, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 2028778803022, 0, 0, 0, 4252009289869, 2655471466972, 364902194330, 2290569272643, 0, 1599482877825, 2144093971220, 98518801469, 3884085649292, 367923640577, 0, 2242612772688]) (branchResiduals023 32 0) 67647473
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck023_32_1 :
    integerResidualCheck 23 32 1 (dualNumerators023 32 1) ∧
    integerMassCheck 23 32 1 (dualNumerators023 32 1) := by
  apply integerChecks_of_simple 23 32 1 (dualNumerators023 32 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 301213128929, 1890779360508, 0, 1320313360088, 1769869471398, 81323590019, 0, 135852760286, 1825462640703, 25730420714]) (branchResiduals023 32 1) 67647473
    branchSparseDots023 branchIntegerCurvature023 branchDots023
    branchIntegerCurvature023_entry rfl
    (congrFun (congrFun branchResiduals023_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks023 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 23 j s (dualNumerators023 j s) ∧
    integerMassCheck 23 j s (dualNumerators023 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck023_0_0
    · exact integerCheck023_0_1
  · fin_cases s
    · exact integerCheck023_1_0
    · exact integerCheck023_1_1
  · fin_cases s
    · exact integerCheck023_2_0
    · exact integerCheck023_2_1
  · fin_cases s
    · exact integerCheck023_3_0
    · exact integerCheck023_3_1
  · fin_cases s
    · exact integerCheck023_4_0
    · exact integerCheck023_4_1
  · fin_cases s
    · exact integerCheck023_5_0
    · exact integerCheck023_5_1
  · fin_cases s
    · exact integerCheck023_6_0
    · exact integerCheck023_6_1
  · fin_cases s
    · exact integerCheck023_7_0
    · exact integerCheck023_7_1
  · fin_cases s
    · exact integerCheck023_8_0
    · exact integerCheck023_8_1
  · fin_cases s
    · exact integerCheck023_9_0
    · exact integerCheck023_9_1
  · fin_cases s
    · exact integerCheck023_10_0
    · exact integerCheck023_10_1
  · fin_cases s
    · exact integerCheck023_11_0
    · exact integerCheck023_11_1
  · fin_cases s
    · exact integerCheck023_12_0
    · exact integerCheck023_12_1
  · fin_cases s
    · exact integerCheck023_13_0
    · exact integerCheck023_13_1
  · fin_cases s
    · exact integerCheck023_14_0
    · exact integerCheck023_14_1
  · fin_cases s
    · exact integerCheck023_15_0
    · exact integerCheck023_15_1
  · fin_cases s
    · exact integerCheck023_16_0
    · exact integerCheck023_16_1
  · fin_cases s
    · exact integerCheck023_17_0
    · exact integerCheck023_17_1
  · fin_cases s
    · exact integerCheck023_18_0
    · exact integerCheck023_18_1
  · fin_cases s
    · exact integerCheck023_19_0
    · exact integerCheck023_19_1
  · fin_cases s
    · exact integerCheck023_20_0
    · exact integerCheck023_20_1
  · fin_cases s
    · exact integerCheck023_21_0
    · exact integerCheck023_21_1
  · fin_cases s
    · exact integerCheck023_22_0
    · exact integerCheck023_22_1
  · fin_cases s
    · exact integerCheck023_23_0
    · exact integerCheck023_23_1
  · fin_cases s
    · exact integerCheck023_24_0
    · exact integerCheck023_24_1
  · fin_cases s
    · exact integerCheck023_25_0
    · exact integerCheck023_25_1
  · fin_cases s
    · exact integerCheck023_26_0
    · exact integerCheck023_26_1
  · fin_cases s
    · exact integerCheck023_27_0
    · exact integerCheck023_27_1
  · fin_cases s
    · exact integerCheck023_28_0
    · exact integerCheck023_28_1
  · fin_cases s
    · exact integerCheck023_29_0
    · exact integerCheck023_29_1
  · fin_cases s
    · exact integerCheck023_30_0
    · exact integerCheck023_30_1
  · fin_cases s
    · exact integerCheck023_31_0
    · exact integerCheck023_31_1
  · fin_cases s
    · exact integerCheck023_32_0
    · exact integerCheck023_32_1

end ElevenSquare.Tasks.T06
