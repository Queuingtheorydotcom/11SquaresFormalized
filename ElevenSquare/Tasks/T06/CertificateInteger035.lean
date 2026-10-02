import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual035
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
import ElevenSquare.Tasks.T06.SparseColumn29
import ElevenSquare.Tasks.T06.SparseColumn30
import ElevenSquare.Tasks.T06.SparseColumn31
import ElevenSquare.Tasks.T06.SparseColumn32
import ElevenSquare.Tasks.T06.SparseColumn35
import ElevenSquare.Tasks.T06.SparseColumn36
import ElevenSquare.Tasks.T06.SparseColumn38
import ElevenSquare.Tasks.T06.SparseColumn39
import ElevenSquare.Tasks.T06.SparseColumn41
import ElevenSquare.Tasks.T06.SparseColumn52
import ElevenSquare.Tasks.T06.SparseColumn53

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix035 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix035_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = branchIntegerMatrix035 := by
  change roundedGradients ∘ branchRows 35 = branchIntegerMatrix035
  rw [show branchRows 35 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 34, 35, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, branchIntegerMatrix035]

theorem branchColumn035_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 0) i) = _
  rw [branchColumn035_0]
  exact sparseColumn00_sum n

theorem branchColumn035_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 1) i) = _
  rw [branchColumn035_1]
  exact sparseColumn01_sum n

theorem branchColumn035_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 2) i) = _
  rw [branchColumn035_2]
  exact sparseColumn02_sum n

theorem branchColumn035_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 3) i) = _
  rw [branchColumn035_3]
  exact sparseColumn03_sum n

theorem branchColumn035_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 4) i) = _
  rw [branchColumn035_4]
  exact sparseColumn04_sum n

theorem branchColumn035_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 5) i) = _
  rw [branchColumn035_5]
  exact sparseColumn05_sum n

theorem branchColumn035_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 6) i) = _
  rw [branchColumn035_6]
  exact sparseColumn06_sum n

theorem branchColumn035_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 7) i) = _
  rw [branchColumn035_7]
  exact sparseColumn07_sum n

theorem branchColumn035_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 8) i) = _
  rw [branchColumn035_8]
  exact sparseColumn08_sum n

theorem branchColumn035_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 9) i) = _
  rw [branchColumn035_9]
  exact sparseColumn09_sum n

theorem branchColumn035_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 10) i) = _
  rw [branchColumn035_10]
  exact sparseColumn10_sum n

theorem branchColumn035_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 11) i) = _
  rw [branchColumn035_11]
  exact sparseColumn11_sum n

theorem branchColumn035_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 12) i) = _
  rw [branchColumn035_12]
  exact sparseColumn35_sum n

theorem branchColumn035_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 13) i) = _
  rw [branchColumn035_13]
  exact sparseColumn36_sum n

theorem branchColumn035_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 14) i) = _
  rw [branchColumn035_14]
  exact sparseColumn41_sum n

theorem branchColumn035_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 15) i) = _
  rw [branchColumn035_15]
  exact sparseColumn38_sum n

theorem branchColumn035_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 16) i) = _
  rw [branchColumn035_16]
  exact sparseColumn39_sum n

theorem branchColumn035_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 17) i) = _
  rw [branchColumn035_17]
  exact sparseColumn17_sum n

theorem branchColumn035_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 18) i) = _
  rw [branchColumn035_18]
  exact sparseColumn18_sum n

theorem branchColumn035_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 19) i) = _
  rw [branchColumn035_19]
  exact sparseColumn19_sum n

theorem branchColumn035_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 20) = sparseColumn52 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 20) = sparseDot52 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 20) i) = _
  rw [branchColumn035_20]
  exact sparseColumn52_sum n

theorem branchColumn035_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 21) i) = _
  rw [branchColumn035_21]
  exact sparseColumn21_sum n

theorem branchColumn035_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 22) i) = _
  rw [branchColumn035_22]
  exact sparseColumn22_sum n

theorem branchColumn035_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 23) = sparseColumn53 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 23) = sparseDot53 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 23) i) = _
  rw [branchColumn035_23]
  exact sparseColumn53_sum n

theorem branchColumn035_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 24) i) = _
  rw [branchColumn035_24]
  exact sparseColumn24_sum n

theorem branchColumn035_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 25) i) = _
  rw [branchColumn035_25]
  exact sparseColumn25_sum n

theorem branchColumn035_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 26) = sparseColumn26 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 26) = sparseDot26 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 26) i) = _
  rw [branchColumn035_26]
  exact sparseColumn26_sum n

theorem branchColumn035_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 27) i) = _
  rw [branchColumn035_27]
  exact sparseColumn27_sum n

theorem branchColumn035_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 28) i) = _
  rw [branchColumn035_28]
  exact sparseColumn28_sum n

theorem branchColumn035_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 29) = sparseColumn29 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 29) = sparseDot29 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 29) i) = _
  rw [branchColumn035_29]
  exact sparseColumn29_sum n

theorem branchColumn035_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 30) i) = _
  rw [branchColumn035_30]
  exact sparseColumn30_sum n

theorem branchColumn035_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 31) i) = _
  rw [branchColumn035_31]
  exact sparseColumn31_sum n

theorem branchColumn035_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 35 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 35 i)) = _
  rw [branchIntegerMatrix035_eq]
  simp only [branchIntegerMatrix035, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot035_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 35 i) 32) i) = _
  rw [branchColumn035_32]
  exact sparseColumn32_sum n

def branchSparseDots035 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot52, sparseDot21, sparseDot22, sparseDot53, sparseDot24, sparseDot25, sparseDot26, sparseDot27, sparseDot28, sparseDot29, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot035_0 :
    branchSparseDots035 0 = sparseDot00 := rfl

private theorem branchSparseDot035_1 :
    branchSparseDots035 1 = sparseDot01 := rfl

private theorem branchSparseDot035_2 :
    branchSparseDots035 2 = sparseDot02 := rfl

private theorem branchSparseDot035_3 :
    branchSparseDots035 3 = sparseDot03 := rfl

private theorem branchSparseDot035_4 :
    branchSparseDots035 4 = sparseDot04 := rfl

private theorem branchSparseDot035_5 :
    branchSparseDots035 5 = sparseDot05 := rfl

private theorem branchSparseDot035_6 :
    branchSparseDots035 6 = sparseDot06 := rfl

private theorem branchSparseDot035_7 :
    branchSparseDots035 7 = sparseDot07 := rfl

private theorem branchSparseDot035_8 :
    branchSparseDots035 8 = sparseDot08 := rfl

private theorem branchSparseDot035_9 :
    branchSparseDots035 9 = sparseDot09 := rfl

private theorem branchSparseDot035_10 :
    branchSparseDots035 10 = sparseDot10 := rfl

private theorem branchSparseDot035_11 :
    branchSparseDots035 11 = sparseDot11 := rfl

private theorem branchSparseDot035_12 :
    branchSparseDots035 12 = sparseDot35 := rfl

private theorem branchSparseDot035_13 :
    branchSparseDots035 13 = sparseDot36 := rfl

private theorem branchSparseDot035_14 :
    branchSparseDots035 14 = sparseDot41 := rfl

private theorem branchSparseDot035_15 :
    branchSparseDots035 15 = sparseDot38 := rfl

private theorem branchSparseDot035_16 :
    branchSparseDots035 16 = sparseDot39 := rfl

private theorem branchSparseDot035_17 :
    branchSparseDots035 17 = sparseDot17 := rfl

private theorem branchSparseDot035_18 :
    branchSparseDots035 18 = sparseDot18 := rfl

private theorem branchSparseDot035_19 :
    branchSparseDots035 19 = sparseDot19 := rfl

private theorem branchSparseDot035_20 :
    branchSparseDots035 20 = sparseDot52 := rfl

private theorem branchSparseDot035_21 :
    branchSparseDots035 21 = sparseDot21 := rfl

private theorem branchSparseDot035_22 :
    branchSparseDots035 22 = sparseDot22 := rfl

private theorem branchSparseDot035_23 :
    branchSparseDots035 23 = sparseDot53 := rfl

private theorem branchSparseDot035_24 :
    branchSparseDots035 24 = sparseDot24 := rfl

private theorem branchSparseDot035_25 :
    branchSparseDots035 25 = sparseDot25 := rfl

private theorem branchSparseDot035_26 :
    branchSparseDots035 26 = sparseDot26 := rfl

private theorem branchSparseDot035_27 :
    branchSparseDots035 27 = sparseDot27 := rfl

private theorem branchSparseDot035_28 :
    branchSparseDots035 28 = sparseDot28 := rfl

private theorem branchSparseDot035_29 :
    branchSparseDots035 29 = sparseDot29 := rfl

private theorem branchSparseDot035_30 :
    branchSparseDots035 30 = sparseDot30 := rfl

private theorem branchSparseDot035_31 :
    branchSparseDots035 31 = sparseDot31 := rfl

private theorem branchSparseDot035_32 :
    branchSparseDots035 32 = sparseDot32 := rfl

theorem branchDots035 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 35 i) k) = branchSparseDots035 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot035_0 n
      _ = _ := congrFun branchSparseDot035_0.symm n
  · calc
      _ = sparseDot01 n := branchDot035_1 n
      _ = _ := congrFun branchSparseDot035_1.symm n
  · calc
      _ = sparseDot02 n := branchDot035_2 n
      _ = _ := congrFun branchSparseDot035_2.symm n
  · calc
      _ = sparseDot03 n := branchDot035_3 n
      _ = _ := congrFun branchSparseDot035_3.symm n
  · calc
      _ = sparseDot04 n := branchDot035_4 n
      _ = _ := congrFun branchSparseDot035_4.symm n
  · calc
      _ = sparseDot05 n := branchDot035_5 n
      _ = _ := congrFun branchSparseDot035_5.symm n
  · calc
      _ = sparseDot06 n := branchDot035_6 n
      _ = _ := congrFun branchSparseDot035_6.symm n
  · calc
      _ = sparseDot07 n := branchDot035_7 n
      _ = _ := congrFun branchSparseDot035_7.symm n
  · calc
      _ = sparseDot08 n := branchDot035_8 n
      _ = _ := congrFun branchSparseDot035_8.symm n
  · calc
      _ = sparseDot09 n := branchDot035_9 n
      _ = _ := congrFun branchSparseDot035_9.symm n
  · calc
      _ = sparseDot10 n := branchDot035_10 n
      _ = _ := congrFun branchSparseDot035_10.symm n
  · calc
      _ = sparseDot11 n := branchDot035_11 n
      _ = _ := congrFun branchSparseDot035_11.symm n
  · calc
      _ = sparseDot35 n := branchDot035_12 n
      _ = _ := congrFun branchSparseDot035_12.symm n
  · calc
      _ = sparseDot36 n := branchDot035_13 n
      _ = _ := congrFun branchSparseDot035_13.symm n
  · calc
      _ = sparseDot41 n := branchDot035_14 n
      _ = _ := congrFun branchSparseDot035_14.symm n
  · calc
      _ = sparseDot38 n := branchDot035_15 n
      _ = _ := congrFun branchSparseDot035_15.symm n
  · calc
      _ = sparseDot39 n := branchDot035_16 n
      _ = _ := congrFun branchSparseDot035_16.symm n
  · calc
      _ = sparseDot17 n := branchDot035_17 n
      _ = _ := congrFun branchSparseDot035_17.symm n
  · calc
      _ = sparseDot18 n := branchDot035_18 n
      _ = _ := congrFun branchSparseDot035_18.symm n
  · calc
      _ = sparseDot19 n := branchDot035_19 n
      _ = _ := congrFun branchSparseDot035_19.symm n
  · calc
      _ = sparseDot52 n := branchDot035_20 n
      _ = _ := congrFun branchSparseDot035_20.symm n
  · calc
      _ = sparseDot21 n := branchDot035_21 n
      _ = _ := congrFun branchSparseDot035_21.symm n
  · calc
      _ = sparseDot22 n := branchDot035_22 n
      _ = _ := congrFun branchSparseDot035_22.symm n
  · calc
      _ = sparseDot53 n := branchDot035_23 n
      _ = _ := congrFun branchSparseDot035_23.symm n
  · calc
      _ = sparseDot24 n := branchDot035_24 n
      _ = _ := congrFun branchSparseDot035_24.symm n
  · calc
      _ = sparseDot25 n := branchDot035_25 n
      _ = _ := congrFun branchSparseDot035_25.symm n
  · calc
      _ = sparseDot26 n := branchDot035_26 n
      _ = _ := congrFun branchSparseDot035_26.symm n
  · calc
      _ = sparseDot27 n := branchDot035_27 n
      _ = _ := congrFun branchSparseDot035_27.symm n
  · calc
      _ = sparseDot28 n := branchDot035_28 n
      _ = _ := congrFun branchSparseDot035_28.symm n
  · calc
      _ = sparseDot29 n := branchDot035_29 n
      _ = _ := congrFun branchSparseDot035_29.symm n
  · calc
      _ = sparseDot30 n := branchDot035_30 n
      _ = _ := congrFun branchSparseDot035_30.symm n
  · calc
      _ = sparseDot31 n := branchDot035_31 n
      _ = _ := congrFun branchSparseDot035_31.symm n
  · calc
      _ = sparseDot32 n := branchDot035_32 n
      _ = _ := congrFun branchSparseDot035_32.symm n

def branchIntegerCurvature035 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101955390, 101955390, 44932602, 44932602, 115699695, 115699695, 48290998, 48290998, 204734428, 204734428]

theorem branchIntegerCurvature035_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 35 i)) = branchIntegerCurvature035 := by
  change curvatureNumerators ∘ branchRows 35 = branchIntegerCurvature035
  rw [show branchRows 35 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 34, 35, 36, 37, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature035_entry (i : Fin 42) :
    curvatureNumerators (branchRows 35 i) = branchIntegerCurvature035 i :=
  congrFun branchIntegerCurvature035_eq i

def branchResiduals035 : Fin 33 → Fin 2 → ℕ := ![![1299032358292642, 33000000000000], ![1544079178931672, 33000000000000], ![1582596039613752, 1336957321771908], ![33000000000000, 1024972577710138], ![858142737625302, 33000000000000], ![1055430827592989, 893543026158127], ![719276878788466, 622101700319854], ![33000000000000, 760032410154233], ![1575841241234724, 1128234752178627], ![1026453309955757, 33000000000000], ![33000000000000, 777347420336232], ![509074331094638, 466521501490144], ![991051622521255, 66000000000000], ![33000000000000, 860568754468382], ![1055391089796589, 483836562042497], ![476101617187278, 33000000000000], ![66000000000000, 743836417130807], ![659703735157417, 461801678787261], ![619532993535711, 246306849641587], ![625819033157232, 511433164941632], ![1229411389574310, 951169131190975], ![754719530248321, 390169556652905], ![468078925992357, 97768067069809], ![1229411389574310, 951169131190975], ![664908105537880, 229966723420264], ![501932851477877, 221360137673294], ![396136216194598, 856050208658842], ![408376286972534, 546318670561582], ![283516963432086, 309025754415644], ![396136216194598, 951169131190975], ![216154441782752, 552035493757653], ![1679207070951443, 648307756949721], ![1329665580284121, 2885788018294683]]

theorem branchResiduals035_eq : residualNumerators 35 = branchResiduals035 := rfl

theorem integerCheck035_0_0 :
    integerResidualCheck 35 0 0 (dualNumerators035 0 0) ∧
    integerMassCheck 35 0 0 (dualNumerators035 0 0) := by
  apply integerChecks_of_simple 35 0 0 (dualNumerators035 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1820383169708, 352663154359, 0, 1308901425339, 1536582908426, 298609637459, 1741178091979, 225835502005, 1430871029972, 404321515913]) (branchResiduals035 0 0) 18767167
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck035_0_1 :
    integerResidualCheck 35 0 1 (dualNumerators035 0 1) ∧
    integerMassCheck 35 0 1 (dualNumerators035 0 1) := by
  apply integerChecks_of_simple 35 0 1 (dualNumerators035 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals035 0 1) 18767167
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck035_1_0 :
    integerResidualCheck 35 1 0 (dualNumerators035 1 0) ∧
    integerMassCheck 35 1 0 (dualNumerators035 1 0) := by
  apply integerChecks_of_simple 35 1 0 (dualNumerators035 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 2155510583453, 417587447667, 0, 1549866490727, 1819463493499, 353582830568, 2061724074025, 267411181773, 1694290356000, 478755968067]) (branchResiduals035 1 0) 22176635
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck035_1_1 :
    integerResidualCheck 35 1 1 (dualNumerators035 1 1) ∧
    integerMassCheck 35 1 1 (dualNumerators035 1 1) := by
  apply integerChecks_of_simple 35 1 1 (dualNumerators035 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals035 1 1) 22176635
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck035_2_0 :
    integerResidualCheck 35 2 0 (dualNumerators035 2 0) ∧
    integerMassCheck 35 2 0 (dualNumerators035 2 0) := by
  apply integerChecks_of_simple 35 2 0 (dualNumerators035 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 2155510583455, 417587447667, 0, 1549866490728, 1819463493501, 353582830568, 2061724074027, 267411181773, 1694290356001, 478755968068]) (branchResiduals035 2 0) 22681452
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck035_2_1 :
    integerResidualCheck 35 2 1 (dualNumerators035 2 1) ∧
    integerMassCheck 35 2 1 (dualNumerators035 2 1) := by
  apply integerChecks_of_simple 35 2 1 (dualNumerators035 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1820383169707, 352663154359, 0, 1308901425338, 1536582908425, 298609637459, 1741178091978, 225835502005, 1430871029971, 404321515912]) (branchResiduals035 2 1) 22681452
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck035_3_0 :
    integerResidualCheck 35 3 0 (dualNumerators035 3 0) ∧
    integerMassCheck 35 3 0 (dualNumerators035 3 0) := by
  apply integerChecks_of_simple 35 3 0 (dualNumerators035 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals035 3 0) 16360330
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck035_3_1 :
    integerResidualCheck 35 3 1 (dualNumerators035 3 1) ∧
    integerMassCheck 35 3 1 (dualNumerators035 3 1) := by
  apply integerChecks_of_simple 35 3 1 (dualNumerators035 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000001, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000001, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1434332169154, 277873425546, 0, 1031321016287, 1210717794365, 235283107510, 1371924214149, 177942276579, 1127424369963, 318576531911]) (branchResiduals035 3 1) 16360330
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck035_4_0 :
    integerResidualCheck 35 4 0 (dualNumerators035 4 0) ∧
    integerMassCheck 35 4 0 (dualNumerators035 4 0) := by
  apply integerChecks_of_simple 35 4 0 (dualNumerators035 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1211329770563, 234671131311, 0, 870976665588, 1022481779049, 198702531231, 1158624675158, 150276750182, 952138376845, 269045933435]) (branchResiduals035 4 0) 13760362
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck035_4_1 :
    integerResidualCheck 35 4 1 (dualNumerators035 4 1) ∧
    integerMassCheck 35 4 1 (dualNumerators035 4 1) := by
  apply integerChecks_of_simple 35 4 1 (dualNumerators035 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals035 4 1) 13760362
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck035_5_0 :
    integerResidualCheck 35 5 0 (dualNumerators035 5 0) ∧
    integerMassCheck 35 5 0 (dualNumerators035 5 0) := by
  apply integerChecks_of_simple 35 5 0 (dualNumerators035 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1434332169156, 277873425546, 0, 1031321016288, 1210717794366, 235283107510, 1371924214150, 177942276579, 1127424369964, 318576531911]) (branchResiduals035 5 0) 17641130
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck035_5_1 :
    integerResidualCheck 35 5 1 (dualNumerators035 5 1) ∧
    integerMassCheck 35 5 1 (dualNumerators035 5 1) := by
  apply integerChecks_of_simple 35 5 1 (dualNumerators035 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1211329770562, 234671131311, 0, 870976665588, 1022481779048, 198702531231, 1158624675157, 150276750182, 952138376844, 269045933435]) (branchResiduals035 5 1) 17641130
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck035_6_0 :
    integerResidualCheck 35 6 0 (dualNumerators035 6 0) ∧
    integerMassCheck 35 6 0 (dualNumerators035 6 0) := by
  apply integerChecks_of_simple 35 6 0 (dualNumerators035 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 659499318402, 1175693227483, 103906894360, 5439901403, 1430871029972, 404321515913]) (branchResiduals035 6 0) 8962451
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck035_6_1 :
    integerResidualCheck 35 6 1 (dualNumerators035 6 1) ∧
    integerMassCheck 35 6 1 (dualNumerators035 6 1) := by
  apply integerChecks_of_simple 35 6 1 (dualNumerators035 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 760187607595, 1097479190627, 0, 0]) (branchResiduals035 6 1) 8962451
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck035_7_0 :
    integerResidualCheck 35 7 0 (dualNumerators035 7 0) ∧
    integerMassCheck 35 7 0 (dualNumerators035 7 0) := by
  apply integerChecks_of_simple 35 7 0 (dualNumerators035 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals035 7 0) 10424794
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck035_7_1 :
    integerResidualCheck 35 7 1 (dualNumerators035 7 1) ∧
    integerMassCheck 35 7 1 (dualNumerators035 7 1) := by
  apply integerChecks_of_simple 35 7 1 (dualNumerators035 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 1077755291729, 208793723834, 0, 774933245365, 909731746751, 176791415285, 1030862037014, 133705590887, 847145178002, 239377984034]) (branchResiduals035 7 1) 10424794
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck035_8_0 :
    integerResidualCheck 35 8 0 (dualNumerators035 8 0) ∧
    integerMassCheck 35 8 0 (dualNumerators035 8 0) := by
  apply integerChecks_of_simple 35 8 0 (dualNumerators035 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 2155510583457, 417587447668, 0, 1549866490730, 1819463493502, 353582830569, 2061724074028, 267411181773, 1694290356003, 478755968068]) (branchResiduals035 8 0) 22681452
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck035_8_1 :
    integerResidualCheck 35 8 1 (dualNumerators035 8 1) ∧
    integerMassCheck 35 8 1 (dualNumerators035 8 1) := by
  apply integerChecks_of_simple 35 8 1 (dualNumerators035 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1537359598228, 297832947655, 0, 1105400337063, 1297683104332, 252183386394, 1470468908124, 190723789588, 1208406751039, 341459739686]) (branchResiduals035 8 1) 22681452
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck035_9_0 :
    integerResidualCheck 35 9 0 (dualNumerators035 9 0) ∧
    integerMassCheck 35 9 0 (dualNumerators035 9 0) := by
  apply integerChecks_of_simple 35 9 0 (dualNumerators035 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 1434332169154, 277873425546, 0, 1031321016287, 1210717794365, 235283107510, 1371924214149, 177942276579, 1127424369963, 318576531911]) (branchResiduals035 9 0) 16350530
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck035_9_1 :
    integerResidualCheck 35 9 1 (dualNumerators035 9 1) ∧
    integerMassCheck 35 9 1 (dualNumerators035 9 1) := by
  apply integerChecks_of_simple 35 9 1 (dualNumerators035 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals035 9 1) 16350530
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck035_10_0 :
    integerResidualCheck 35 10 0 (dualNumerators035 10 0) ∧
    integerMassCheck 35 10 0 (dualNumerators035 10 0) := by
  apply integerChecks_of_simple 35 10 0 (dualNumerators035 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals035 10 0) 10683139
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck035_10_1 :
    integerResidualCheck 35 10 1 (dualNumerators035 10 1) ∧
    integerMassCheck 35 10 1 (dualNumerators035 10 1) := by
  apply integerChecks_of_simple 35 10 1 (dualNumerators035 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 1096480134411, 212421290928, 0, 788396879662, 925537360486, 179862976579, 1048772159673, 136028582177, 861863417206, 243536919859]) (branchResiduals035 10 1) 10683139
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck035_11_0 :
    integerResidualCheck 35 11 0 (dualNumerators035 11 0) ∧
    integerMassCheck 35 11 0 (dualNumerators035 11 0) := by
  apply integerChecks_of_simple 35 11 0 (dualNumerators035 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 681475855631, 132022438389, 0, 489998333105, 575232824436, 111787046581, 651824764029, 84543432681, 535658687508, 151361183509]) (branchResiduals035 11 0) 15120968
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck035_11_1 :
    integerResidualCheck 35 11 1 (dualNumerators035 11 1) ∧
    integerMassCheck 35 11 1 (dualNumerators035 11 1) := by
  apply integerChecks_of_simple 35 11 1 (dualNumerators035 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 621427644954, 120389287883, 0, 446822154676, 524546213099, 101936936605, 594389257794, 77093892371, 488459149252, 138024000452]) (branchResiduals035 11 1) 15120968
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck035_12_0 :
    integerResidualCheck 35 12 0 (dualNumerators035 12 0) ∧
    integerMassCheck 35 12 0 (dualNumerators035 12 0) := by
  apply integerChecks_of_simple 35 12 0 (dualNumerators035 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1434332169154, 277873425546, 0, 1031321016287, 1210717794365, 235283107510, 1371924214149, 177942276579, 1127424369963, 318576531911]) (branchResiduals035 12 0) 16348076
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck035_12_1 :
    integerResidualCheck 35 12 1 (dualNumerators035 12 1) ∧
    integerMassCheck 35 12 1 (dualNumerators035 12 1) := by
  apply integerChecks_of_simple 35 12 1 (dualNumerators035 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals035 12 1) 16348076
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck035_13_0 :
    integerResidualCheck 35 13 0 (dualNumerators035 13 0) ∧
    integerMassCheck 35 13 0 (dualNumerators035 13 0) := by
  apply integerChecks_of_simple 35 13 0 (dualNumerators035 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals035 13 0) 13962901
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck035_13_1 :
    integerResidualCheck 35 13 1 (dualNumerators035 13 1) ∧
    integerMassCheck 35 13 1 (dualNumerators035 13 1) := by
  apply integerChecks_of_simple 35 13 1 (dualNumerators035 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1211329770563, 234671131311, 0, 870976665588, 1022481779049, 198702531231, 1158624675158, 150276750182, 952138376845, 269045933435]) (branchResiduals035 13 1) 13962901
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck035_14_0 :
    integerResidualCheck 35 14 0 (dualNumerators035 14 0) ∧
    integerMassCheck 35 14 0 (dualNumerators035 14 0) := by
  apply integerChecks_of_simple 35 14 0 (dualNumerators035 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1434332169156, 277873425546, 0, 1031321016288, 1210717794366, 235283107510, 1371924214150, 177942276579, 1127424369964, 318576531911]) (branchResiduals035 14 0) 20161291
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck035_14_1 :
    integerResidualCheck 35 14 1 (dualNumerators035 14 1) ∧
    integerMassCheck 35 14 1 (dualNumerators035 14 1) := by
  apply integerChecks_of_simple 35 14 1 (dualNumerators035 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 656716276290, 127225760691, 0, 472195570901, 554333297859, 107725567034, 628142476787, 81471776052, 516196980004, 145861884889]) (branchResiduals035 14 1) 20161291
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck035_15_0 :
    integerResidualCheck 35 15 0 (dualNumerators035 15 0) ∧
    integerMassCheck 35 15 0 (dualNumerators035 15 0) := by
  apply integerChecks_of_simple 35 15 0 (dualNumerators035 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 681475855631, 132022438389, 0, 489998333105, 575232824436, 111787046581, 651824764029, 84543432681, 535658687508, 151361183509]) (branchResiduals035 15 0) 12900283
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck035_15_1 :
    integerResidualCheck 35 15 1 (dualNumerators035 15 1) ∧
    integerMassCheck 35 15 1 (dualNumerators035 15 1) := by
  apply integerChecks_of_simple 35 15 1 (dualNumerators035 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals035 15 1) 12900283
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck035_16_0 :
    integerResidualCheck 35 16 0 (dualNumerators035 16 0) ∧
    integerMassCheck 35 16 0 (dualNumerators035 16 0) := by
  apply integerChecks_of_simple 35 16 0 (dualNumerators035 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals035 16 0) 10683060
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck035_16_1 :
    integerResidualCheck 35 16 1 (dualNumerators035 16 1) ∧
    integerMassCheck 35 16 1 (dualNumerators035 16 1) := by
  apply integerChecks_of_simple 35 16 1 (dualNumerators035 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 1096480134411, 212421290928, 0, 788396879662, 925537360486, 179862976579, 1048772159673, 136028582177, 861863417206, 243536919859]) (branchResiduals035 16 1) 10683060
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck035_17_0 :
    integerResidualCheck 35 17 0 (dualNumerators035 17 0) ∧
    integerMassCheck 35 17 0 (dualNumerators035 17 0) := by
  apply integerChecks_of_simple 35 17 0 (dualNumerators035 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 893807506737, 173157486820, 0, 642670147151, 754461676602, 146617228717, 854917840966, 110885153378, 702557180842, 198521724476]) (branchResiduals035 17 0) 15120968
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck035_17_1 :
    integerResidualCheck 35 17 1 (dualNumerators035 17 1) ∧
    integerMassCheck 35 17 1 (dualNumerators035 17 1) := by
  apply integerChecks_of_simple 35 17 1 (dualNumerators035 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 621427644954, 120389287883, 0, 446822154676, 524546213099, 101936936605, 594389257794, 77093892370, 488459149252, 138024000452]) (branchResiduals035 17 1) 15120968
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck035_18_0 :
    integerResidualCheck 35 18 0 (dualNumerators035 18 0) ∧
    integerMassCheck 35 18 0 (dualNumerators035 18 0) := by
  apply integerChecks_of_simple 35 18 0 (dualNumerators035 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 975124848843, 293271850585, 0, 763999473637, 809471999789, 261721072459, 862769256399, 123780303264, 835192545885, 236000526363]) (branchResiduals035 18 0) 13565580
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck035_18_1 :
    integerResidualCheck 35 18 1 (dualNumerators035 18 1) ∧
    integerMassCheck 35 18 1 (dualNumerators035 18 1) := by
  apply integerChecks_of_simple 35 18 1 (dualNumerators035 18 1)
    (![538874628613, 99205301184, 538874628613, 0, 1, 173280948973, 205181483568, 0, 64396810428, 45929282541, 173280948973, 0, 90678335261, 492556886113, 205181483568, 0, 0, 492556886114, 154686685730, 130636815909, 835183729590, 268562336295, 71184255953, 84289076957, 173280948973, 0, 90678335261, 492556886113, 0, 0, 268562336295, 763397412564, 115240860334, 2939686143, 71184255953, 0, 99806458592, 0, 177057282341, 91505053955, 77817540467, 21988918126]) (branchResiduals035 18 1) 13565580
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck035_19_0 :
    integerResidualCheck 35 19 0 (dualNumerators035 19 0) ∧
    integerMassCheck 35 19 0 (dualNumerators035 19 0) := by
  apply integerChecks_of_simple 35 19 0 (dualNumerators035 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 737249033801, 333944038447, 0, 645216866088, 597351015788, 307298608852, 577111910116, 96603051948, 705341215054, 199308409586]) (branchResiduals035 19 0) 8248658
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck035_19_1 :
    integerResidualCheck 35 19 1 (dualNumerators035 19 1) ∧
    integerMassCheck 35 19 1 (dualNumerators035 19 1) := by
  apply integerChecks_of_simple 35 19 1 (dualNumerators035 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 744995341971, 19004131667, 55115222459, 405068248519, 645216866088, 0, 838241775552, 149235960098, 503065535987, 142151330101]) (branchResiduals035 19 1) 8248658
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck035_20_0 :
    integerResidualCheck 35 20 0 (dualNumerators035 20 0) ∧
    integerMassCheck 35 20 0 (dualNumerators035 20 0) := by
  apply integerChecks_of_simple 35 20 0 (dualNumerators035 20 0)
    (![525362030296, 96717669897, 525362030296, 0, 2, 1982073878105, 2346968095804, 0, 736602820676, 525362030295, 1982073878106, 0, 160571279833, 872209325039, 2346968095804, 0, 0, 872209325040, 1769383425546, 1494289025232, 814241006256, 3071949885821, 814241006256, 964140481889, 1982073878106, 0, 160571279833, 872209325039, 0, 0, 3071949885821, 1351808005779, 1318182410191, 33625595588, 814241006256, 0, 1141636028738, 0, 2025269461734, 1046680424088, 890115821339, 251520207400]) (branchResiduals035 20 0) 35312013
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck035_20_1 :
    integerResidualCheck 35 20 1 (dualNumerators035 20 1) ∧
    integerMassCheck 35 20 1 (dualNumerators035 20 1) := by
  apply integerChecks_of_simple 35 20 1 (dualNumerators035 20 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 836254566552, 1355737922885, 0, 1320313360088, 549979932486, 1301213128931, 0, 135852760286, 1443346382594, 407846678822]) (branchResiduals035 20 1) 35312013
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck035_21_0 :
    integerResidualCheck 35 21 0 (dualNumerators035 21 0) ∧
    integerMassCheck 35 21 0 (dualNumerators035 21 0) := by
  apply integerChecks_of_simple 35 21 0 (dualNumerators035 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 604293255477, 704608169863, 851509250277, 798941670661, 1020530044549, 288371380791]) (branchResiduals035 21 0) 11182451
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck035_21_1 :
    integerResidualCheck 35 21 1 (dualNumerators035 21 1) ∧
    integerMassCheck 35 21 1 (dualNumerators035 21 1) := by
  apply integerChecks_of_simple 35 21 1 (dualNumerators035 21 1)
    (![114087637157, 21003212630, 114087637157, 0, 1, 11738971135, 13900082653, 0, 159960694697, 114087637156, 11738971135, 0, 218966847953, 1189409008000, 13900082653, 0, 0, 1189409008001, 1568336550649, 324499857786, 176820605835, 18193837997, 176820605835, 209372781287, 11738971135, 0, 218966847953, 1189409008000, 0, 0, 18193837997, 1843425165269, 918700010035, 924725155234, 0, 176820605835, 73655079013, 174262641531, 0, 18193837997, 193297583373, 54620137172]) (branchResiduals035 21 1) 11182451
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck035_22_0 :
    integerResidualCheck 35 22 0 (dualNumerators035 22 0) ∧
    integerMassCheck 35 22 0 (dualNumerators035 22 0) := by
  apply integerChecks_of_simple 35 22 0 (dualNumerators035 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 179826715678, 584172757959, 460183470977, 0, 139439543571, 505777322518, 256292246333, 545043834385, 503065535987, 142151330101]) (branchResiduals035 22 0) 6465674
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck035_22_1 :
    integerResidualCheck 35 22 1 (dualNumerators035 22 1) ∧
    integerMassCheck 35 22 1 (dualNumerators035 22 1) := by
  apply integerChecks_of_simple 35 22 1 (dualNumerators035 22 1)
    (![50594765625, 9314353833, 50594765625, 0, 0, 5205914576, 6164308785, 0, 70938219592, 50594765625, 5205914576, 0, 15463748427, 83997745994, 6164308785, 0, 0, 83997745994, 1170399714012, 143906865451, 78415131848, 8068472555, 78415131848, 92851136735, 5205914576, 0, 15463748427, 83997745994, 0, 0, 8068472555, 130185291813, 109057552771, 21127739043, 0, 78415131848, 32664025241, 77280744217, 0, 8068472555, 85722223462, 24222545996]) (branchResiduals035 22 1) 6465674
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck035_23_0 :
    integerResidualCheck 35 23 0 (dualNumerators035 23 0) ∧
    integerMassCheck 35 23 0 (dualNumerators035 23 0) := by
  apply integerChecks_of_simple 35 23 0 (dualNumerators035 23 0)
    (![525362030296, 96717669897, 525362030296, 0, 2, 1982073878105, 2346968095804, 0, 736602820676, 525362030295, 1982073878106, 0, 160571279833, 872209325039, 2346968095804, 0, 0, 872209325040, 1769383425546, 1494289025232, 814241006256, 3071949885821, 814241006256, 964140481889, 1982073878106, 0, 160571279833, 872209325039, 0, 0, 3071949885821, 1351808005779, 318182410191, 1033625595588, 814241006256, 0, 1141636028738, 0, 2025269461734, 1046680424088, 890115821339, 251520207400]) (branchResiduals035 23 0) 35297932
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck035_23_1 :
    integerResidualCheck 35 23 1 (dualNumerators035 23 1) ∧
    integerMassCheck 35 23 1 (dualNumerators035 23 1) := by
  apply integerChecks_of_simple 35 23 1 (dualNumerators035 23 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 1836254566552, 355737922885, 0, 1320313360088, 549979932486, 1301213128931, 0, 135852760286, 1443346382594, 407846678822]) (branchResiduals035 23 1) 35297932
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck035_24_0 :
    integerResidualCheck 35 24 0 (dualNumerators035 24 0) ∧
    integerMassCheck 35 24 0 (dualNumerators035 24 0) := by
  apply integerChecks_of_simple 35 24 0 (dualNumerators035 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 384946583730, 686246488518, 569308312247, 737522866658, 835192545885, 236000526363]) (branchResiduals035 24 0) 9356857
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck035_24_1 :
    integerResidualCheck 35 24 1 (dualNumerators035 24 1) ∧
    integerMassCheck 35 24 1 (dualNumerators035 24 1) := by
  apply integerChecks_of_simple 35 24 1 (dualNumerators035 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 587483804282, 282115266095, 48434165160, 99625565721, 0, 0, 115439864933, 32619865948]) (branchResiduals035 24 1) 9356857
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck035_25_0 :
    integerResidualCheck 35 25 0 (dualNumerators035 25 0) ∧
    integerMassCheck 35 25 0 (dualNumerators035 25 0) := by
  apply integerChecks_of_simple 35 25 0 (dualNumerators035 25 0)
    (![30936264063, 5695279071, 30936264063, 0, 1, 16941043971, 20059842445, 0, 627070502755, 447241068346, 509886390043, 0, 136694444206, 742512415929, 603755038162, 0, 0, 742512415929, 1506277362888, 1272089305134, 47947079019, 26256356369, 693163945107, 820773474842, 509886390043, 0, 136694444206, 742512415929, 0, 0, 790255830005, 1150795112397, 483731503338, 667063609060, 47947079019, 0, 333437443812, 638438115729, 26256356369, 0, 757756228906, 214119330636]) (branchResiduals035 25 0) 8671199
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck035_25_1 :
    integerResidualCheck 35 25 1 (dualNumerators035 25 1) ∧
    integerMassCheck 35 25 1 (dualNumerators035 25 1) := by
  apply integerChecks_of_simple 35 25 1 (dualNumerators035 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 415529968297, 599898615461, 0, 0]) (branchResiduals035 25 1) 8671199
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck035_26_0 :
    integerResidualCheck 35 26 0 (dualNumerators035 26 0) ∧
    integerMassCheck 35 26 0 (dualNumerators035 26 0) := by
  apply integerChecks_of_simple 35 26 0 (dualNumerators035 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0]) (branchResiduals035 26 0) 15099566
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck035_26_1 :
    integerResidualCheck 35 26 1 (dualNumerators035 26 1) ∧
    integerMassCheck 35 26 1 (dualNumerators035 26 1) := by
  apply integerChecks_of_simple 35 26 1 (dualNumerators035 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 879744679617, 350168760452, 564110399358, 1160334187225, 0, 0, 1344522571906, 379922014678]) (branchResiduals035 26 1) 15099566
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck035_27_0 :
    integerResidualCheck 35 27 0 (dualNumerators035 27 0) ∧
    integerMassCheck 35 27 0 (dualNumerators035 27 0) := by
  apply integerChecks_of_simple 35 27 0 (dualNumerators035 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 286173900105, 455299762271, 595678484088, 168320989550]) (branchResiduals035 27 0) 7338775
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck035_27_1 :
    integerResidualCheck 35 27 1 (dualNumerators035 27 1) ∧
    integerMassCheck 35 27 1 (dualNumerators035 27 1) := by
  apply integerChecks_of_simple 35 27 1 (dualNumerators035 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 918185996600, 613751944609, 0, 377837583379, 718114611481, 575645700634, 576174693322, 69042172766, 413046270426, 116714568052]) (branchResiduals035 27 1) 7338775
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck035_28_0 :
    integerResidualCheck 35 28 0 (dualNumerators035 28 0) ∧
    integerMassCheck 35 28 0 (dualNumerators035 28 0) := by
  apply integerChecks_of_simple 35 28 0 (dualNumerators035 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 450383711774, 395438493575, 503065535987, 142151330101]) (branchResiduals035 28 0) 10335557
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck035_28_1 :
    integerResidualCheck 35 28 1 (dualNumerators035 28 1) ∧
    integerMassCheck 35 28 1 (dualNumerators035 28 1) := by
  apply integerChecks_of_simple 35 28 1 (dualNumerators035 28 1)
    (![71098470185, 13089028086, 71098470186, 0, 1, 500260975618, 592357612055, 0, 99686179557, 71098470185, 7315629546, 0, 112480335850, 610983470480, 8662416338, 0, 0, 610983470481, 1239454790169, 202225622679, 110193136482, 775337722729, 110193136482, 130479382508, 7315629546, 0, 112480335850, 610983470480, 0, 0, 11338249092, 946942807286, 484898704770, 462044102516, 0, 110193136482, 361227794882, 438489340489, 0, 11338249092, 120461452361, 34038816922]) (branchResiduals035 28 1) 10335557
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck035_29_0 :
    integerResidualCheck 35 29 0 (dualNumerators035 29 0) ∧
    integerMassCheck 35 29 0 (dualNumerators035 29 0) := by
  apply integerChecks_of_simple 35 29 0 (dualNumerators035 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0]) (branchResiduals035 29 0) 40352153
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck035_29_1 :
    integerResidualCheck 35 29 1 (dualNumerators035 29 1) ∧
    integerMassCheck 35 29 1 (dualNumerators035 29 1) := by
  apply integerChecks_of_simple 35 29 1 (dualNumerators035 29 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 87654492241, 0, 260370583625, 1414310524520, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 0, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 1836254566552, 355737922885, 0, 1320313360088, 1549979932486, 301213128931, 0, 135852760286, 1443346382594, 407846678822]) (branchResiduals035 29 1) 40352153
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck035_30_0 :
    integerResidualCheck 35 30 0 (dualNumerators035 30 0) ∧
    integerMassCheck 35 30 0 (dualNumerators035 30 0) := by
  apply integerChecks_of_simple 35 30 0 (dualNumerators035 30 0)
    (![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 115599349926, 0, 37915592376, 205954223378, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 0, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 267398408357, 51803141081, 0, 192266201784, 225710625575, 43863150960, 151451427040, 27712131761, 269573776534, 0]) (branchResiduals035 30 0) 7680628
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck035_30_1 :
    integerResidualCheck 35 30 1 (dualNumerators035 30 1) ∧
    integerMassCheck 35 30 1 (dualNumerators035 30 1) := by
  apply integerChecks_of_simple 35 30 1 (dualNumerators035 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 757834259187, 146815365454, 0, 544901951702, 639686846958, 124312626680, 829173251111, 99477537975, 536287180313, 227712293325]) (branchResiduals035 30 1) 7680628
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck035_31_0 :
    integerResidualCheck 35 31 0 (dualNumerators035 31 0) ∧
    integerMassCheck 35 31 0 (dualNumerators035 31 0) := by
  apply integerChecks_of_simple 35 31 0 (dualNumerators035 31 0)
    (![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1719079079316, 0, 1491143233587, 0, 2035556695381, 0, 1259308150413, 1, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079316, 0, 1491143233587, 0, 0, 0, 2664343059941, 1951759503826, 1903210393687, 48549110140, 472517800157, 1808495209396, 1648310233018, 0, 1836249633287, 828093426654, 1648310233018, 0]) (branchResiduals035 31 0) 32891612
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck035_31_1 :
    integerResidualCheck 35 31 1 (dualNumerators035 31 1) ∧
    integerMassCheck 35 31 1 (dualNumerators035 31 1) := by
  apply integerChecks_of_simple 35 31 1 (dualNumerators035 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 556963843680, 992902647048, 725570984152, 37986262977, 845258320866, 704608169862]) (branchResiduals035 31 1) 32891612
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck035_32_0 :
    integerResidualCheck 35 32 0 (dualNumerators035 32 0) ∧
    integerMassCheck 35 32 0 (dualNumerators035 32 0) := by
  apply integerChecks_of_simple 35 32 0 (dualNumerators035 32 0)
    (![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 0, 2079538667399, 1160276651773, 0, 382837210862, 2079538667397, 979882959195, 1, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 1160276651773, 0, 0, 0, 3223007296772, 1518687763292, 1272220299089, 246467464203, 0, 914758491801, 1073879389714, 208690812243, 2973224772447, 249782524326, 0, 1282570201956]) (branchResiduals035 32 0) 67647473
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck035_32_1 :
    integerResidualCheck 35 32 1 (dualNumerators035 32 1) ∧
    integerMassCheck 35 32 1 (dualNumerators035 32 1) := by
  apply integerChecks_of_simple 35 32 1 (dualNumerators035 32 1)
    (![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1946401957496, 0, 638403098871, 3467750500273, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957496, 0, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 4502315850300, 872234448278, 0, 3237278684975, 3800398563899, 738545008631, 2550060655570, 466602515837, 4538943572529, 0]) (branchResiduals035 32 1) 67647473
    branchSparseDots035 branchIntegerCurvature035 branchDots035
    branchIntegerCurvature035_entry rfl
    (congrFun (congrFun branchResiduals035_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks035 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 35 j s (dualNumerators035 j s) ∧
    integerMassCheck 35 j s (dualNumerators035 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck035_0_0
    · exact integerCheck035_0_1
  · fin_cases s
    · exact integerCheck035_1_0
    · exact integerCheck035_1_1
  · fin_cases s
    · exact integerCheck035_2_0
    · exact integerCheck035_2_1
  · fin_cases s
    · exact integerCheck035_3_0
    · exact integerCheck035_3_1
  · fin_cases s
    · exact integerCheck035_4_0
    · exact integerCheck035_4_1
  · fin_cases s
    · exact integerCheck035_5_0
    · exact integerCheck035_5_1
  · fin_cases s
    · exact integerCheck035_6_0
    · exact integerCheck035_6_1
  · fin_cases s
    · exact integerCheck035_7_0
    · exact integerCheck035_7_1
  · fin_cases s
    · exact integerCheck035_8_0
    · exact integerCheck035_8_1
  · fin_cases s
    · exact integerCheck035_9_0
    · exact integerCheck035_9_1
  · fin_cases s
    · exact integerCheck035_10_0
    · exact integerCheck035_10_1
  · fin_cases s
    · exact integerCheck035_11_0
    · exact integerCheck035_11_1
  · fin_cases s
    · exact integerCheck035_12_0
    · exact integerCheck035_12_1
  · fin_cases s
    · exact integerCheck035_13_0
    · exact integerCheck035_13_1
  · fin_cases s
    · exact integerCheck035_14_0
    · exact integerCheck035_14_1
  · fin_cases s
    · exact integerCheck035_15_0
    · exact integerCheck035_15_1
  · fin_cases s
    · exact integerCheck035_16_0
    · exact integerCheck035_16_1
  · fin_cases s
    · exact integerCheck035_17_0
    · exact integerCheck035_17_1
  · fin_cases s
    · exact integerCheck035_18_0
    · exact integerCheck035_18_1
  · fin_cases s
    · exact integerCheck035_19_0
    · exact integerCheck035_19_1
  · fin_cases s
    · exact integerCheck035_20_0
    · exact integerCheck035_20_1
  · fin_cases s
    · exact integerCheck035_21_0
    · exact integerCheck035_21_1
  · fin_cases s
    · exact integerCheck035_22_0
    · exact integerCheck035_22_1
  · fin_cases s
    · exact integerCheck035_23_0
    · exact integerCheck035_23_1
  · fin_cases s
    · exact integerCheck035_24_0
    · exact integerCheck035_24_1
  · fin_cases s
    · exact integerCheck035_25_0
    · exact integerCheck035_25_1
  · fin_cases s
    · exact integerCheck035_26_0
    · exact integerCheck035_26_1
  · fin_cases s
    · exact integerCheck035_27_0
    · exact integerCheck035_27_1
  · fin_cases s
    · exact integerCheck035_28_0
    · exact integerCheck035_28_1
  · fin_cases s
    · exact integerCheck035_29_0
    · exact integerCheck035_29_1
  · fin_cases s
    · exact integerCheck035_30_0
    · exact integerCheck035_30_1
  · fin_cases s
    · exact integerCheck035_31_0
    · exact integerCheck035_31_1
  · fin_cases s
    · exact integerCheck035_32_0
    · exact integerCheck035_32_1

end ElevenSquare.Tasks.T06
