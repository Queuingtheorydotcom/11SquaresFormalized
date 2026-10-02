import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual091
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
import ElevenSquare.Tasks.T06.SparseColumn47
import ElevenSquare.Tasks.T06.SparseColumn50
import ElevenSquare.Tasks.T06.SparseColumn55
import ElevenSquare.Tasks.T06.SparseColumn57

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix091 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix091_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = branchIntegerMatrix091 := by
  change roundedGradients ∘ branchRows 91 = branchIntegerMatrix091
  rw [show branchRows 91 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 54, 55, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix091]

theorem branchColumn091_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 0) i) = _
  rw [branchColumn091_0]
  exact sparseColumn00_sum n

theorem branchColumn091_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 1) i) = _
  rw [branchColumn091_1]
  exact sparseColumn01_sum n

theorem branchColumn091_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 2) i) = _
  rw [branchColumn091_2]
  exact sparseColumn02_sum n

theorem branchColumn091_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 3) i) = _
  rw [branchColumn091_3]
  exact sparseColumn03_sum n

theorem branchColumn091_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 4) i) = _
  rw [branchColumn091_4]
  exact sparseColumn04_sum n

theorem branchColumn091_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 5) i) = _
  rw [branchColumn091_5]
  exact sparseColumn05_sum n

theorem branchColumn091_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 6) i) = _
  rw [branchColumn091_6]
  exact sparseColumn06_sum n

theorem branchColumn091_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 7) i) = _
  rw [branchColumn091_7]
  exact sparseColumn07_sum n

theorem branchColumn091_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 8) i) = _
  rw [branchColumn091_8]
  exact sparseColumn08_sum n

theorem branchColumn091_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 9) i) = _
  rw [branchColumn091_9]
  exact sparseColumn09_sum n

theorem branchColumn091_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 10) i) = _
  rw [branchColumn091_10]
  exact sparseColumn10_sum n

theorem branchColumn091_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 11) i) = _
  rw [branchColumn091_11]
  exact sparseColumn11_sum n

theorem branchColumn091_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 12) i) = _
  rw [branchColumn091_12]
  exact sparseColumn35_sum n

theorem branchColumn091_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 13) i) = _
  rw [branchColumn091_13]
  exact sparseColumn36_sum n

theorem branchColumn091_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 14) i) = _
  rw [branchColumn091_14]
  exact sparseColumn41_sum n

theorem branchColumn091_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 15) i) = _
  rw [branchColumn091_15]
  exact sparseColumn38_sum n

theorem branchColumn091_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 16) i) = _
  rw [branchColumn091_16]
  exact sparseColumn39_sum n

theorem branchColumn091_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 17) i) = _
  rw [branchColumn091_17]
  exact sparseColumn17_sum n

theorem branchColumn091_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 18) i) = _
  rw [branchColumn091_18]
  exact sparseColumn18_sum n

theorem branchColumn091_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 19) i) = _
  rw [branchColumn091_19]
  exact sparseColumn19_sum n

theorem branchColumn091_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 20) = sparseColumn55 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 20) = sparseDot55 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 20) i) = _
  rw [branchColumn091_20]
  exact sparseColumn55_sum n

theorem branchColumn091_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 21) i) = _
  rw [branchColumn091_21]
  exact sparseColumn21_sum n

theorem branchColumn091_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 22) i) = _
  rw [branchColumn091_22]
  exact sparseColumn22_sum n

theorem branchColumn091_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 23) = sparseColumn47 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 23) = sparseDot47 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 23) i) = _
  rw [branchColumn091_23]
  exact sparseColumn47_sum n

theorem branchColumn091_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 24) i) = _
  rw [branchColumn091_24]
  exact sparseColumn24_sum n

theorem branchColumn091_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 25) i) = _
  rw [branchColumn091_25]
  exact sparseColumn25_sum n

theorem branchColumn091_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 26) = sparseColumn57 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 26) = sparseDot57 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 26) i) = _
  rw [branchColumn091_26]
  exact sparseColumn57_sum n

theorem branchColumn091_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 27) i) = _
  rw [branchColumn091_27]
  exact sparseColumn27_sum n

theorem branchColumn091_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 28) i) = _
  rw [branchColumn091_28]
  exact sparseColumn28_sum n

theorem branchColumn091_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 29) = sparseColumn50 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 29) = sparseDot50 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 29) i) = _
  rw [branchColumn091_29]
  exact sparseColumn50_sum n

theorem branchColumn091_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 30) i) = _
  rw [branchColumn091_30]
  exact sparseColumn30_sum n

theorem branchColumn091_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 31) i) = _
  rw [branchColumn091_31]
  exact sparseColumn31_sum n

theorem branchColumn091_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 91 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 91 i)) = _
  rw [branchIntegerMatrix091_eq]
  simp only [branchIntegerMatrix091, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot091_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 91 i) 32) i) = _
  rw [branchColumn091_32]
  exact sparseColumn32_sum n

def branchSparseDots091 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot55, sparseDot21, sparseDot22, sparseDot47, sparseDot24, sparseDot25, sparseDot57, sparseDot27, sparseDot28, sparseDot50, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot091_0 :
    branchSparseDots091 0 = sparseDot00 := rfl

private theorem branchSparseDot091_1 :
    branchSparseDots091 1 = sparseDot01 := rfl

private theorem branchSparseDot091_2 :
    branchSparseDots091 2 = sparseDot02 := rfl

private theorem branchSparseDot091_3 :
    branchSparseDots091 3 = sparseDot03 := rfl

private theorem branchSparseDot091_4 :
    branchSparseDots091 4 = sparseDot04 := rfl

private theorem branchSparseDot091_5 :
    branchSparseDots091 5 = sparseDot05 := rfl

private theorem branchSparseDot091_6 :
    branchSparseDots091 6 = sparseDot06 := rfl

private theorem branchSparseDot091_7 :
    branchSparseDots091 7 = sparseDot07 := rfl

private theorem branchSparseDot091_8 :
    branchSparseDots091 8 = sparseDot08 := rfl

private theorem branchSparseDot091_9 :
    branchSparseDots091 9 = sparseDot09 := rfl

private theorem branchSparseDot091_10 :
    branchSparseDots091 10 = sparseDot10 := rfl

private theorem branchSparseDot091_11 :
    branchSparseDots091 11 = sparseDot11 := rfl

private theorem branchSparseDot091_12 :
    branchSparseDots091 12 = sparseDot35 := rfl

private theorem branchSparseDot091_13 :
    branchSparseDots091 13 = sparseDot36 := rfl

private theorem branchSparseDot091_14 :
    branchSparseDots091 14 = sparseDot41 := rfl

private theorem branchSparseDot091_15 :
    branchSparseDots091 15 = sparseDot38 := rfl

private theorem branchSparseDot091_16 :
    branchSparseDots091 16 = sparseDot39 := rfl

private theorem branchSparseDot091_17 :
    branchSparseDots091 17 = sparseDot17 := rfl

private theorem branchSparseDot091_18 :
    branchSparseDots091 18 = sparseDot18 := rfl

private theorem branchSparseDot091_19 :
    branchSparseDots091 19 = sparseDot19 := rfl

private theorem branchSparseDot091_20 :
    branchSparseDots091 20 = sparseDot55 := rfl

private theorem branchSparseDot091_21 :
    branchSparseDots091 21 = sparseDot21 := rfl

private theorem branchSparseDot091_22 :
    branchSparseDots091 22 = sparseDot22 := rfl

private theorem branchSparseDot091_23 :
    branchSparseDots091 23 = sparseDot47 := rfl

private theorem branchSparseDot091_24 :
    branchSparseDots091 24 = sparseDot24 := rfl

private theorem branchSparseDot091_25 :
    branchSparseDots091 25 = sparseDot25 := rfl

private theorem branchSparseDot091_26 :
    branchSparseDots091 26 = sparseDot57 := rfl

private theorem branchSparseDot091_27 :
    branchSparseDots091 27 = sparseDot27 := rfl

private theorem branchSparseDot091_28 :
    branchSparseDots091 28 = sparseDot28 := rfl

private theorem branchSparseDot091_29 :
    branchSparseDots091 29 = sparseDot50 := rfl

private theorem branchSparseDot091_30 :
    branchSparseDots091 30 = sparseDot30 := rfl

private theorem branchSparseDot091_31 :
    branchSparseDots091 31 = sparseDot31 := rfl

private theorem branchSparseDot091_32 :
    branchSparseDots091 32 = sparseDot32 := rfl

theorem branchDots091 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 91 i) k) = branchSparseDots091 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot091_0 n
      _ = _ := congrFun branchSparseDot091_0.symm n
  · calc
      _ = sparseDot01 n := branchDot091_1 n
      _ = _ := congrFun branchSparseDot091_1.symm n
  · calc
      _ = sparseDot02 n := branchDot091_2 n
      _ = _ := congrFun branchSparseDot091_2.symm n
  · calc
      _ = sparseDot03 n := branchDot091_3 n
      _ = _ := congrFun branchSparseDot091_3.symm n
  · calc
      _ = sparseDot04 n := branchDot091_4 n
      _ = _ := congrFun branchSparseDot091_4.symm n
  · calc
      _ = sparseDot05 n := branchDot091_5 n
      _ = _ := congrFun branchSparseDot091_5.symm n
  · calc
      _ = sparseDot06 n := branchDot091_6 n
      _ = _ := congrFun branchSparseDot091_6.symm n
  · calc
      _ = sparseDot07 n := branchDot091_7 n
      _ = _ := congrFun branchSparseDot091_7.symm n
  · calc
      _ = sparseDot08 n := branchDot091_8 n
      _ = _ := congrFun branchSparseDot091_8.symm n
  · calc
      _ = sparseDot09 n := branchDot091_9 n
      _ = _ := congrFun branchSparseDot091_9.symm n
  · calc
      _ = sparseDot10 n := branchDot091_10 n
      _ = _ := congrFun branchSparseDot091_10.symm n
  · calc
      _ = sparseDot11 n := branchDot091_11 n
      _ = _ := congrFun branchSparseDot091_11.symm n
  · calc
      _ = sparseDot35 n := branchDot091_12 n
      _ = _ := congrFun branchSparseDot091_12.symm n
  · calc
      _ = sparseDot36 n := branchDot091_13 n
      _ = _ := congrFun branchSparseDot091_13.symm n
  · calc
      _ = sparseDot41 n := branchDot091_14 n
      _ = _ := congrFun branchSparseDot091_14.symm n
  · calc
      _ = sparseDot38 n := branchDot091_15 n
      _ = _ := congrFun branchSparseDot091_15.symm n
  · calc
      _ = sparseDot39 n := branchDot091_16 n
      _ = _ := congrFun branchSparseDot091_16.symm n
  · calc
      _ = sparseDot17 n := branchDot091_17 n
      _ = _ := congrFun branchSparseDot091_17.symm n
  · calc
      _ = sparseDot18 n := branchDot091_18 n
      _ = _ := congrFun branchSparseDot091_18.symm n
  · calc
      _ = sparseDot19 n := branchDot091_19 n
      _ = _ := congrFun branchSparseDot091_19.symm n
  · calc
      _ = sparseDot55 n := branchDot091_20 n
      _ = _ := congrFun branchSparseDot091_20.symm n
  · calc
      _ = sparseDot21 n := branchDot091_21 n
      _ = _ := congrFun branchSparseDot091_21.symm n
  · calc
      _ = sparseDot22 n := branchDot091_22 n
      _ = _ := congrFun branchSparseDot091_22.symm n
  · calc
      _ = sparseDot47 n := branchDot091_23 n
      _ = _ := congrFun branchSparseDot091_23.symm n
  · calc
      _ = sparseDot24 n := branchDot091_24 n
      _ = _ := congrFun branchSparseDot091_24.symm n
  · calc
      _ = sparseDot25 n := branchDot091_25 n
      _ = _ := congrFun branchSparseDot091_25.symm n
  · calc
      _ = sparseDot57 n := branchDot091_26 n
      _ = _ := congrFun branchSparseDot091_26.symm n
  · calc
      _ = sparseDot27 n := branchDot091_27 n
      _ = _ := congrFun branchSparseDot091_27.symm n
  · calc
      _ = sparseDot28 n := branchDot091_28 n
      _ = _ := congrFun branchSparseDot091_28.symm n
  · calc
      _ = sparseDot50 n := branchDot091_29 n
      _ = _ := congrFun branchSparseDot091_29.symm n
  · calc
      _ = sparseDot30 n := branchDot091_30 n
      _ = _ := congrFun branchSparseDot091_30.symm n
  · calc
      _ = sparseDot31 n := branchDot091_31 n
      _ = _ := congrFun branchSparseDot091_31.symm n
  · calc
      _ = sparseDot32 n := branchDot091_32 n
      _ = _ := congrFun branchSparseDot091_32.symm n

def branchIntegerCurvature091 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101981296, 101981296, 79086693, 79086693, 106371291, 106371291, 88123140, 88123140, 204734428, 204734428]

theorem branchIntegerCurvature091_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 91 i)) = branchIntegerCurvature091 := by
  change curvatureNumerators ∘ branchRows 91 = branchIntegerCurvature091
  rw [show branchRows 91 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 54, 55, 50, 51, 48, 49, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature091_entry (i : Fin 42) :
    curvatureNumerators (branchRows 91 i) = branchIntegerCurvature091 i :=
  congrFun branchIntegerCurvature091_eq i

def branchResiduals091 : Fin 33 → Fin 2 → ℕ := ![![1297716749512534, 33000000000000], ![1544142352688614, 33000000000000], ![1582373852669008, 1336679166854766], ![33000000000000, 1022757033455086], ![854774597750774, 33000000000000], ![1055303820412363, 893860909105151], ![721314166788627, 624798065222648], ![33000000000000, 762495766309350], ![1579326946298457, 1126678081953160], ![1024237765700705, 33000000000000], ![33000000000000, 777632019678618], ![506746491309072, 465540643623192], ![988836078266203, 66000000000000], ![33000000000000, 857512920319029], ![1055264082615963, 485898469939739], ![471567081660068, 33000000000000], ![66000000000000, 744121016473193], ![659291282162355, 464361203778556], ![620200547757655, 265854275997260], ![631206309063686, 511523664210544], ![1474857131414287, 854833127134258], ![750685570138465, 375215540078376], ![470960609320769, 90706651221511], ![1474857131414287, 854833127134258], ![669804609154668, 230374054719026], ![508381601136753, 218713669397988], ![398805840068707, 854833127134258], ![409060239811991, 545830869935804], ![285044621435502, 299207140313493], ![398805840068707, 891378403766055], ![212642981664919, 550827554714890], ![1680150457817014, 648710695287693], ![1330753307417293, 2885659800450397]]

theorem branchResiduals091_eq : residualNumerators 91 = branchResiduals091 := rfl

theorem integerCheck091_0_0 :
    integerResidualCheck 91 0 0 (dualNumerators091 0 0) ∧
    integerMassCheck 91 0 0 (dualNumerators091 0 0) := by
  apply integerChecks_of_simple 91 0 0 (dualNumerators091 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1452036338470, 721009985597, 1308901425339, 0, 601145163368, 1234047382517, 1330333654477, 636679939507, 1430871029972, 404321515913]) (branchResiduals091 0 0) 18767167
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck091_0_1 :
    integerResidualCheck 91 0 1 (dualNumerators091 0 1) ∧
    integerMassCheck 91 0 1 (dualNumerators091 0 1) := by
  apply integerChecks_of_simple 91 0 1 (dualNumerators091 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals091 0 1) 18767167
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck091_1_0 :
    integerResidualCheck 91 1 0 (dualNumerators091 1 0) ∧
    integerMassCheck 91 1 0 (dualNumerators091 1 0) := by
  apply integerChecks_of_simple 91 1 0 (dualNumerators091 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 1719352138172, 853745892948, 1549866490727, 0, 711814294591, 1461232029476, 1575244332878, 753890922920, 1694290356000, 478755968067]) (branchResiduals091 1 0) 22176635
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck091_1_1 :
    integerResidualCheck 91 1 1 (dualNumerators091 1 1) ∧
    integerMassCheck 91 1 1 (dualNumerators091 1 1) := by
  apply integerChecks_of_simple 91 1 1 (dualNumerators091 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals091 1 1) 22176635
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck091_2_0 :
    integerResidualCheck 91 2 0 (dualNumerators091 2 0) ∧
    integerMassCheck 91 2 0 (dualNumerators091 2 0) := by
  apply integerChecks_of_simple 91 2 0 (dualNumerators091 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 1719352138173, 853745892949, 1549866490728, 0, 711814294592, 1461232029477, 1575244332879, 753890922921, 1694290356001, 478755968068]) (branchResiduals091 2 0) 22681452
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck091_2_1 :
    integerResidualCheck 91 2 1 (dualNumerators091 2 1) ∧
    integerMassCheck 91 2 1 (dualNumerators091 2 1) := by
  apply integerChecks_of_simple 91 2 1 (dualNumerators091 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1452036338469, 721009985597, 1308901425338, 0, 601145163368, 1234047382516, 1330333654476, 636679939507, 1430871029971, 404321515912]) (branchResiduals091 2 1) 22681452
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck091_3_0 :
    integerResidualCheck 91 3 0 (dualNumerators091 3 0) ∧
    integerMassCheck 91 3 0 (dualNumerators091 3 0) := by
  apply integerChecks_of_simple 91 3 0 (dualNumerators091 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals091 3 0) 16360330
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck091_3_1 :
    integerResidualCheck 91 3 1 (dualNumerators091 3 1) ∧
    integerMassCheck 91 3 1 (dualNumerators091 3 1) := by
  apply integerChecks_of_simple 91 3 1 (dualNumerators091 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000001, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000001, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1144101124261, 568104470439, 1031321016287, 0, 473659535255, 972341366619, 1048208085022, 501658405706, 1127424369963, 318576531911]) (branchResiduals091 3 1) 16360330
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck091_4_0 :
    integerResidualCheck 91 4 0 (dualNumerators091 4 0) ∧
    integerMassCheck 91 4 0 (dualNumerators091 4 0) := by
  apply integerChecks_of_simple 91 4 0 (dualNumerators091 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000001, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 966222317365, 479778584509, 870976665588, 0, 400017449587, 821166860693, 885238221966, 423663203373, 952138376845, 269045933435]) (branchResiduals091 4 0) 13760362
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck091_4_1 :
    integerResidualCheck 91 4 1 (dualNumerators091 4 1) ∧
    integerMassCheck 91 4 1 (dualNumerators091 4 1) := by
  apply integerChecks_of_simple 91 4 1 (dualNumerators091 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals091 4 1) 13760362
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck091_5_0 :
    integerResidualCheck 91 5 0 (dualNumerators091 5 0) ∧
    integerMassCheck 91 5 0 (dualNumerators091 5 0) := by
  apply integerChecks_of_simple 91 5 0 (dualNumerators091 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1144101124262, 568104470440, 1031321016288, 0, 473659535256, 972341366620, 1048208085022, 501658405707, 1127424369964, 318576531911]) (branchResiduals091 5 0) 17641130
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck091_5_1 :
    integerResidualCheck 91 5 1 (dualNumerators091 5 1) ∧
    integerMassCheck 91 5 1 (dualNumerators091 5 1) := by
  apply integerChecks_of_simple 91 5 1 (dualNumerators091 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 966222317364, 479778584509, 870976665588, 0, 400017449587, 821166860692, 885238221966, 423663203373, 952138376844, 269045933435]) (branchResiduals091 5 1) 17641130
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck091_6_0 :
    integerResidualCheck 91 6 0 (dualNumerators091 6 0) ∧
    integerMassCheck 91 6 0 (dualNumerators091 6 0) := by
  apply integerChecks_of_simple 91 6 0 (dualNumerators091 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 877488274356, 957704271528, 2719950702, 106626845062, 1430871029972, 404321515913]) (branchResiduals091 6 0) 8962451
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck091_6_1 :
    integerResidualCheck 91 6 1 (dualNumerators091 6 1) ∧
    integerMassCheck 91 6 1 (dualNumerators091 6 1) := by
  apply integerChecks_of_simple 91 6 1 (dualNumerators091 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals091 6 1) 8962451
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck091_7_0 :
    integerResidualCheck 91 7 0 (dualNumerators091 7 0) ∧
    integerMassCheck 91 7 0 (dualNumerators091 7 0) := by
  apply integerChecks_of_simple 91 7 0 (dualNumerators091 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals091 7 0) 10424794
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck091_7_1 :
    integerResidualCheck 91 7 1 (dualNumerators091 7 1) ∧
    integerMassCheck 91 7 1 (dualNumerators091 7 1) := by
  apply integerChecks_of_simple 91 7 1 (dualNumerators091 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 859676069088, 426872946475, 774933245365, 0, 355907147296, 730616014740, 787622166441, 376945461461, 847145178002, 239377984034]) (branchResiduals091 7 1) 10424794
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck091_8_0 :
    integerResidualCheck 91 8 0 (dualNumerators091 8 0) ∧
    integerMassCheck 91 8 0 (dualNumerators091 8 0) := by
  apply integerChecks_of_simple 91 8 0 (dualNumerators091 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 1719352138175, 853745892950, 1549866490730, 0, 711814294592, 1461232029479, 1575244332881, 753890922921, 1694290356003, 478755968068]) (branchResiduals091 8 0) 22681452
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck091_8_1 :
    integerResidualCheck 91 8 1 (dualNumerators091 8 1) ∧
    integerMassCheck 91 8 1 (dualNumerators091 8 1) := by
  apply integerChecks_of_simple 91 8 1 (dualNumerators091 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1226281389033, 608911156849, 1105400337063, 0, 507682284813, 1042184205913, 1123500396284, 537692301428, 1208406751039, 341459739686]) (branchResiduals091 8 1) 22681452
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck091_9_0 :
    integerResidualCheck 91 9 0 (dualNumerators091 9 0) ∧
    integerMassCheck 91 9 0 (dualNumerators091 9 0) := by
  apply integerChecks_of_simple 91 9 0 (dualNumerators091 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 1144101124261, 568104470439, 1031321016287, 0, 473659535255, 972341366619, 1048208085022, 501658405706, 1127424369963, 318576531911]) (branchResiduals091 9 0) 16350530
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck091_9_1 :
    integerResidualCheck 91 9 1 (dualNumerators091 9 1) ∧
    integerMassCheck 91 9 1 (dualNumerators091 9 1) := by
  apply integerChecks_of_simple 91 9 1 (dualNumerators091 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals091 9 1) 16350530
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck091_10_0 :
    integerResidualCheck 91 10 0 (dualNumerators091 10 0) ∧
    integerMassCheck 91 10 0 (dualNumerators091 10 0) := by
  apply integerChecks_of_simple 91 10 0 (dualNumerators091 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals091 10 0) 10683139
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck091_10_1 :
    integerResidualCheck 91 10 1 (dualNumerators091 10 1) ∧
    integerMassCheck 91 10 1 (dualNumerators091 10 1) := by
  apply integerChecks_of_simple 91 10 1 (dualNumerators091 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 874612019090, 434289406250, 788396879662, 0, 362090652396, 743309684668, 801306257136, 383494484713, 861863417206, 243536919859]) (branchResiduals091 10 1) 10683139
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck091_11_0 :
    integerResidualCheck 91 11 0 (dualNumerators091 11 0) ∧
    integerMassCheck 91 11 0 (dualNumerators091 11 0) := by
  apply integerChecks_of_simple 91 11 0 (dualNumerators091 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 543582099984, 269916194035, 489998333105, 0, 225043782750, 461976088268, 498021669583, 238346527126, 535658687508, 151361183509]) (branchResiduals091 11 0) 15120968
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck091_11_1 :
    integerResidualCheck 91 11 1 (dualNumerators091 11 1) ∧
    integerMassCheck 91 11 1 (dualNumerators091 11 1) := by
  apply integerChecks_of_simple 91 11 1 (dualNumerators091 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 495684390637, 246132542200, 446822154676, 0, 205214061173, 421269088530, 454138515265, 217344634900, 488459149252, 138024000452]) (branchResiduals091 11 1) 15120968
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck091_12_0 :
    integerResidualCheck 91 12 0 (dualNumerators091 12 0) ∧
    integerMassCheck 91 12 0 (dualNumerators091 12 0) := by
  apply integerChecks_of_simple 91 12 0 (dualNumerators091 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1144101124261, 568104470439, 1031321016287, 0, 473659535255, 972341366619, 1048208085022, 501658405706, 1127424369963, 318576531911]) (branchResiduals091 12 0) 16348076
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck091_12_1 :
    integerResidualCheck 91 12 1 (dualNumerators091 12 1) ∧
    integerMassCheck 91 12 1 (dualNumerators091 12 1) := by
  apply integerChecks_of_simple 91 12 1 (dualNumerators091 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals091 12 1) 16348076
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck091_13_0 :
    integerResidualCheck 91 13 0 (dualNumerators091 13 0) ∧
    integerMassCheck 91 13 0 (dualNumerators091 13 0) := by
  apply integerChecks_of_simple 91 13 0 (dualNumerators091 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals091 13 0) 13962901
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck091_13_1 :
    integerResidualCheck 91 13 1 (dualNumerators091 13 1) ∧
    integerMassCheck 91 13 1 (dualNumerators091 13 1) := by
  apply integerChecks_of_simple 91 13 1 (dualNumerators091 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 966222317365, 479778584509, 870976665588, 0, 400017449587, 821166860693, 885238221966, 423663203373, 952138376845, 269045933435]) (branchResiduals091 13 1) 13962901
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck091_14_0 :
    integerResidualCheck 91 14 0 (dualNumerators091 14 0) ∧
    integerMassCheck 91 14 0 (dualNumerators091 14 0) := by
  apply integerChecks_of_simple 91 14 0 (dualNumerators091 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1144101124262, 568104470440, 1031321016288, 0, 473659535256, 972341366620, 1048208085022, 501658405707, 1127424369964, 318576531911]) (branchResiduals091 14 0) 20161291
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck091_14_1 :
    integerResidualCheck 91 14 1 (dualNumerators091 14 1) ∧
    integerMassCheck 91 14 1 (dualNumerators091 14 1) := by
  apply integerChecks_of_simple 91 14 1 (dualNumerators091 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 523832516750, 260109520231, 472195570901, 0, 216867426466, 445191438428, 479927401181, 229686851658, 516196980004, 145861884889]) (branchResiduals091 14 1) 20161291
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck091_15_0 :
    integerResidualCheck 91 15 0 (dualNumerators091 15 0) ∧
    integerMassCheck 91 15 0 (dualNumerators091 15 0) := by
  apply integerChecks_of_simple 91 15 0 (dualNumerators091 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 543582099984, 269916194035, 489998333105, 0, 225043782750, 461976088267, 498021669583, 238346527126, 535658687508, 151361183509]) (branchResiduals091 15 0) 12900283
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck091_15_1 :
    integerResidualCheck 91 15 1 (dualNumerators091 15 1) ∧
    integerMassCheck 91 15 1 (dualNumerators091 15 1) := by
  apply integerChecks_of_simple 91 15 1 (dualNumerators091 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals091 15 1) 12900283
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck091_16_0 :
    integerResidualCheck 91 16 0 (dualNumerators091 16 0) ∧
    integerMassCheck 91 16 0 (dualNumerators091 16 0) := by
  apply integerChecks_of_simple 91 16 0 (dualNumerators091 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals091 16 0) 10683060
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck091_16_1 :
    integerResidualCheck 91 16 1 (dualNumerators091 16 1) ∧
    integerMassCheck 91 16 1 (dualNumerators091 16 1) := by
  apply integerChecks_of_simple 91 16 1 (dualNumerators091 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 874612019090, 434289406250, 788396879662, 0, 362090652396, 743309684668, 801306257136, 383494484713, 861863417206, 243536919859]) (branchResiduals091 16 1) 10683060
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck091_17_0 :
    integerResidualCheck 91 17 0 (dualNumerators091 17 0) ∧
    integerMassCheck 91 17 0 (dualNumerators091 17 0) := by
  apply integerChecks_of_simple 91 17 0 (dualNumerators091 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 712949339994, 354015653563, 642670147151, 0, 295162067305, 605916838014, 653193364245, 312609630099, 702557180842, 198521724476]) (branchResiduals091 17 0) 15120968
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck091_17_1 :
    integerResidualCheck 91 17 1 (dualNumerators091 17 1) ∧
    integerMassCheck 91 17 1 (dualNumerators091 17 1) := by
  apply integerChecks_of_simple 91 17 1 (dualNumerators091 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 495684390637, 246132542200, 446822154676, 0, 205214061173, 421269088530, 454138515265, 217344634900, 488459149252, 138024000452]) (branchResiduals091 17 1) 15120968
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck091_18_0 :
    integerResidualCheck 91 18 0 (dualNumerators091 18 0) ∧
    integerMassCheck 91 18 0 (dualNumerators091 18 0) := by
  apply integerChecks_of_simple 91 18 0 (dualNumerators091 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 934970696450, 333426002978, 763999473637, 0, 263461482107, 807731590141, 772489965679, 214059593984, 835192545885, 236000526363]) (branchResiduals091 18 0) 13565580
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck091_18_1 :
    integerResidualCheck 91 18 1 (dualNumerators091 18 1) ∧
    integerMassCheck 91 18 1 (dualNumerators091 18 1) := by
  apply integerChecks_of_simple 91 18 1 (dualNumerators091 18 1)
    (![552774353318, 101764201348, 552774353318, 0, 1, 194169418432, 229915461414, 0, 83885421775, 59829007246, 194169418432, 0, 94926637302, 515633295911, 229915461414, 0, 0, 515633295912, 201500008915, 170171850577, 856726447141, 300936675152, 92726973504, 109797748126, 194169418432, 0, 94926637302, 515633295911, 0, 0, 300936675152, 799162766836, 15443069854, 138502830895, 92726973504, 0, 130011204269, 0, 98264701746, 202671973406, 101367709986, 28643494283]) (branchResiduals091 18 1) 13565580
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck091_19_0 :
    integerResidualCheck 91 19 0 (dualNumerators091 19 0) ∧
    integerMassCheck 91 19 0 (dualNumerators091 19 0) := by
  apply integerChecks_of_simple 91 19 0 (dualNumerators091 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 875874933151, 195318139098, 645216866088, 0, 136231332822, 768418291818, 648421029826, 25293932239, 705341215054, 199308409586]) (branchResiduals091 19 0) 8248658
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck091_19_1 :
    integerResidualCheck 91 19 1 (dualNumerators091 19 1) ∧
    integerMassCheck 91 19 1 (dualNumerators091 19 1) := by
  apply integerChecks_of_simple 91 19 1 (dualNumerators091 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 350406455885, 413593017753, 460183470977, 0, 371450951992, 273765914097, 475079366460, 512398369190, 503065535987, 142151330101]) (branchResiduals091 19 1) 8248658
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck091_20_0 :
    integerResidualCheck 91 20 0 (dualNumerators091 20 0) ∧
    integerMassCheck 91 20 0 (dualNumerators091 20 0) := by
  apply integerChecks_of_simple 91 20 0 (dualNumerators091 20 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 176645531640, 1584264425996, 1060657349048, 0, 1487132967409, 0, 1124000645334, 2318263067540, 1159494400494, 327638566915]) (branchResiduals091 20 0) 35312013
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck091_20_1 :
    integerResidualCheck 91 20 1 (dualNumerators091 20 1) ∧
    integerMassCheck 91 20 1 (dualNumerators091 20 1) := by
  apply integerChecks_of_simple 91 20 1 (dualNumerators091 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals091 20 1) 35312013
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck091_21_0 :
    integerResidualCheck 91 21 0 (dualNumerators091 21 0) ∧
    integerMassCheck 91 21 0 (dualNumerators091 21 0) := by
  apply integerChecks_of_simple 91 21 0 (dualNumerators091 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 759767979803, 549133445537, 757887471419, 892563449519, 1020530044549, 288371380791]) (branchResiduals091 21 0) 11182451
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck091_21_1 :
    integerResidualCheck 91 21 1 (dualNumerators091 21 1) ∧
    integerMassCheck 91 21 1 (dualNumerators091 21 1) := by
  apply integerChecks_of_simple 91 21 1 (dualNumerators091 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 860003851037, 963321782180, 3460174706, 161253783489, 102979506989, 127963650709, 0, 0, 180062781238, 50880376460]) (branchResiduals091 21 1) 11182451
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck091_22_0 :
    integerResidualCheck 91 22 0 (dualNumerators091 22 0) ∧
    integerMassCheck 91 22 0 (dualNumerators091 22 0) := by
  apply integerChecks_of_simple 91 22 0 (dualNumerators091 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 136031845564, 627967628074, 85708482881, 374474988096, 645216866088, 0, 95974191249, 705361889470, 503065535987, 142151330101]) (branchResiduals091 22 0) 6465674
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck091_22_1 :
    integerResidualCheck 91 22 1 (dualNumerators091 22 1) ∧
    integerMassCheck 91 22 1 (dualNumerators091 22 1) := by
  apply integerChecks_of_simple 91 22 1 (dualNumerators091 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 9522456419, 111749239332, 1534493418, 71511669319, 45668611868, 56748400418, 0, 0, 79852948501, 22564063785]) (branchResiduals091 22 1) 6465674
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck091_23_0 :
    integerResidualCheck 91 23 0 (dualNumerators091 23 0) ∧
    integerMassCheck 91 23 0 (dualNumerators091 23 0) := by
  apply integerChecks_of_simple 91 23 0 (dualNumerators091 23 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 1176645531640, 584264425996, 1060657349048, 0, 1487132967409, 0, 1124000645334, 2318263067540, 1159494400494, 327638566915]) (branchResiduals091 23 0) 35297932
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck091_23_1 :
    integerResidualCheck 91 23 1 (dualNumerators091 23 1) ∧
    integerMassCheck 91 23 1 (dualNumerators091 23 1) := by
  apply integerChecks_of_simple 91 23 1 (dualNumerators091 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 160334187224, 1881575790198, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals091 23 1) 35297932
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck091_24_0 :
    integerResidualCheck 91 24 0 (dualNumerators091 24 0) ∧
    integerMassCheck 91 24 0 (dualNumerators091 24 0) := by
  apply integerChecks_of_simple 91 24 0 (dualNumerators091 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 512185690040, 559007382209, 705016048726, 601815130180, 835192545885, 236000526363]) (branchResiduals091 24 0) 9356857
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck091_24_1 :
    integerResidualCheck 91 24 1 (dualNumerators091 24 1) ∧
    integerMassCheck 91 24 1 (dualNumerators091 24 1) := by
  apply integerChecks_of_simple 91 24 1 (dualNumerators091 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 690777049383, 178822020994, 66021086067, 82038644814, 0, 0, 115439864933, 32619865948]) (branchResiduals091 24 1) 9356857
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck091_25_0 :
    integerResidualCheck 91 25 0 (dualNumerators091 25 0) ∧
    integerMassCheck 91 25 0 (dualNumerators091 25 0) := by
  apply integerChecks_of_simple 91 25 0 (dualNumerators091 25 0)
    (![34966365041, 6437209308, 34966365041, 0, 1, 22997469043, 27231238312, 0, 632721051475, 451271169324, 515942815115, 0, 137926201422, 749203214751, 610926434029, 0, 0, 749203214752, 1519850467647, 1283552135172, 54193197479, 35643006641, 699410063567, 828169486116, 515942815115, 0, 137926201422, 749203214751, 0, 0, 799642480277, 1161164957288, 639671999392, 521492957897, 54193197479, 0, 457443319543, 523189836115, 0, 35643006641, 764584390126, 216048765531]) (branchResiduals091 25 0) 8671199
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck091_25_1 :
    integerResidualCheck 91 25 1 (dualNumerators091 25 1) ∧
    integerMassCheck 91 25 1 (dualNumerators091 25 1) := by
  apply integerChecks_of_simple 91 25 1 (dualNumerators091 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals091 25 1) 8671199
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck091_26_0 :
    integerResidualCheck 91 26 0 (dualNumerators091 26 0) ∧
    integerMassCheck 91 26 0 (dualNumerators091 26 0) := by
  apply integerChecks_of_simple 91 26 0 (dualNumerators091 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals091 26 0) 15099566
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck091_26_1 :
    integerResidualCheck 91 26 1 (dualNumerators091 26 1) ∧
    integerMassCheck 91 26 1 (dualNumerators091 26 1) := by
  apply integerChecks_of_simple 91 26 1 (dualNumerators091 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 1025837005087, 204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals091 26 1) 15099566
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck091_27_0 :
    integerResidualCheck 91 27 0 (dualNumerators091 27 0) ∧
    integerMassCheck 91 27 0 (dualNumerators091 27 0) := by
  apply integerChecks_of_simple 91 27 0 (dualNumerators091 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 436855949686, 304617712691, 595678484088, 168320989550]) (branchResiduals091 27 0) 7338775
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck091_27_1 :
    integerResidualCheck 91 27 1 (dualNumerators091 27 1) ∧
    integerMassCheck 91 27 1 (dualNumerators091 27 1) := by
  apply integerChecks_of_simple 91 27 1 (dualNumerators091 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 908602750628, 623335190581, 377837583379, 0, 538833784902, 754926527212, 385949753226, 259267112862, 413046270426, 116714568052]) (branchResiduals091 27 1) 7338775
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck091_28_0 :
    integerResidualCheck 91 28 0 (dualNumerators091 28 0) ∧
    integerMassCheck 91 28 0 (dualNumerators091 28 0) := by
  apply integerChecks_of_simple 91 28 0 (dualNumerators091 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 374399059503, 471423145846, 503065535987, 142151330101]) (branchResiduals091 28 0) 10335557
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck091_28_1 :
    integerResidualCheck 91 28 1 (dualNumerators091 28 1) ∧
    integerMassCheck 91 28 1 (dualNumerators091 28 1) := by
  apply integerChecks_of_simple 91 28 1 (dualNumerators091 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 426731607120, 507685338329, 2156352207, 100492021777, 456143077212, 332995651238, 0, 0, 112213633330, 31708229033]) (branchResiduals091 28 1) 10335557
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck091_29_0 :
    integerResidualCheck 91 29 0 (dualNumerators091 29 0) ∧
    integerMassCheck 91 29 0 (dualNumerators091 29 0) := by
  apply integerChecks_of_simple 91 29 0 (dualNumerators091 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals091 29 0) 40352153
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck091_29_1 :
    integerResidualCheck 91 29 1 (dualNumerators091 29 1) ∧
    integerMassCheck 91 29 1 (dualNumerators091 29 1) := by
  apply integerChecks_of_simple 91 29 1 (dualNumerators091 29 1)
    (![813650000253, 149790673094, 813650000253, 0, 1, 30189853607, 35747720615, 0, 1140807387415, 813650000252, 30189853607, 0, 248683411329, 1350826813920, 35747720615, 0, 0, 1350826813921, 2740317612662, 2314267487267, 1261048870572, 46790242466, 1261048870572, 1493204415423, 30189853607, 0, 248683411329, 1350826813920, 0, 0, 46790242466, 2093601213671, 210019426506, 1883581787165, 72117429420, 1188931441153, 1768099142126, 0, 46790242466, 0, 1378559348588, 389539793539]) (branchResiduals091 29 1) 40352153
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck091_30_0 :
    integerResidualCheck 91 30 0 (dualNumerators091 30 0) ∧
    integerMassCheck 91 30 0 (dualNumerators091 30 0) := by
  apply integerChecks_of_simple 91 30 0 (dualNumerators091 30 0)
    (![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 115599349926, 0, 37915592376, 205954223378, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 0, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 199771188218, 119430361220, 178745918050, 13520283734, 101823264420, 167750512114, 179163558800, 0, 269573776534, 0]) (branchResiduals091 30 0) 7680628
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck091_30_1 :
    integerResidualCheck 91 30 1 (dualNumerators091 30 1) ∧
    integerMassCheck 91 30 1 (dualNumerators091 30 1) := by
  apply integerChecks_of_simple 91 30 1 (dualNumerators091 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 604489703699, 300159920941, 544901951702, 0, 250259619582, 513739854055, 556554858415, 372095930671, 536287180313, 227712293325]) (branchResiduals091 30 1) 7680628
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck091_31_0 :
    integerResidualCheck 91 31 0 (dualNumerators091 31 0) ∧
    integerMassCheck 91 31 0 (dualNumerators091 31 0) := by
  apply integerChecks_of_simple 91 31 0 (dualNumerators091 31 0)
    (![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1719079079316, 0, 1491143233587, 0, 2035556695381, 0, 1259308150413, 1, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079316, 0, 1491143233587, 0, 0, 0, 2664343059941, 1951759503826, 195790587527, 1755968916300, 939253060812, 1341759948741, 1648310233018, 0, 957609719416, 1706733340526, 1648310233018, 0]) (branchResiduals091 31 0) 32891612
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck091_31_1 :
    integerResidualCheck 91 31 1 (dualNumerators091 31 1) ∧
    integerMassCheck 91 31 1 (dualNumerators091 31 1) := by
  apply integerChecks_of_simple 91 31 1 (dualNumerators091 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 741061026801, 808805463926, 18993131489, 744564115640, 845258320866, 704608169862]) (branchResiduals091 31 1) 32891612
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck091_32_0 :
    integerResidualCheck 91 32 0 (dualNumerators091 32 0) ∧
    integerMassCheck 91 32 0 (dualNumerators091 32 0) := by
  apply integerChecks_of_simple 91 32 0 (dualNumerators091 32 0)
    (![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 0, 2079538667399, 1160276651773, 0, 382837210862, 2079538667397, 979882959195, 1, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 1160276651773, 0, 0, 0, 3223007296772, 1518687763292, 152347032953, 1366340730340, 52313619645, 862444872157, 1282570201956, 0, 113267937144, 3109739359628, 0, 1282570201956]) (branchResiduals091 32 0) 67647473
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck091_32_1 :
    integerResidualCheck 91 32 1 (dualNumerators091 32 1) ∧
    integerMassCheck 91 32 1 (dualNumerators091 32 1) := by
  apply integerChecks_of_simple 91 32 1 (dualNumerators091 32 1)
    (![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1946401957496, 0, 638403098871, 3467750500273, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957496, 0, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 3363643757916, 2010906540662, 3009631152853, 227647532122, 1714447367673, 2824496204857, 3016663171407, 0, 4538943572529, 0]) (branchResiduals091 32 1) 67647473
    branchSparseDots091 branchIntegerCurvature091 branchDots091
    branchIntegerCurvature091_entry rfl
    (congrFun (congrFun branchResiduals091_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks091 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 91 j s (dualNumerators091 j s) ∧
    integerMassCheck 91 j s (dualNumerators091 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck091_0_0
    · exact integerCheck091_0_1
  · fin_cases s
    · exact integerCheck091_1_0
    · exact integerCheck091_1_1
  · fin_cases s
    · exact integerCheck091_2_0
    · exact integerCheck091_2_1
  · fin_cases s
    · exact integerCheck091_3_0
    · exact integerCheck091_3_1
  · fin_cases s
    · exact integerCheck091_4_0
    · exact integerCheck091_4_1
  · fin_cases s
    · exact integerCheck091_5_0
    · exact integerCheck091_5_1
  · fin_cases s
    · exact integerCheck091_6_0
    · exact integerCheck091_6_1
  · fin_cases s
    · exact integerCheck091_7_0
    · exact integerCheck091_7_1
  · fin_cases s
    · exact integerCheck091_8_0
    · exact integerCheck091_8_1
  · fin_cases s
    · exact integerCheck091_9_0
    · exact integerCheck091_9_1
  · fin_cases s
    · exact integerCheck091_10_0
    · exact integerCheck091_10_1
  · fin_cases s
    · exact integerCheck091_11_0
    · exact integerCheck091_11_1
  · fin_cases s
    · exact integerCheck091_12_0
    · exact integerCheck091_12_1
  · fin_cases s
    · exact integerCheck091_13_0
    · exact integerCheck091_13_1
  · fin_cases s
    · exact integerCheck091_14_0
    · exact integerCheck091_14_1
  · fin_cases s
    · exact integerCheck091_15_0
    · exact integerCheck091_15_1
  · fin_cases s
    · exact integerCheck091_16_0
    · exact integerCheck091_16_1
  · fin_cases s
    · exact integerCheck091_17_0
    · exact integerCheck091_17_1
  · fin_cases s
    · exact integerCheck091_18_0
    · exact integerCheck091_18_1
  · fin_cases s
    · exact integerCheck091_19_0
    · exact integerCheck091_19_1
  · fin_cases s
    · exact integerCheck091_20_0
    · exact integerCheck091_20_1
  · fin_cases s
    · exact integerCheck091_21_0
    · exact integerCheck091_21_1
  · fin_cases s
    · exact integerCheck091_22_0
    · exact integerCheck091_22_1
  · fin_cases s
    · exact integerCheck091_23_0
    · exact integerCheck091_23_1
  · fin_cases s
    · exact integerCheck091_24_0
    · exact integerCheck091_24_1
  · fin_cases s
    · exact integerCheck091_25_0
    · exact integerCheck091_25_1
  · fin_cases s
    · exact integerCheck091_26_0
    · exact integerCheck091_26_1
  · fin_cases s
    · exact integerCheck091_27_0
    · exact integerCheck091_27_1
  · fin_cases s
    · exact integerCheck091_28_0
    · exact integerCheck091_28_1
  · fin_cases s
    · exact integerCheck091_29_0
    · exact integerCheck091_29_1
  · fin_cases s
    · exact integerCheck091_30_0
    · exact integerCheck091_30_1
  · fin_cases s
    · exact integerCheck091_31_0
    · exact integerCheck091_31_1
  · fin_cases s
    · exact integerCheck091_32_0
    · exact integerCheck091_32_1

end ElevenSquare.Tasks.T06
