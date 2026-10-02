import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual119
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
import ElevenSquare.Tasks.T06.SparseColumn49
import ElevenSquare.Tasks.T06.SparseColumn54
import ElevenSquare.Tasks.T06.SparseColumn56
import ElevenSquare.Tasks.T06.SparseColumn58

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix119 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix119_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = branchIntegerMatrix119 := by
  change roundedGradients ∘ branchRows 119 = branchIntegerMatrix119
  rw [show branchRows 119 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix119]

theorem branchColumn119_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 0) i) = _
  rw [branchColumn119_0]
  exact sparseColumn00_sum n

theorem branchColumn119_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 1) i) = _
  rw [branchColumn119_1]
  exact sparseColumn01_sum n

theorem branchColumn119_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 2) i) = _
  rw [branchColumn119_2]
  exact sparseColumn02_sum n

theorem branchColumn119_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 3) i) = _
  rw [branchColumn119_3]
  exact sparseColumn03_sum n

theorem branchColumn119_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 4) i) = _
  rw [branchColumn119_4]
  exact sparseColumn04_sum n

theorem branchColumn119_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 5) i) = _
  rw [branchColumn119_5]
  exact sparseColumn05_sum n

theorem branchColumn119_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 6) i) = _
  rw [branchColumn119_6]
  exact sparseColumn06_sum n

theorem branchColumn119_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 7) i) = _
  rw [branchColumn119_7]
  exact sparseColumn07_sum n

theorem branchColumn119_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 8) i) = _
  rw [branchColumn119_8]
  exact sparseColumn08_sum n

theorem branchColumn119_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 9) i) = _
  rw [branchColumn119_9]
  exact sparseColumn09_sum n

theorem branchColumn119_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 10) i) = _
  rw [branchColumn119_10]
  exact sparseColumn10_sum n

theorem branchColumn119_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 11) i) = _
  rw [branchColumn119_11]
  exact sparseColumn11_sum n

theorem branchColumn119_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 12) i) = _
  rw [branchColumn119_12]
  exact sparseColumn35_sum n

theorem branchColumn119_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 13) i) = _
  rw [branchColumn119_13]
  exact sparseColumn36_sum n

theorem branchColumn119_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 14) i) = _
  rw [branchColumn119_14]
  exact sparseColumn41_sum n

theorem branchColumn119_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 15) i) = _
  rw [branchColumn119_15]
  exact sparseColumn38_sum n

theorem branchColumn119_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 16) i) = _
  rw [branchColumn119_16]
  exact sparseColumn39_sum n

theorem branchColumn119_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 17) i) = _
  rw [branchColumn119_17]
  exact sparseColumn17_sum n

theorem branchColumn119_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 18) i) = _
  rw [branchColumn119_18]
  exact sparseColumn18_sum n

theorem branchColumn119_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 19) i) = _
  rw [branchColumn119_19]
  exact sparseColumn19_sum n

theorem branchColumn119_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 20) = sparseColumn58 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 20) = sparseDot58 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 20) i) = _
  rw [branchColumn119_20]
  exact sparseColumn58_sum n

theorem branchColumn119_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 21) i) = _
  rw [branchColumn119_21]
  exact sparseColumn21_sum n

theorem branchColumn119_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 22) i) = _
  rw [branchColumn119_22]
  exact sparseColumn22_sum n

theorem branchColumn119_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 23) = sparseColumn54 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 23) = sparseDot54 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 23) i) = _
  rw [branchColumn119_23]
  exact sparseColumn54_sum n

theorem branchColumn119_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 24) i) = _
  rw [branchColumn119_24]
  exact sparseColumn24_sum n

theorem branchColumn119_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 25) i) = _
  rw [branchColumn119_25]
  exact sparseColumn25_sum n

theorem branchColumn119_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 26) = sparseColumn56 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 26) = sparseDot56 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 26) i) = _
  rw [branchColumn119_26]
  exact sparseColumn56_sum n

theorem branchColumn119_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 27) i) = _
  rw [branchColumn119_27]
  exact sparseColumn27_sum n

theorem branchColumn119_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 28) i) = _
  rw [branchColumn119_28]
  exact sparseColumn28_sum n

theorem branchColumn119_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 29) = sparseColumn49 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 29) = sparseDot49 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 29) i) = _
  rw [branchColumn119_29]
  exact sparseColumn49_sum n

theorem branchColumn119_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 30) i) = _
  rw [branchColumn119_30]
  exact sparseColumn30_sum n

theorem branchColumn119_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 31) i) = _
  rw [branchColumn119_31]
  exact sparseColumn31_sum n

theorem branchColumn119_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 119 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 119 i)) = _
  rw [branchIntegerMatrix119_eq]
  simp only [branchIntegerMatrix119, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot119_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 119 i) 32) i) = _
  rw [branchColumn119_32]
  exact sparseColumn43_sum n

def branchSparseDots119 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot58, sparseDot21, sparseDot22, sparseDot54, sparseDot24, sparseDot25, sparseDot56, sparseDot27, sparseDot28, sparseDot49, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot119_0 :
    branchSparseDots119 0 = sparseDot00 := rfl

private theorem branchSparseDot119_1 :
    branchSparseDots119 1 = sparseDot01 := rfl

private theorem branchSparseDot119_2 :
    branchSparseDots119 2 = sparseDot02 := rfl

private theorem branchSparseDot119_3 :
    branchSparseDots119 3 = sparseDot03 := rfl

private theorem branchSparseDot119_4 :
    branchSparseDots119 4 = sparseDot04 := rfl

private theorem branchSparseDot119_5 :
    branchSparseDots119 5 = sparseDot05 := rfl

private theorem branchSparseDot119_6 :
    branchSparseDots119 6 = sparseDot06 := rfl

private theorem branchSparseDot119_7 :
    branchSparseDots119 7 = sparseDot07 := rfl

private theorem branchSparseDot119_8 :
    branchSparseDots119 8 = sparseDot08 := rfl

private theorem branchSparseDot119_9 :
    branchSparseDots119 9 = sparseDot09 := rfl

private theorem branchSparseDot119_10 :
    branchSparseDots119 10 = sparseDot10 := rfl

private theorem branchSparseDot119_11 :
    branchSparseDots119 11 = sparseDot11 := rfl

private theorem branchSparseDot119_12 :
    branchSparseDots119 12 = sparseDot35 := rfl

private theorem branchSparseDot119_13 :
    branchSparseDots119 13 = sparseDot36 := rfl

private theorem branchSparseDot119_14 :
    branchSparseDots119 14 = sparseDot41 := rfl

private theorem branchSparseDot119_15 :
    branchSparseDots119 15 = sparseDot38 := rfl

private theorem branchSparseDot119_16 :
    branchSparseDots119 16 = sparseDot39 := rfl

private theorem branchSparseDot119_17 :
    branchSparseDots119 17 = sparseDot17 := rfl

private theorem branchSparseDot119_18 :
    branchSparseDots119 18 = sparseDot18 := rfl

private theorem branchSparseDot119_19 :
    branchSparseDots119 19 = sparseDot19 := rfl

private theorem branchSparseDot119_20 :
    branchSparseDots119 20 = sparseDot58 := rfl

private theorem branchSparseDot119_21 :
    branchSparseDots119 21 = sparseDot21 := rfl

private theorem branchSparseDot119_22 :
    branchSparseDots119 22 = sparseDot22 := rfl

private theorem branchSparseDot119_23 :
    branchSparseDots119 23 = sparseDot54 := rfl

private theorem branchSparseDot119_24 :
    branchSparseDots119 24 = sparseDot24 := rfl

private theorem branchSparseDot119_25 :
    branchSparseDots119 25 = sparseDot25 := rfl

private theorem branchSparseDot119_26 :
    branchSparseDots119 26 = sparseDot56 := rfl

private theorem branchSparseDot119_27 :
    branchSparseDots119 27 = sparseDot27 := rfl

private theorem branchSparseDot119_28 :
    branchSparseDots119 28 = sparseDot28 := rfl

private theorem branchSparseDot119_29 :
    branchSparseDots119 29 = sparseDot49 := rfl

private theorem branchSparseDot119_30 :
    branchSparseDots119 30 = sparseDot30 := rfl

private theorem branchSparseDot119_31 :
    branchSparseDots119 31 = sparseDot31 := rfl

private theorem branchSparseDot119_32 :
    branchSparseDots119 32 = sparseDot43 := rfl

theorem branchDots119 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 119 i) k) = branchSparseDots119 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot119_0 n
      _ = _ := congrFun branchSparseDot119_0.symm n
  · calc
      _ = sparseDot01 n := branchDot119_1 n
      _ = _ := congrFun branchSparseDot119_1.symm n
  · calc
      _ = sparseDot02 n := branchDot119_2 n
      _ = _ := congrFun branchSparseDot119_2.symm n
  · calc
      _ = sparseDot03 n := branchDot119_3 n
      _ = _ := congrFun branchSparseDot119_3.symm n
  · calc
      _ = sparseDot04 n := branchDot119_4 n
      _ = _ := congrFun branchSparseDot119_4.symm n
  · calc
      _ = sparseDot05 n := branchDot119_5 n
      _ = _ := congrFun branchSparseDot119_5.symm n
  · calc
      _ = sparseDot06 n := branchDot119_6 n
      _ = _ := congrFun branchSparseDot119_6.symm n
  · calc
      _ = sparseDot07 n := branchDot119_7 n
      _ = _ := congrFun branchSparseDot119_7.symm n
  · calc
      _ = sparseDot08 n := branchDot119_8 n
      _ = _ := congrFun branchSparseDot119_8.symm n
  · calc
      _ = sparseDot09 n := branchDot119_9 n
      _ = _ := congrFun branchSparseDot119_9.symm n
  · calc
      _ = sparseDot10 n := branchDot119_10 n
      _ = _ := congrFun branchSparseDot119_10.symm n
  · calc
      _ = sparseDot11 n := branchDot119_11 n
      _ = _ := congrFun branchSparseDot119_11.symm n
  · calc
      _ = sparseDot35 n := branchDot119_12 n
      _ = _ := congrFun branchSparseDot119_12.symm n
  · calc
      _ = sparseDot36 n := branchDot119_13 n
      _ = _ := congrFun branchSparseDot119_13.symm n
  · calc
      _ = sparseDot41 n := branchDot119_14 n
      _ = _ := congrFun branchSparseDot119_14.symm n
  · calc
      _ = sparseDot38 n := branchDot119_15 n
      _ = _ := congrFun branchSparseDot119_15.symm n
  · calc
      _ = sparseDot39 n := branchDot119_16 n
      _ = _ := congrFun branchSparseDot119_16.symm n
  · calc
      _ = sparseDot17 n := branchDot119_17 n
      _ = _ := congrFun branchSparseDot119_17.symm n
  · calc
      _ = sparseDot18 n := branchDot119_18 n
      _ = _ := congrFun branchSparseDot119_18.symm n
  · calc
      _ = sparseDot19 n := branchDot119_19 n
      _ = _ := congrFun branchSparseDot119_19.symm n
  · calc
      _ = sparseDot58 n := branchDot119_20 n
      _ = _ := congrFun branchSparseDot119_20.symm n
  · calc
      _ = sparseDot21 n := branchDot119_21 n
      _ = _ := congrFun branchSparseDot119_21.symm n
  · calc
      _ = sparseDot22 n := branchDot119_22 n
      _ = _ := congrFun branchSparseDot119_22.symm n
  · calc
      _ = sparseDot54 n := branchDot119_23 n
      _ = _ := congrFun branchSparseDot119_23.symm n
  · calc
      _ = sparseDot24 n := branchDot119_24 n
      _ = _ := congrFun branchSparseDot119_24.symm n
  · calc
      _ = sparseDot25 n := branchDot119_25 n
      _ = _ := congrFun branchSparseDot119_25.symm n
  · calc
      _ = sparseDot56 n := branchDot119_26 n
      _ = _ := congrFun branchSparseDot119_26.symm n
  · calc
      _ = sparseDot27 n := branchDot119_27 n
      _ = _ := congrFun branchSparseDot119_27.symm n
  · calc
      _ = sparseDot28 n := branchDot119_28 n
      _ = _ := congrFun branchSparseDot119_28.symm n
  · calc
      _ = sparseDot49 n := branchDot119_29 n
      _ = _ := congrFun branchSparseDot119_29.symm n
  · calc
      _ = sparseDot30 n := branchDot119_30 n
      _ = _ := congrFun branchSparseDot119_30.symm n
  · calc
      _ = sparseDot31 n := branchDot119_31 n
      _ = _ := congrFun branchSparseDot119_31.symm n
  · calc
      _ = sparseDot43 n := branchDot119_32 n
      _ = _ := congrFun branchSparseDot119_32.symm n

def branchIntegerCurvature119 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101955390, 101955390, 79086693, 79086693, 106371291, 106371291, 48290998, 48290998, 289103692, 289103692]

theorem branchIntegerCurvature119_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 119 i)) = branchIntegerCurvature119 := by
  change curvatureNumerators ∘ branchRows 119 = branchIntegerCurvature119
  rw [show branchRows 119 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature119_entry (i : Fin 42) :
    curvatureNumerators (branchRows 119 i) = branchIntegerCurvature119 i :=
  congrFun branchIntegerCurvature119_eq i

def branchResiduals119 : Fin 33 → Fin 2 → ℕ := ![![1301202678401862, 33000000000000], ![1547203133121816, 33000000000000], ![1582789177046382, 1336325522045450], ![33000000000000, 1023208217410656], ![860323282512716, 33000000000000], ![1053697168845654, 896212917795830], ![719847115983962, 624777238175104], ![33000000000000, 763389621497682], ![1577837324875186, 1129634016906895], ![1025926177105843, 33000000000000], ![33000000000000, 777010170491012], ![506895331247360, 463411327916313], ![990524489671341, 66000000000000], ![33000000000000, 862758930921171], ![1054197168845687, 489414591931787], ![472135592355118, 33000000000000], ![66000000000000, 743499167285587], ![663919591519890, 462482488929729], ![623226665353723, 269082194081155], ![629223857852173, 508695745449214], ![1476959482758784, 851835656632042], ![750873121411385, 374264383628312], ![470744175595155, 90602725914513], ![1476959482758784, 851835656632042], ![667371168578856, 230313982650212], ![506058049045585, 218713669397988], ![396136216194598, 851835656632042], ![407377540739132, 546417668864042], ![283888335003034, 300681493829892], ![396136216194598, 888986112139013], ![93859099418061, 550574488330724], ![966898838209851, 648436709070965], ![2021122746193132, 919268488260995]]

theorem branchResiduals119_eq : residualNumerators 119 = branchResiduals119 := rfl

theorem integerCheck119_0_0 :
    integerResidualCheck 119 0 0 (dualNumerators119 0 0) ∧
    integerMassCheck 119 0 0 (dualNumerators119 0 0) := by
  apply integerChecks_of_simple 119 0 0 (dualNumerators119 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1901003851212, 272042472855, 74854042823, 1234047382517, 1835192545884, 0, 1821798773483, 145214820501, 818327875519, 1016864670366]) (branchResiduals119 0 0) 18767167
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck119_0_1 :
    integerResidualCheck 119 0 1 (dualNumerators119 0 1) ∧
    integerMassCheck 119 0 1 (dualNumerators119 0 1) := by
  apply integerChecks_of_simple 119 0 1 (dualNumerators119 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals119 0 1) 18767167
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck119_1_0 :
    integerResidualCheck 119 1 0 (dualNumerators119 1 0) ∧
    integerMassCheck 119 1 0 (dualNumerators119 1 0) := by
  apply integerChecks_of_simple 119 1 0 (dualNumerators119 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 2250973305323, 322124725797, 88634461252, 1461232029476, 2173046324067, 0, 2157186795895, 171948459903, 968979732271, 1204066591796]) (branchResiduals119 1 0) 22176635
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck119_1_1 :
    integerResidualCheck 119 1 1 (dualNumerators119 1 1) ∧
    integerMassCheck 119 1 1 (dualNumerators119 1 1) := by
  apply integerChecks_of_simple 119 1 1 (dualNumerators119 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals119 1 1) 22176635
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck119_2_0 :
    integerResidualCheck 119 2 0 (dualNumerators119 2 0) ∧
    integerMassCheck 119 2 0 (dualNumerators119 2 0) := by
  apply integerChecks_of_simple 119 2 0 (dualNumerators119 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 2250973305325, 322124725797, 88634461252, 1461232029477, 2173046324068, 0, 2157186795897, 171948459903, 968979732272, 1204066591797]) (branchResiduals119 2 0) 22681452
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck119_2_1 :
    integerResidualCheck 119 2 1 (dualNumerators119 2 1) ∧
    integerMassCheck 119 2 1 (dualNumerators119 2 1) := by
  apply integerChecks_of_simple 119 2 1 (dualNumerators119 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1901003851211, 272042472855, 74854042823, 1234047382516, 1835192545883, 0, 1821798773482, 145214820501, 818327875518, 1016864670365]) (branchResiduals119 2 1) 22681452
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck119_3_0 :
    integerResidualCheck 119 3 0 (dualNumerators119 3 0) ∧
    integerMassCheck 119 3 0 (dualNumerators119 3 0) := by
  apply integerChecks_of_simple 119 3 0 (dualNumerators119 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals119 3 0) 16360330
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck119_3_1 :
    integerResidualCheck 119 3 1 (dualNumerators119 3 1) ∧
    integerMassCheck 119 3 1 (dualNumerators119 3 1) := by
  apply integerChecks_of_simple 119 3 1 (dualNumerators119 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000000, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1497855519021, 214350075679, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 644784030255, 801216871619]) (branchResiduals119 3 1) 16360330
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck119_4_0 :
    integerResidualCheck 119 4 0 (dualNumerators119 4 0) ∧
    integerMassCheck 119 4 0 (dualNumerators119 4 0) := by
  apply integerChecks_of_simple 119 4 0 (dualNumerators119 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1264976845121, 181024056754, 49809804896, 821166860693, 1221184310279, 0, 1212271749715, 96629675624, 544536410901, 676647899379]) (branchResiduals119 4 0) 13760362
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck119_4_1 :
    integerResidualCheck 119 4 1 (dualNumerators119 4 1) ∧
    integerMassCheck 119 4 1 (dualNumerators119 4 1) := by
  apply integerChecks_of_simple 119 4 1 (dualNumerators119 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals119 4 1) 13760362
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck119_5_0 :
    integerResidualCheck 119 5 0 (dualNumerators119 5 0) ∧
    integerMassCheck 119 5 0 (dualNumerators119 5 0) := by
  apply integerChecks_of_simple 119 5 0 (dualNumerators119 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1497855519022, 214350075679, 58979649669, 972341366620, 1446000901875, 0, 1435447564017, 114418926712, 644784030255, 801216871620]) (branchResiduals119 5 0) 17641130
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck119_5_1 :
    integerResidualCheck 119 5 1 (dualNumerators119 5 1) ∧
    integerMassCheck 119 5 1 (dualNumerators119 5 1) := by
  apply integerChecks_of_simple 119 5 1 (dualNumerators119 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1264976845120, 181024056754, 49809804896, 821166860692, 1221184310279, 0, 1212271749715, 96629675624, 544536410901, 676647899378]) (branchResiduals119 5 1) 17641130
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck119_6_0 :
    integerResidualCheck 119 6 0 (dualNumerators119 6 0) ∧
    integerMassCheck 119 6 0 (dualNumerators119 6 0) := by
  apply integerChecks_of_simple 119 6 0 (dualNumerators119 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 877488274356, 957704271528, 103906894360, 5439901403, 818327875519, 1016864670366]) (branchResiduals119 6 0) 8962451
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck119_6_1 :
    integerResidualCheck 119 6 1 (dualNumerators119 6 1) ∧
    integerMassCheck 119 6 1 (dualNumerators119 6 1) := by
  apply integerChecks_of_simple 119 6 1 (dualNumerators119 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 760187607595, 1097479190627, 0, 0]) (branchResiduals119 6 1) 8962451
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck119_7_0 :
    integerResidualCheck 119 7 0 (dualNumerators119 7 0) ∧
    integerMassCheck 119 7 0 (dualNumerators119 7 0) := by
  apply integerChecks_of_simple 119 7 0 (dualNumerators119 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals119 7 0) 10424794
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck119_7_1 :
    integerResidualCheck 119 7 1 (dualNumerators119 7 1) ∧
    integerMassCheck 119 7 1 (dualNumerators119 7 1) := by
  apply integerChecks_of_simple 119 7 1 (dualNumerators119 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 1125486652664, 161062362899, 44317230626, 730616014740, 1086523162035, 0, 1078593397950, 85974229952, 484489866137, 602033295899]) (branchResiduals119 7 1) 10424794
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck119_8_0 :
    integerResidualCheck 119 8 0 (dualNumerators119 8 0) ∧
    integerMassCheck 119 8 0 (dualNumerators119 8 0) := by
  apply integerChecks_of_simple 119 8 0 (dualNumerators119 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 2250973305327, 322124725797, 88634461252, 1461232029479, 2173046324070, 0, 2157186795899, 171948459903, 968979732273, 1204066591798]) (branchResiduals119 8 0) 22681452
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck119_8_1 :
    integerResidualCheck 119 8 1 (dualNumerators119 8 1) ∧
    integerMassCheck 119 8 1 (dualNumerators119 8 1) := by
  apply integerChecks_of_simple 119 8 1 (dualNumerators119 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1605445801500, 229746744383, 63216131150, 1042184205913, 1549866490725, 0, 1538555111396, 122637586316, 691098574663, 858767916063]) (branchResiduals119 8 1) 22681452
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck119_9_0 :
    integerResidualCheck 119 9 0 (dualNumerators119 9 0) ∧
    integerMassCheck 119 9 0 (dualNumerators119 9 0) := by
  apply integerChecks_of_simple 119 9 0 (dualNumerators119 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 1497855519021, 214350075679, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 644784030255, 801216871619]) (branchResiduals119 9 0) 16350530
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck119_9_1 :
    integerResidualCheck 119 9 1 (dualNumerators119 9 1) ∧
    integerMassCheck 119 9 1 (dualNumerators119 9 1) := by
  apply integerChecks_of_simple 119 9 1 (dualNumerators119 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals119 9 1) 16350530
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck119_10_0 :
    integerResidualCheck 119 10 0 (dualNumerators119 10 0) ∧
    integerMassCheck 119 10 0 (dualNumerators119 10 0) := by
  apply integerChecks_of_simple 119 10 0 (dualNumerators119 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals119 10 0) 10683139
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck119_10_1 :
    integerResidualCheck 119 10 1 (dualNumerators119 10 1) ∧
    integerMassCheck 119 10 1 (dualNumerators119 10 1) := by
  apply integerChecks_of_simple 119 10 1 (dualNumerators119 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 1145040776568, 163860648772, 45087194994, 743309684668, 1105400337064, 0, 1097332801829, 87467940020, 492907358117, 612492978948]) (branchResiduals119 10 1) 10683139
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck119_11_0 :
    integerResidualCheck 119 11 0 (dualNumerators119 11 0) ∧
    integerMassCheck 119 11 0 (dualNumerators119 11 0) := by
  apply integerChecks_of_simple 119 11 0 (dualNumerators119 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 711656890494, 101841403525, 28022244838, 461976088268, 687019871017, 0, 682005798892, 54362397817, 306347970271, 380671900746]) (branchResiduals119 11 0) 15120968
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck119_11_1 :
    integerResidualCheck 119 11 1 (dualNumerators119 11 1) ∧
    integerMassCheck 119 11 1 (dualNumerators119 11 1) := by
  apply integerChecks_of_simple 119 11 1 (dualNumerators119 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 648949279451, 92867653386, 25553066146, 421269088530, 626483149703, 0, 621910892291, 49572257873, 279354134309, 347129015395]) (branchResiduals119 11 1) 15120968
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck119_12_0 :
    integerResidualCheck 119 12 0 (dualNumerators119 12 0) ∧
    integerMassCheck 119 12 0 (dualNumerators119 12 0) := by
  apply integerChecks_of_simple 119 12 0 (dualNumerators119 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1497855519021, 214350075679, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 644784030255, 801216871619]) (branchResiduals119 12 0) 16348076
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck119_12_1 :
    integerResidualCheck 119 12 1 (dualNumerators119 12 1) ∧
    integerMassCheck 119 12 1 (dualNumerators119 12 1) := by
  apply integerChecks_of_simple 119 12 1 (dualNumerators119 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals119 12 1) 16348076
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck119_13_0 :
    integerResidualCheck 119 13 0 (dualNumerators119 13 0) ∧
    integerMassCheck 119 13 0 (dualNumerators119 13 0) := by
  apply integerChecks_of_simple 119 13 0 (dualNumerators119 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals119 13 0) 13962901
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck119_13_1 :
    integerResidualCheck 119 13 1 (dualNumerators119 13 1) ∧
    integerMassCheck 119 13 1 (dualNumerators119 13 1) := by
  apply integerChecks_of_simple 119 13 1 (dualNumerators119 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000001, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1264976845121, 181024056754, 49809804896, 821166860693, 1221184310279, 0, 1212271749715, 96629675624, 544536410901, 676647899379]) (branchResiduals119 13 1) 13962901
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck119_14_0 :
    integerResidualCheck 119 14 0 (dualNumerators119 14 0) ∧
    integerMassCheck 119 14 0 (dualNumerators119 14 0) := by
  apply integerChecks_of_simple 119 14 0 (dualNumerators119 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000001, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1497855519022, 214350075679, 58979649669, 972341366620, 1446000901875, 0, 1435447564017, 114418926712, 644784030255, 801216871620]) (branchResiduals119 14 0) 20161291
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck119_14_1 :
    integerResidualCheck 119 14 1 (dualNumerators119 14 1) ∧
    integerMassCheck 119 14 1 (dualNumerators119 14 1) := by
  apply integerChecks_of_simple 119 14 1 (dualNumerators119 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 685800765001, 98141271980, 27004132474, 445191438428, 662058864893, 0, 657226965498, 52387287341, 295217646558, 366841218336]) (branchResiduals119 14 1) 20161291
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck119_15_0 :
    integerResidualCheck 119 15 0 (dualNumerators119 15 0) ∧
    integerMassCheck 119 15 0 (dualNumerators119 15 0) := by
  apply integerChecks_of_simple 119 15 0 (dualNumerators119 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 711656890494, 101841403525, 28022244838, 461976088267, 687019871016, 0, 682005798892, 54362397817, 306347970271, 380671900746]) (branchResiduals119 15 0) 12900283
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck119_15_1 :
    integerResidualCheck 119 15 1 (dualNumerators119 15 1) ∧
    integerMassCheck 119 15 1 (dualNumerators119 15 1) := by
  apply integerChecks_of_simple 119 15 1 (dualNumerators119 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals119 15 1) 12900283
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck119_16_0 :
    integerResidualCheck 119 16 0 (dualNumerators119 16 0) ∧
    integerMassCheck 119 16 0 (dualNumerators119 16 0) := by
  apply integerChecks_of_simple 119 16 0 (dualNumerators119 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals119 16 0) 10683060
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck119_16_1 :
    integerResidualCheck 119 16 1 (dualNumerators119 16 1) ∧
    integerMassCheck 119 16 1 (dualNumerators119 16 1) := by
  apply integerChecks_of_simple 119 16 1 (dualNumerators119 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 1145040776568, 163860648772, 45087194994, 743309684668, 1105400337064, 0, 1097332801829, 87467940020, 492907358117, 612492978948]) (branchResiduals119 16 1) 10683060
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck119_17_0 :
    integerResidualCheck 119 17 0 (dualNumerators119 17 0) ∧
    integerMassCheck 119 17 0 (dualNumerators119 17 0) := by
  apply integerChecks_of_simple 119 17 0 (dualNumerators119 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 933392233473, 133572760085, 36753309138, 605916838014, 901078905318, 0, 894502567701, 71300426643, 401798703857, 499280201462]) (branchResiduals119 17 0) 15120968
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck119_17_1 :
    integerResidualCheck 119 17 1 (dualNumerators119 17 1) ∧
    integerMassCheck 119 17 1 (dualNumerators119 17 1) := by
  apply integerChecks_of_simple 119 17 1 (dualNumerators119 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 648949279451, 92867653386, 25553066146, 421269088530, 626483149703, 0, 621910892291, 49572257873, 279354134309, 347129015395]) (branchResiduals119 17 1) 15120968
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck119_18_0 :
    integerResidualCheck 119 18 0 (dualNumerators119 18 0) ∧
    integerMassCheck 119 18 0 (dualNumerators119 18 0) := by
  apply integerChecks_of_simple 119 18 0 (dualNumerators119 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 1065874698487, 202522000941, 0, 763999473637, 1027460955744, 43732116505, 953519106044, 33030453619, 477654049462, 593539022787]) (branchResiduals119 18 0) 13565580
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck119_18_1 :
    integerResidualCheck 119 18 1 (dualNumerators119 18 1) ∧
    integerMassCheck 119 18 1 (dualNumerators119 18 1) := by
  apply integerChecks_of_simple 119 18 1 (dualNumerators119 18 1)
    (![552774353318, 101764201348, 552774353318, 0, 1, 194169418432, 229915461414, 0, 83885421775, 59829007246, 194169418432, 0, 94926637302, 515633295911, 229915461414, 0, 0, 515633295912, 201500008915, 170171850577, 856726447141, 300936675152, 92726973504, 109797748126, 194169418432, 0, 94926637302, 515633295911, 0, 0, 300936675152, 799162766836, 134673498195, 19272402554, 92726973504, 0, 130011204269, 0, 195186313540, 105750361613, 57973095424, 72038108846]) (branchResiduals119 18 1) 13565580
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck119_19_0 :
    integerResidualCheck 119 19 0 (dualNumerators119 19 0) ∧
    integerMassCheck 119 19 0 (dualNumerators119 19 0) := by
  apply integerChecks_of_simple 119 19 0 (dualNumerators119 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 813889575590, 257303496658, 0, 645216866088, 781448198910, 123201425731, 653752451905, 19962510160, 403390917798, 501258706842]) (branchResiduals119 19 0) 8248658
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck119_19_1 :
    integerResidualCheck 119 19 1 (dualNumerators119 19 1) ∧
    integerMassCheck 119 19 1 (dualNumerators119 19 1) := by
  apply integerChecks_of_simple 119 19 1 (dualNumerators119 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 668354800182, 95644673455, 186417556881, 273765914097, 645216866088, 0, 761601233763, 225876501886, 287707656866, 357509209222]) (branchResiduals119 19 1) 8248658
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck119_20_0 :
    integerResidualCheck 119 20 0 (dualNumerators119 20 0) ∧
    integerMassCheck 119 20 0 (dualNumerators119 20 0) := by
  apply integerChecks_of_simple 119 20 0 (dualNumerators119 20 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 1540462609577, 220447348059, 1060657349048, 0, 1487132967409, 0, 2232638358246, 1209625354629, 663125166110, 824007801299]) (branchResiduals119 20 0) 35312013
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck119_20_1 :
    integerResidualCheck 119 20 1 (dualNumerators119 20 1) ∧
    integerMassCheck 119 20 1 (dualNumerators119 20 1) := by
  apply integerChecks_of_simple 119 20 1 (dualNumerators119 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals119 20 1) 35312013
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck119_21_0 :
    integerResidualCheck 119 21 0 (dualNumerators119 21 0) ∧
    integerMassCheck 119 21 0 (dualNumerators119 21 0) := by
  apply integerChecks_of_simple 119 21 0 (dualNumerators119 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 759767979803, 549133445537, 851509250277, 798941670661, 583650214286, 725251211053]) (branchResiduals119 21 0) 11182451
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck119_21_1 :
    integerResidualCheck 119 21 1 (dualNumerators119 21 1) ∧
    integerMassCheck 119 21 1 (dualNumerators119 21 1) := by
  apply integerChecks_of_simple 119 21 1 (dualNumerators119 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 917967404853, 905358228364, 3460174706, 161253783489, 102979506989, 127963650709, 0, 0, 102979506989, 127963650709]) (branchResiduals119 21 1) 11182451
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck119_22_0 :
    integerResidualCheck 119 22 0 (dualNumerators119 22 0) ∧
    integerMassCheck 119 22 0 (dualNumerators119 22 0) := by
  apply integerChecks_of_simple 119 22 0 (dualNumerators119 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 234488508312, 529510965326, 460183470977, 0, 270741877993, 374474988096, 310954038967, 490382041752, 287707656866, 357509209222]) (branchResiduals119 22 0) 6465674
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck119_22_1 :
    integerResidualCheck 119 22 1 (dualNumerators119 22 1) ∧
    integerMassCheck 119 22 1 (dualNumerators119 22 1) := by
  apply integerChecks_of_simple 119 22 1 (dualNumerators119 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 108732662288, 12539033463, 1534493418, 71511669319, 45668611868, 56748400418, 0, 0, 45668611868, 56748400418]) (branchResiduals119 22 1) 6465674
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck119_23_0 :
    integerResidualCheck 119 23 0 (dualNumerators119 23 0) ∧
    integerMassCheck 119 23 0 (dualNumerators119 23 0) := by
  apply integerChecks_of_simple 119 23 0 (dualNumerators119 23 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 540462609577, 1220447348059, 1060657349048, 0, 1487132967409, 0, 2232638358246, 1209625354629, 663125166110, 824007801299]) (branchResiduals119 23 0) 35297932
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck119_23_1 :
    integerResidualCheck 119 23 1 (dualNumerators119 23 1) ∧
    integerMassCheck 119 23 1 (dualNumerators119 23 1) := by
  apply integerChecks_of_simple 119 23 1 (dualNumerators119 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1830784228945, 211125748477, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals119 23 1) 35297932
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck119_24_0 :
    integerResidualCheck 119 24 0 (dualNumerators119 24 0) ∧
    integerMassCheck 119 24 0 (dualNumerators119 24 0) := by
  apply integerChecks_of_simple 119 24 0 (dualNumerators119 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 512185690040, 559007382209, 569308312247, 737522866658, 477654049462, 593539022787]) (branchResiduals119 24 0) 9356857
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck119_24_1 :
    integerResidualCheck 119 24 1 (dualNumerators119 24 1) ∧
    integerMassCheck 119 24 1 (dualNumerators119 24 1) := by
  apply integerChecks_of_simple 119 24 1 (dualNumerators119 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 690777049383, 178822020994, 66021086067, 82038644814, 0, 0, 66021086067, 82038644814]) (branchResiduals119 24 1) 9356857
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck119_25_0 :
    integerResidualCheck 119 25 0 (dualNumerators119 25 0) ∧
    integerMassCheck 119 25 0 (dualNumerators119 25 0) := by
  apply integerChecks_of_simple 119 25 0 (dualNumerators119 25 0)
    (![34423495944, 6337268637, 34423495944, 0, 1, 22181646803, 26265225496, 0, 631959902239, 450728300227, 515126992874, 0, 137760279295, 748301940085, 609960421212, 0, 0, 748301940086, 1518022121617, 1282008050738, 53351822857, 34378591088, 698568688945, 827173216796, 515126992874, 0, 137760279295, 748301940085, 0, 0, 798378064725, 1159768101884, 492180793363, 667587308522, 53351822857, 0, 457056897559, 522396578403, 34378591088, 0, 436746587681, 542706888281]) (branchResiduals119 25 0) 8671199
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck119_25_1 :
    integerResidualCheck 119 25 1 (dualNumerators119 25 1) ∧
    integerMassCheck 119 25 1 (dualNumerators119 25 1) := by
  apply integerChecks_of_simple 119 25 1 (dualNumerators119 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 415529968297, 599898615461, 0, 0]) (branchResiduals119 25 1) 8671199
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck119_26_0 :
    integerResidualCheck 119 26 0 (dualNumerators119 26 0) ∧
    integerMassCheck 119 26 0 (dualNumerators119 26 0) := by
  apply integerChecks_of_simple 119 26 0 (dualNumerators119 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0]) (branchResiduals119 26 0) 15099566
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck119_26_1 :
    integerResidualCheck 119 26 1 (dualNumerators119 26 1) ∧
    integerMassCheck 119 26 1 (dualNumerators119 26 1) := by
  apply integerChecks_of_simple 119 26 1 (dualNumerators119 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 1025837005087, 204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals119 26 1) 15099566
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck119_27_0 :
    integerResidualCheck 119 27 0 (dualNumerators119 27 0) ∧
    integerMassCheck 119 27 0 (dualNumerators119 27 0) := by
  apply integerChecks_of_simple 119 27 0 (dualNumerators119 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 286173900105, 455299762271, 340673826058, 423325647580]) (branchResiduals119 27 0) 7338775
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck119_27_1 :
    integerResidualCheck 119 27 1 (dualNumerators119 27 1) ∧
    integerMassCheck 119 27 1 (dualNumerators119 27 1) := by
  apply integerChecks_of_simple 119 27 1 (dualNumerators119 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 963066529984, 568871411225, 0, 377837583379, 916671368281, 377088943834, 621055226706, 24161639382, 236224837801, 293536000677]) (branchResiduals119 27 1) 7338775
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck119_28_0 :
    integerResidualCheck 119 28 0 (dualNumerators119 28 0) ∧
    integerMassCheck 119 28 0 (dualNumerators119 28 0) := by
  apply integerChecks_of_simple 119 28 0 (dualNumerators119 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 450383711774, 395438493575, 287707656866, 357509209222]) (branchResiduals119 28 0) 10335557
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck119_28_1 :
    integerResidualCheck 119 28 1 (dualNumerators119 28 1) ∧
    integerMassCheck 119 28 1 (dualNumerators119 28 1) := by
  apply integerChecks_of_simple 119 28 1 (dualNumerators119 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 484442151291, 449974794159, 2156352207, 100492021777, 456143077212, 332995651238, 0, 0, 64175975503, 79745886859]) (branchResiduals119 28 1) 10335557
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck119_29_0 :
    integerResidualCheck 119 29 0 (dualNumerators119 29 0) ∧
    integerMassCheck 119 29 0 (dualNumerators119 29 0) := by
  apply integerChecks_of_simple 119 29 0 (dualNumerators119 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0]) (branchResiduals119 29 0) 40352153
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck119_29_1 :
    integerResidualCheck 119 29 1 (dualNumerators119 29 1) ∧
    integerMassCheck 119 29 1 (dualNumerators119 29 1) := by
  apply integerChecks_of_simple 119 29 1 (dualNumerators119 29 1)
    (![814189538844, 149890000629, 814189538844, 0, 1, 31000670773, 36707806937, 0, 1141563866996, 814189538843, 31000670773, 0, 248848315523, 1351722559260, 36707806937, 0, 0, 1351722559261, 2742134741776, 2315802098733, 1261885083355, 48046900821, 1261885083355, 1494194572624, 31000670773, 0, 248848315523, 1351722559260, 0, 0, 48046900821, 2094989499358, 1832718917411, 262270581947, 72165251132, 1189719832223, 1769271584479, 0, 0, 48046900821, 788933161367, 980338423112]) (branchResiduals119 29 1) 40352153
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck119_30_0 :
    integerResidualCheck 119 30 0 (dualNumerators119 30 0) ∧
    integerMassCheck 119 30 0 (dualNumerators119 30 0) := by
  apply integerChecks_of_simple 119 30 0 (dualNumerators119 30 0)
    (![49325597255, 9080703511, 49325597255, 0, 0, 3298611714, 3905876838, 0, 69158736213, 49325597255, 3298611714, 0, 15075840703, 81890664738, 3905876838, 0, 0, 81890664738, 166125241653, 1140296965504, 76448090321, 5112407761, 76448090321, 90521968404, 3298611714, 0, 15075840703, 81890664738, 0, 0, 5112407761, 126919597181, 111030602690, 15888994491, 4371947739, 72076142582, 107186807798, 0, 2092080791, 3020326970, 107186807798, 0]) (branchResiduals119 30 0) 7680628
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck119_30_1 :
    integerResidualCheck 119 30 1 (dualNumerators119 30 1) ∧
    integerMassCheck 119 30 1 (dualNumerators119 30 1) := by
  apply integerChecks_of_simple 119 30 1 (dualNumerators119 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 791397036221, 113252588419, 31162097647, 513739854055, 763999473637, 0, 862736028146, 65914760940, 281282522283, 482716951355]) (branchResiduals119 30 1) 7680628
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck119_31_0 :
    integerResidualCheck 119 31 0 (dualNumerators119 31 0) ∧
    integerMassCheck 119 31 0 (dualNumerators119 31 0) := by
  apply integerChecks_of_simple 119 31 0 (dualNumerators119 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 1032415642125, 1, 592902192609, 0, 1222480453651, 0, 500720887661, 0, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642125, 0, 592902192609, 0, 0, 0, 1600106408231, 776050524992, 678897187053, 97153337939, 898753891846, 674088683815, 655394283556, 0, 654789687546, 945316720686, 655394283556, 0]) (branchResiduals119 31 0) 32891612
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck119_31_1 :
    integerResidualCheck 119 31 1 (dualNumerators119 31 1) ∧
    integerMassCheck 119 31 1 (dualNumerators119 31 1) := by
  apply integerChecks_of_simple 119 31 1 (dualNumerators119 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 741061026801, 808805463926, 725570984152, 37986262977, 327950144489, 1221916346239]) (branchResiduals119 31 1) 32891612
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck119_32_0 :
    integerResidualCheck 119 32 0 (dualNumerators119 32 0) ∧
    integerMassCheck 119 32 0 (dualNumerators119 32 0) := by
  apply integerChecks_of_simple 119 32 0 (dualNumerators119 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 0, 2743468108582, 2028778803022, 0, 505064750776, 2743468108580, 1713354977902, 2, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 2028778803022, 0, 0, 0, 4252009289869, 2655471466972, 2323034456095, 332437010877, 91471945490, 1508010932335, 2242612772688, 0, 3982604450761, 269404839109, 0, 2242612772688]) (branchResiduals119 32 0) 67647473
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck119_32_1 :
    integerResidualCheck 119 32 1 (dualNumerators119 32 1) ∧
    integerMassCheck 119 32 1 (dualNumerators119 32 1) := by
  apply integerChecks_of_simple 119 32 1 (dualNumerators119 32 1)
    (![830518849052, 152896180641, 830518849053, 0, 1, 55540314888, 65765130409, 0, 1164458966499, 830518849051, 55540314888, 0, 253839194360, 1378832582089, 65765130409, 0, 0, 1378832582090, 2797130742946, 2362247611782, 1287193334063, 86080072929, 1287193334063, 1524162000997, 55540314888, 0, 253839194360, 1378832582089, 0, 0, 86080072929, 2137006415304, 1869475758784, 267530656520, 73612590745, 1213580743319, 1804755932001, 0, 35225372368, 50854700562, 1804755932001, 0]) (branchResiduals119 32 1) 67647473
    branchSparseDots119 branchIntegerCurvature119 branchDots119
    branchIntegerCurvature119_entry rfl
    (congrFun (congrFun branchResiduals119_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks119 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 119 j s (dualNumerators119 j s) ∧
    integerMassCheck 119 j s (dualNumerators119 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck119_0_0
    · exact integerCheck119_0_1
  · fin_cases s
    · exact integerCheck119_1_0
    · exact integerCheck119_1_1
  · fin_cases s
    · exact integerCheck119_2_0
    · exact integerCheck119_2_1
  · fin_cases s
    · exact integerCheck119_3_0
    · exact integerCheck119_3_1
  · fin_cases s
    · exact integerCheck119_4_0
    · exact integerCheck119_4_1
  · fin_cases s
    · exact integerCheck119_5_0
    · exact integerCheck119_5_1
  · fin_cases s
    · exact integerCheck119_6_0
    · exact integerCheck119_6_1
  · fin_cases s
    · exact integerCheck119_7_0
    · exact integerCheck119_7_1
  · fin_cases s
    · exact integerCheck119_8_0
    · exact integerCheck119_8_1
  · fin_cases s
    · exact integerCheck119_9_0
    · exact integerCheck119_9_1
  · fin_cases s
    · exact integerCheck119_10_0
    · exact integerCheck119_10_1
  · fin_cases s
    · exact integerCheck119_11_0
    · exact integerCheck119_11_1
  · fin_cases s
    · exact integerCheck119_12_0
    · exact integerCheck119_12_1
  · fin_cases s
    · exact integerCheck119_13_0
    · exact integerCheck119_13_1
  · fin_cases s
    · exact integerCheck119_14_0
    · exact integerCheck119_14_1
  · fin_cases s
    · exact integerCheck119_15_0
    · exact integerCheck119_15_1
  · fin_cases s
    · exact integerCheck119_16_0
    · exact integerCheck119_16_1
  · fin_cases s
    · exact integerCheck119_17_0
    · exact integerCheck119_17_1
  · fin_cases s
    · exact integerCheck119_18_0
    · exact integerCheck119_18_1
  · fin_cases s
    · exact integerCheck119_19_0
    · exact integerCheck119_19_1
  · fin_cases s
    · exact integerCheck119_20_0
    · exact integerCheck119_20_1
  · fin_cases s
    · exact integerCheck119_21_0
    · exact integerCheck119_21_1
  · fin_cases s
    · exact integerCheck119_22_0
    · exact integerCheck119_22_1
  · fin_cases s
    · exact integerCheck119_23_0
    · exact integerCheck119_23_1
  · fin_cases s
    · exact integerCheck119_24_0
    · exact integerCheck119_24_1
  · fin_cases s
    · exact integerCheck119_25_0
    · exact integerCheck119_25_1
  · fin_cases s
    · exact integerCheck119_26_0
    · exact integerCheck119_26_1
  · fin_cases s
    · exact integerCheck119_27_0
    · exact integerCheck119_27_1
  · fin_cases s
    · exact integerCheck119_28_0
    · exact integerCheck119_28_1
  · fin_cases s
    · exact integerCheck119_29_0
    · exact integerCheck119_29_1
  · fin_cases s
    · exact integerCheck119_30_0
    · exact integerCheck119_30_1
  · fin_cases s
    · exact integerCheck119_31_0
    · exact integerCheck119_31_1
  · fin_cases s
    · exact integerCheck119_32_0
    · exact integerCheck119_32_1

end ElevenSquare.Tasks.T06
