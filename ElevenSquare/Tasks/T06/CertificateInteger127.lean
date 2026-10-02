import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual127
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
import ElevenSquare.Tasks.T06.SparseColumn51
import ElevenSquare.Tasks.T06.SparseColumn54
import ElevenSquare.Tasks.T06.SparseColumn57
import ElevenSquare.Tasks.T06.SparseColumn58

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix127 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix127_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = branchIntegerMatrix127 := by
  change roundedGradients ∘ branchRows 127 = branchIntegerMatrix127
  rw [show branchRows 127 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix127]

theorem branchColumn127_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 0) i) = _
  rw [branchColumn127_0]
  exact sparseColumn00_sum n

theorem branchColumn127_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 1) i) = _
  rw [branchColumn127_1]
  exact sparseColumn01_sum n

theorem branchColumn127_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 2) i) = _
  rw [branchColumn127_2]
  exact sparseColumn02_sum n

theorem branchColumn127_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 3) i) = _
  rw [branchColumn127_3]
  exact sparseColumn03_sum n

theorem branchColumn127_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 4) i) = _
  rw [branchColumn127_4]
  exact sparseColumn04_sum n

theorem branchColumn127_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 5) i) = _
  rw [branchColumn127_5]
  exact sparseColumn05_sum n

theorem branchColumn127_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 6) i) = _
  rw [branchColumn127_6]
  exact sparseColumn06_sum n

theorem branchColumn127_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 7) i) = _
  rw [branchColumn127_7]
  exact sparseColumn07_sum n

theorem branchColumn127_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 8) i) = _
  rw [branchColumn127_8]
  exact sparseColumn08_sum n

theorem branchColumn127_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 9) i) = _
  rw [branchColumn127_9]
  exact sparseColumn09_sum n

theorem branchColumn127_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 10) i) = _
  rw [branchColumn127_10]
  exact sparseColumn10_sum n

theorem branchColumn127_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 11) i) = _
  rw [branchColumn127_11]
  exact sparseColumn11_sum n

theorem branchColumn127_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 12) i) = _
  rw [branchColumn127_12]
  exact sparseColumn35_sum n

theorem branchColumn127_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 13) i) = _
  rw [branchColumn127_13]
  exact sparseColumn36_sum n

theorem branchColumn127_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 14) i) = _
  rw [branchColumn127_14]
  exact sparseColumn41_sum n

theorem branchColumn127_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 15) i) = _
  rw [branchColumn127_15]
  exact sparseColumn38_sum n

theorem branchColumn127_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 16) i) = _
  rw [branchColumn127_16]
  exact sparseColumn39_sum n

theorem branchColumn127_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 17) i) = _
  rw [branchColumn127_17]
  exact sparseColumn17_sum n

theorem branchColumn127_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 18) i) = _
  rw [branchColumn127_18]
  exact sparseColumn18_sum n

theorem branchColumn127_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 19) i) = _
  rw [branchColumn127_19]
  exact sparseColumn19_sum n

theorem branchColumn127_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 20) = sparseColumn58 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 20) = sparseDot58 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 20) i) = _
  rw [branchColumn127_20]
  exact sparseColumn58_sum n

theorem branchColumn127_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 21) i) = _
  rw [branchColumn127_21]
  exact sparseColumn21_sum n

theorem branchColumn127_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 22) i) = _
  rw [branchColumn127_22]
  exact sparseColumn22_sum n

theorem branchColumn127_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 23) = sparseColumn54 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 23) = sparseDot54 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 23) i) = _
  rw [branchColumn127_23]
  exact sparseColumn54_sum n

theorem branchColumn127_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 24) i) = _
  rw [branchColumn127_24]
  exact sparseColumn24_sum n

theorem branchColumn127_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 25) i) = _
  rw [branchColumn127_25]
  exact sparseColumn25_sum n

theorem branchColumn127_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 26) = sparseColumn57 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 26) = sparseDot57 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 26) i) = _
  rw [branchColumn127_26]
  exact sparseColumn57_sum n

theorem branchColumn127_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 27) i) = _
  rw [branchColumn127_27]
  exact sparseColumn27_sum n

theorem branchColumn127_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 28) i) = _
  rw [branchColumn127_28]
  exact sparseColumn28_sum n

theorem branchColumn127_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 29) = sparseColumn51 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 29) = sparseDot51 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 29) i) = _
  rw [branchColumn127_29]
  exact sparseColumn51_sum n

theorem branchColumn127_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 30) i) = _
  rw [branchColumn127_30]
  exact sparseColumn30_sum n

theorem branchColumn127_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 31) i) = _
  rw [branchColumn127_31]
  exact sparseColumn31_sum n

theorem branchColumn127_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 127 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 127 i)) = _
  rw [branchIntegerMatrix127_eq]
  simp only [branchIntegerMatrix127, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot127_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 127 i) 32) i) = _
  rw [branchColumn127_32]
  exact sparseColumn43_sum n

def branchSparseDots127 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot58, sparseDot21, sparseDot22, sparseDot54, sparseDot24, sparseDot25, sparseDot57, sparseDot27, sparseDot28, sparseDot51, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot127_0 :
    branchSparseDots127 0 = sparseDot00 := rfl

private theorem branchSparseDot127_1 :
    branchSparseDots127 1 = sparseDot01 := rfl

private theorem branchSparseDot127_2 :
    branchSparseDots127 2 = sparseDot02 := rfl

private theorem branchSparseDot127_3 :
    branchSparseDots127 3 = sparseDot03 := rfl

private theorem branchSparseDot127_4 :
    branchSparseDots127 4 = sparseDot04 := rfl

private theorem branchSparseDot127_5 :
    branchSparseDots127 5 = sparseDot05 := rfl

private theorem branchSparseDot127_6 :
    branchSparseDots127 6 = sparseDot06 := rfl

private theorem branchSparseDot127_7 :
    branchSparseDots127 7 = sparseDot07 := rfl

private theorem branchSparseDot127_8 :
    branchSparseDots127 8 = sparseDot08 := rfl

private theorem branchSparseDot127_9 :
    branchSparseDots127 9 = sparseDot09 := rfl

private theorem branchSparseDot127_10 :
    branchSparseDots127 10 = sparseDot10 := rfl

private theorem branchSparseDot127_11 :
    branchSparseDots127 11 = sparseDot11 := rfl

private theorem branchSparseDot127_12 :
    branchSparseDots127 12 = sparseDot35 := rfl

private theorem branchSparseDot127_13 :
    branchSparseDots127 13 = sparseDot36 := rfl

private theorem branchSparseDot127_14 :
    branchSparseDots127 14 = sparseDot41 := rfl

private theorem branchSparseDot127_15 :
    branchSparseDots127 15 = sparseDot38 := rfl

private theorem branchSparseDot127_16 :
    branchSparseDots127 16 = sparseDot39 := rfl

private theorem branchSparseDot127_17 :
    branchSparseDots127 17 = sparseDot17 := rfl

private theorem branchSparseDot127_18 :
    branchSparseDots127 18 = sparseDot18 := rfl

private theorem branchSparseDot127_19 :
    branchSparseDots127 19 = sparseDot19 := rfl

private theorem branchSparseDot127_20 :
    branchSparseDots127 20 = sparseDot58 := rfl

private theorem branchSparseDot127_21 :
    branchSparseDots127 21 = sparseDot21 := rfl

private theorem branchSparseDot127_22 :
    branchSparseDots127 22 = sparseDot22 := rfl

private theorem branchSparseDot127_23 :
    branchSparseDots127 23 = sparseDot54 := rfl

private theorem branchSparseDot127_24 :
    branchSparseDots127 24 = sparseDot24 := rfl

private theorem branchSparseDot127_25 :
    branchSparseDots127 25 = sparseDot25 := rfl

private theorem branchSparseDot127_26 :
    branchSparseDots127 26 = sparseDot57 := rfl

private theorem branchSparseDot127_27 :
    branchSparseDots127 27 = sparseDot27 := rfl

private theorem branchSparseDot127_28 :
    branchSparseDots127 28 = sparseDot28 := rfl

private theorem branchSparseDot127_29 :
    branchSparseDots127 29 = sparseDot51 := rfl

private theorem branchSparseDot127_30 :
    branchSparseDots127 30 = sparseDot30 := rfl

private theorem branchSparseDot127_31 :
    branchSparseDots127 31 = sparseDot31 := rfl

private theorem branchSparseDot127_32 :
    branchSparseDots127 32 = sparseDot43 := rfl

theorem branchDots127 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 127 i) k) = branchSparseDots127 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot127_0 n
      _ = _ := congrFun branchSparseDot127_0.symm n
  · calc
      _ = sparseDot01 n := branchDot127_1 n
      _ = _ := congrFun branchSparseDot127_1.symm n
  · calc
      _ = sparseDot02 n := branchDot127_2 n
      _ = _ := congrFun branchSparseDot127_2.symm n
  · calc
      _ = sparseDot03 n := branchDot127_3 n
      _ = _ := congrFun branchSparseDot127_3.symm n
  · calc
      _ = sparseDot04 n := branchDot127_4 n
      _ = _ := congrFun branchSparseDot127_4.symm n
  · calc
      _ = sparseDot05 n := branchDot127_5 n
      _ = _ := congrFun branchSparseDot127_5.symm n
  · calc
      _ = sparseDot06 n := branchDot127_6 n
      _ = _ := congrFun branchSparseDot127_6.symm n
  · calc
      _ = sparseDot07 n := branchDot127_7 n
      _ = _ := congrFun branchSparseDot127_7.symm n
  · calc
      _ = sparseDot08 n := branchDot127_8 n
      _ = _ := congrFun branchSparseDot127_8.symm n
  · calc
      _ = sparseDot09 n := branchDot127_9 n
      _ = _ := congrFun branchSparseDot127_9.symm n
  · calc
      _ = sparseDot10 n := branchDot127_10 n
      _ = _ := congrFun branchSparseDot127_10.symm n
  · calc
      _ = sparseDot11 n := branchDot127_11 n
      _ = _ := congrFun branchSparseDot127_11.symm n
  · calc
      _ = sparseDot35 n := branchDot127_12 n
      _ = _ := congrFun branchSparseDot127_12.symm n
  · calc
      _ = sparseDot36 n := branchDot127_13 n
      _ = _ := congrFun branchSparseDot127_13.symm n
  · calc
      _ = sparseDot41 n := branchDot127_14 n
      _ = _ := congrFun branchSparseDot127_14.symm n
  · calc
      _ = sparseDot38 n := branchDot127_15 n
      _ = _ := congrFun branchSparseDot127_15.symm n
  · calc
      _ = sparseDot39 n := branchDot127_16 n
      _ = _ := congrFun branchSparseDot127_16.symm n
  · calc
      _ = sparseDot17 n := branchDot127_17 n
      _ = _ := congrFun branchSparseDot127_17.symm n
  · calc
      _ = sparseDot18 n := branchDot127_18 n
      _ = _ := congrFun branchSparseDot127_18.symm n
  · calc
      _ = sparseDot19 n := branchDot127_19 n
      _ = _ := congrFun branchSparseDot127_19.symm n
  · calc
      _ = sparseDot58 n := branchDot127_20 n
      _ = _ := congrFun branchSparseDot127_20.symm n
  · calc
      _ = sparseDot21 n := branchDot127_21 n
      _ = _ := congrFun branchSparseDot127_21.symm n
  · calc
      _ = sparseDot22 n := branchDot127_22 n
      _ = _ := congrFun branchSparseDot127_22.symm n
  · calc
      _ = sparseDot54 n := branchDot127_23 n
      _ = _ := congrFun branchSparseDot127_23.symm n
  · calc
      _ = sparseDot24 n := branchDot127_24 n
      _ = _ := congrFun branchSparseDot127_24.symm n
  · calc
      _ = sparseDot25 n := branchDot127_25 n
      _ = _ := congrFun branchSparseDot127_25.symm n
  · calc
      _ = sparseDot57 n := branchDot127_26 n
      _ = _ := congrFun branchSparseDot127_26.symm n
  · calc
      _ = sparseDot27 n := branchDot127_27 n
      _ = _ := congrFun branchSparseDot127_27.symm n
  · calc
      _ = sparseDot28 n := branchDot127_28 n
      _ = _ := congrFun branchSparseDot127_28.symm n
  · calc
      _ = sparseDot51 n := branchDot127_29 n
      _ = _ := congrFun branchSparseDot127_29.symm n
  · calc
      _ = sparseDot30 n := branchDot127_30 n
      _ = _ := congrFun branchSparseDot127_30.symm n
  · calc
      _ = sparseDot31 n := branchDot127_31 n
      _ = _ := congrFun branchSparseDot127_31.symm n
  · calc
      _ = sparseDot43 n := branchDot127_32 n
      _ = _ := congrFun branchSparseDot127_32.symm n

def branchIntegerCurvature127 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101955390, 101955390, 79086693, 79086693, 106371291, 106371291, 88123140, 88123140, 289103692, 289103692]

theorem branchIntegerCurvature127_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 127 i)) = branchIntegerCurvature127 := by
  change curvatureNumerators ∘ branchRows 127 = branchIntegerCurvature127
  rw [show branchRows 127 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 52, 53, 54, 55, 50, 51, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature127_entry (i : Fin 42) :
    curvatureNumerators (branchRows 127 i) = branchIntegerCurvature127 i :=
  congrFun branchIntegerCurvature127_eq i

def branchResiduals127 : Fin 33 → Fin 2 → ℕ := ![![1297715188219138, 33000000000000], ![1545366750505710, 33000000000000], ![1581776144903180, 1336879694326198], ![33000000000000, 1022239866469096], ![854870483275630, 33000000000000], ![1055559663890905, 895898576849254], ![720984936817417, 624798065222648], ![33000000000000, 763286140676350], ![1577447361653188, 1127412779189880], ![1023720598714715, 33000000000000], ![33000000000000, 777010170491012], ![507968151021277, 465633571577520], ![988318911280213, 66000000000000], ![33000000000000, 857608805843885], ![1055519926094505, 485776263453423], ![471239952661726, 33000000000000], ![66000000000000, 743499167285587], ![659482574634321, 464704732590936], ![621594243807719, 267931885416780], ![628326893989503, 510768346232083], ![1474116175544279, 851835656632042], ![751104335538261, 374264383628312], ![467791871032894, 90602725914513], ![1474116175544279, 851835656632042], ![669682137070249, 230313982650212], ![508521900991697, 218713669397988], ![398805840068707, 851835656632042], ![407851233060713, 545122209812678], ![285139865366158, 300681493829892], ![398805840068707, 891348888424407], ![97644135565378, 550658979383196], ![967110960741787, 648569605951673], ![2018279438978627, 920579729933358]]

theorem branchResiduals127_eq : residualNumerators 127 = branchResiduals127 := rfl

theorem integerCheck127_0_0 :
    integerResidualCheck 127 0 0 (dualNumerators127 0 0) ∧
    integerMassCheck 127 0 0 (dualNumerators127 0 0) := by
  apply integerChecks_of_simple 127 0 0 (dualNumerators127 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 666956468696, 1506089855371, 1308901425339, 0, 601145163368, 1234047382517, 1330333654477, 636679939507, 818327875519, 1016864670366]) (branchResiduals127 0 0) 18767167
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck127_0_1 :
    integerResidualCheck 127 0 1 (dualNumerators127 0 1) ∧
    integerMassCheck 127 0 1 (dualNumerators127 0 1) := by
  apply integerChecks_of_simple 127 0 1 (dualNumerators127 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals127 0 1) 18767167
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck127_1_0 :
    integerResidualCheck 127 1 0 (dualNumerators127 1 0) ∧
    integerMassCheck 127 1 0 (dualNumerators127 1 0) := by
  apply integerChecks_of_simple 127 1 0 (dualNumerators127 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 789741275848, 1783356755272, 1549866490727, 0, 711814294591, 1461232029476, 1575244332878, 753890922920, 968979732271, 1204066591796]) (branchResiduals127 1 0) 22176635
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck127_1_1 :
    integerResidualCheck 127 1 1 (dualNumerators127 1 1) ∧
    integerMassCheck 127 1 1 (dualNumerators127 1 1) := by
  apply integerChecks_of_simple 127 1 1 (dualNumerators127 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals127 1 1) 22176635
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck127_2_0 :
    integerResidualCheck 127 2 0 (dualNumerators127 2 0) ∧
    integerMassCheck 127 2 0 (dualNumerators127 2 0) := by
  apply integerChecks_of_simple 127 2 0 (dualNumerators127 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 789741275848, 1783356755274, 1549866490728, 0, 711814294592, 1461232029477, 1575244332879, 753890922921, 968979732272, 1204066591797]) (branchResiduals127 2 0) 22681452
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck127_2_1 :
    integerResidualCheck 127 2 1 (dualNumerators127 2 1) ∧
    integerMassCheck 127 2 1 (dualNumerators127 2 1) := by
  apply integerChecks_of_simple 127 2 1 (dualNumerators127 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 666956468696, 1506089855370, 1308901425338, 0, 601145163368, 1234047382516, 1330333654476, 636679939507, 818327875518, 1016864670365]) (branchResiduals127 2 1) 22681452
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck127_3_0 :
    integerResidualCheck 127 3 0 (dualNumerators127 3 0) ∧
    integerMassCheck 127 3 0 (dualNumerators127 3 0) := by
  apply integerChecks_of_simple 127 3 0 (dualNumerators127 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals127 3 0) 16360330
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck127_3_1 :
    integerResidualCheck 127 3 1 (dualNumerators127 3 1) ∧
    integerMassCheck 127 3 1 (dualNumerators127 3 1) := by
  apply integerChecks_of_simple 127 3 1 (dualNumerators127 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000001, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000001, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 525514152402, 1186691442298, 1031321016287, 0, 473659535255, 972341366619, 1048208085022, 501658405706, 644784030255, 801216871619]) (branchResiduals127 3 1) 16360330
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck127_4_0 :
    integerResidualCheck 127 4 0 (dualNumerators127 4 0) ∧
    integerMassCheck 127 4 0 (dualNumerators127 4 0) := by
  apply integerChecks_of_simple 127 4 0 (dualNumerators127 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000001, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 443809984428, 1002190917446, 870976665588, 0, 400017449587, 821166860693, 885238221966, 423663203373, 544536410901, 676647899379]) (branchResiduals127 4 0) 13760362
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck127_4_1 :
    integerResidualCheck 127 4 1 (dualNumerators127 4 1) ∧
    integerMassCheck 127 4 1 (dualNumerators127 4 1) := by
  apply integerChecks_of_simple 127 4 1 (dualNumerators127 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals127 4 1) 13760362
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck127_5_0 :
    integerResidualCheck 127 5 0 (dualNumerators127 5 0) ∧
    integerMassCheck 127 5 0 (dualNumerators127 5 0) := by
  apply integerChecks_of_simple 127 5 0 (dualNumerators127 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 525514152403, 1186691442299, 1031321016288, 0, 473659535256, 972341366620, 1048208085022, 501658405707, 644784030255, 801216871620]) (branchResiduals127 5 0) 17641130
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck127_5_1 :
    integerResidualCheck 127 5 1 (dualNumerators127 5 1) ∧
    integerMassCheck 127 5 1 (dualNumerators127 5 1) := by
  apply integerChecks_of_simple 127 5 1 (dualNumerators127 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 443809984428, 1002190917446, 870976665588, 0, 400017449587, 821166860692, 885238221966, 423663203373, 544536410901, 676647899378]) (branchResiduals127 5 1) 17641130
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck127_6_0 :
    integerResidualCheck 127 6 0 (dualNumerators127 6 0) ∧
    integerMassCheck 127 6 0 (dualNumerators127 6 0) := by
  apply integerChecks_of_simple 127 6 0 (dualNumerators127 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 877488274356, 957704271528, 2719950702, 106626845062, 818327875519, 1016864670366]) (branchResiduals127 6 0) 8962451
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck127_6_1 :
    integerResidualCheck 127 6 1 (dualNumerators127 6 1) ∧
    integerMassCheck 127 6 1 (dualNumerators127 6 1) := by
  apply integerChecks_of_simple 127 6 1 (dualNumerators127 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals127 6 1) 8962451
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck127_7_0 :
    integerResidualCheck 127 7 0 (dualNumerators127 7 0) ∧
    integerMassCheck 127 7 0 (dualNumerators127 7 0) := by
  apply integerChecks_of_simple 127 7 0 (dualNumerators127 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals127 7 0) 10424794
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck127_7_1 :
    integerResidualCheck 127 7 1 (dualNumerators127 7 1) ∧
    integerMassCheck 127 7 1 (dualNumerators127 7 1) := by
  apply integerChecks_of_simple 127 7 1 (dualNumerators127 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 394870637925, 891678377638, 774933245365, 0, 355907147296, 730616014740, 787622166441, 376945461461, 484489866137, 602033295899]) (branchResiduals127 7 1) 10424794
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck127_8_0 :
    integerResidualCheck 127 8 0 (dualNumerators127 8 0) ∧
    integerMassCheck 127 8 0 (dualNumerators127 8 0) := by
  apply integerChecks_of_simple 127 8 0 (dualNumerators127 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 789741275849, 1783356755275, 1549866490730, 0, 711814294592, 1461232029479, 1575244332881, 753890922921, 968979732273, 1204066591798]) (branchResiduals127 8 0) 22681452
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck127_8_1 :
    integerResidualCheck 127 8 1 (dualNumerators127 8 1) ∧
    integerMassCheck 127 8 1 (dualNumerators127 8 1) := by
  apply integerChecks_of_simple 127 8 1 (dualNumerators127 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 563261595587, 1271930950295, 1105400337063, 0, 507682284813, 1042184205913, 1123500396284, 537692301428, 691098574663, 858767916063]) (branchResiduals127 8 1) 22681452
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck127_9_0 :
    integerResidualCheck 127 9 0 (dualNumerators127 9 0) ∧
    integerMassCheck 127 9 0 (dualNumerators127 9 0) := by
  apply integerChecks_of_simple 127 9 0 (dualNumerators127 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 525514152402, 1186691442298, 1031321016287, 0, 473659535255, 972341366619, 1048208085022, 501658405706, 644784030255, 801216871619]) (branchResiduals127 9 0) 16350530
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck127_9_1 :
    integerResidualCheck 127 9 1 (dualNumerators127 9 1) ∧
    integerMassCheck 127 9 1 (dualNumerators127 9 1) := by
  apply integerChecks_of_simple 127 9 1 (dualNumerators127 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals127 9 1) 16350530
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck127_10_0 :
    integerResidualCheck 127 10 0 (dualNumerators127 10 0) ∧
    integerMassCheck 127 10 0 (dualNumerators127 10 0) := by
  apply integerChecks_of_simple 127 10 0 (dualNumerators127 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals127 10 0) 10683139
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck127_10_1 :
    integerResidualCheck 127 10 1 (dualNumerators127 10 1) ∧
    integerMassCheck 127 10 1 (dualNumerators127 10 1) := by
  apply integerChecks_of_simple 127 10 1 (dualNumerators127 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 401731091900, 907170333440, 788396879662, 0, 362090652396, 743309684668, 801306257136, 383494484713, 492907358117, 612492978948]) (branchResiduals127 10 1) 10683139
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck127_11_0 :
    integerResidualCheck 127 11 0 (dualNumerators127 11 0) ∧
    integerMassCheck 127 11 0 (dualNumerators127 11 0) := by
  apply integerChecks_of_simple 127 11 0 (dualNumerators127 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 249680802227, 563817491793, 489998333105, 0, 225043782750, 461976088268, 498021669583, 238346527126, 306347970271, 380671900746]) (branchResiduals127 11 0) 15120968
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck127_11_1 :
    integerResidualCheck 127 11 1 (dualNumerators127 11 1) ∧
    integerMassCheck 127 11 1 (dualNumerators127 11 1) := by
  apply integerChecks_of_simple 127 11 1 (dualNumerators127 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 227680190921, 514136741916, 446822154676, 0, 205214061173, 421269088530, 454138515265, 217344634900, 279354134309, 347129015395]) (branchResiduals127 11 1) 15120968
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck127_12_0 :
    integerResidualCheck 127 12 0 (dualNumerators127 12 0) ∧
    integerMassCheck 127 12 0 (dualNumerators127 12 0) := by
  apply integerChecks_of_simple 127 12 0 (dualNumerators127 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 525514152402, 1186691442298, 1031321016287, 0, 473659535255, 972341366619, 1048208085022, 501658405706, 644784030255, 801216871619]) (branchResiduals127 12 0) 16348076
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck127_12_1 :
    integerResidualCheck 127 12 1 (dualNumerators127 12 1) ∧
    integerMassCheck 127 12 1 (dualNumerators127 12 1) := by
  apply integerChecks_of_simple 127 12 1 (dualNumerators127 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals127 12 1) 16348076
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck127_13_0 :
    integerResidualCheck 127 13 0 (dualNumerators127 13 0) ∧
    integerMassCheck 127 13 0 (dualNumerators127 13 0) := by
  apply integerChecks_of_simple 127 13 0 (dualNumerators127 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals127 13 0) 13962901
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck127_13_1 :
    integerResidualCheck 127 13 1 (dualNumerators127 13 1) ∧
    integerMassCheck 127 13 1 (dualNumerators127 13 1) := by
  apply integerChecks_of_simple 127 13 1 (dualNumerators127 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 443809984428, 1002190917446, 870976665588, 0, 400017449587, 821166860693, 885238221966, 423663203373, 544536410901, 676647899379]) (branchResiduals127 13 1) 13962901
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck127_14_0 :
    integerResidualCheck 127 14 0 (dualNumerators127 14 0) ∧
    integerMassCheck 127 14 0 (dualNumerators127 14 0) := by
  apply integerChecks_of_simple 127 14 0 (dualNumerators127 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 525514152403, 1186691442299, 1031321016288, 0, 473659535256, 972341366620, 1048208085022, 501658405707, 644784030255, 801216871620]) (branchResiduals127 14 0) 20161291
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck127_14_1 :
    integerResidualCheck 127 14 1 (dualNumerators127 14 1) ∧
    integerMassCheck 127 14 1 (dualNumerators127 14 1) := by
  apply integerChecks_of_simple 127 14 1 (dualNumerators127 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 240609326574, 543332710407, 472195570901, 0, 216867426466, 445191438428, 479927401181, 229686851658, 295217646558, 366841218336]) (branchResiduals127 14 1) 20161291
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck127_15_0 :
    integerResidualCheck 127 15 0 (dualNumerators127 15 0) ∧
    integerMassCheck 127 15 0 (dualNumerators127 15 0) := by
  apply integerChecks_of_simple 127 15 0 (dualNumerators127 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 249680802227, 563817491792, 489998333105, 0, 225043782750, 461976088267, 498021669583, 238346527126, 306347970271, 380671900746]) (branchResiduals127 15 0) 12900283
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck127_15_1 :
    integerResidualCheck 127 15 1 (dualNumerators127 15 1) ∧
    integerMassCheck 127 15 1 (dualNumerators127 15 1) := by
  apply integerChecks_of_simple 127 15 1 (dualNumerators127 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals127 15 1) 12900283
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck127_16_0 :
    integerResidualCheck 127 16 0 (dualNumerators127 16 0) ∧
    integerMassCheck 127 16 0 (dualNumerators127 16 0) := by
  apply integerChecks_of_simple 127 16 0 (dualNumerators127 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals127 16 0) 10683060
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck127_16_1 :
    integerResidualCheck 127 16 1 (dualNumerators127 16 1) ∧
    integerMassCheck 127 16 1 (dualNumerators127 16 1) := by
  apply integerChecks_of_simple 127 16 1 (dualNumerators127 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 401731091900, 907170333440, 788396879662, 0, 362090652396, 743309684668, 801306257136, 383494484713, 492907358117, 612492978948]) (branchResiduals127 16 1) 10683060
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck127_17_0 :
    integerResidualCheck 127 17 0 (dualNumerators127 17 0) ∧
    integerMassCheck 127 17 0 (dualNumerators127 17 0) := by
  apply integerChecks_of_simple 127 17 0 (dualNumerators127 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 327475395459, 739489598098, 642670147151, 0, 295162067305, 605916838014, 653193364245, 312609630099, 401798703857, 499280201462]) (branchResiduals127 17 0) 15120968
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck127_17_1 :
    integerResidualCheck 127 17 1 (dualNumerators127 17 1) ∧
    integerMassCheck 127 17 1 (dualNumerators127 17 1) := by
  apply integerChecks_of_simple 127 17 1 (dualNumerators127 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 227680190921, 514136741916, 446822154676, 0, 205214061173, 421269088530, 454138515265, 217344634900, 279354134309, 347129015395]) (branchResiduals127 17 1) 15120968
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck127_18_0 :
    integerResidualCheck 127 18 0 (dualNumerators127 18 0) ∧
    integerMassCheck 127 18 0 (dualNumerators127 18 0) := by
  apply integerChecks_of_simple 127 18 0 (dualNumerators127 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 301875224851, 966521474577, 763999473637, 0, 263461482107, 807731590141, 772489965679, 214059593984, 477654049462, 593539022787]) (branchResiduals127 18 0) 13565580
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck127_18_1 :
    integerResidualCheck 127 18 1 (dualNumerators127 18 1) ∧
    integerMassCheck 127 18 1 (dualNumerators127 18 1) := by
  apply integerChecks_of_simple 127 18 1 (dualNumerators127 18 1)
    (![552774353318, 101764201348, 552774353318, 0, 1, 194169418432, 229915461414, 0, 83885421775, 59829007246, 194169418432, 0, 94926637302, 515633295911, 229915461414, 0, 0, 515633295912, 201500008915, 170171850577, 856726447141, 300936675152, 92726973504, 109797748126, 194169418432, 0, 94926637302, 515633295911, 0, 0, 300936675152, 799162766836, 134673498195, 19272402554, 92726973504, 0, 130011204269, 0, 98264701746, 202671973406, 57973095424, 72038108846]) (branchResiduals127 18 1) 13565580
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck127_19_0 :
    integerResidualCheck 127 19 0 (dualNumerators127 19 0) ∧
    integerMassCheck 127 19 0 (dualNumerators127 19 0) := by
  apply integerChecks_of_simple 127 19 0 (dualNumerators127 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 168672709502, 902520362746, 645216866088, 0, 136231332822, 768418291818, 648421029826, 25293932239, 403390917798, 501258706842]) (branchResiduals127 19 0) 8248658
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck127_19_1 :
    integerResidualCheck 127 19 1 (dualNumerators127 19 1) ∧
    integerMassCheck 127 19 1 (dualNumerators127 19 1) := by
  apply integerChecks_of_simple 127 19 1 (dualNumerators127 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 394588886086, 369410587551, 460183470977, 0, 371450951992, 273765914097, 475079366460, 512398369190, 287707656866, 357509209222]) (branchResiduals127 19 1) 8248658
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck127_20_0 :
    integerResidualCheck 127 20 0 (dualNumerators127 20 0) ∧
    integerMassCheck 127 20 0 (dualNumerators127 20 0) := by
  apply integerChecks_of_simple 127 20 0 (dualNumerators127 20 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 1540462609577, 220447348059, 1060657349048, 0, 1487132967409, 0, 1124000645334, 2318263067540, 663125166110, 824007801299]) (branchResiduals127 20 0) 35312013
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck127_20_1 :
    integerResidualCheck 127 20 1 (dualNumerators127 20 1) ∧
    integerMassCheck 127 20 1 (dualNumerators127 20 1) := by
  apply integerChecks_of_simple 127 20 1 (dualNumerators127 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals127 20 1) 35312013
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck127_21_0 :
    integerResidualCheck 127 21 0 (dualNumerators127 21 0) ∧
    integerMassCheck 127 21 0 (dualNumerators127 21 0) := by
  apply integerChecks_of_simple 127 21 0 (dualNumerators127 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 759767979803, 549133445537, 757887471419, 892563449519, 583650214286, 725251211053]) (branchResiduals127 21 0) 11182451
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck127_21_1 :
    integerResidualCheck 127 21 1 (dualNumerators127 21 1) ∧
    integerMassCheck 127 21 1 (dualNumerators127 21 1) := by
  apply integerChecks_of_simple 127 21 1 (dualNumerators127 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 917967404853, 905358228364, 3460174706, 161253783489, 102979506989, 127963650709, 0, 0, 102979506989, 127963650709]) (branchResiduals127 21 1) 11182451
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck127_22_0 :
    integerResidualCheck 127 22 0 (dualNumerators127 22 0) ∧
    integerMassCheck 127 22 0 (dualNumerators127 22 0) := by
  apply integerChecks_of_simple 127 22 0 (dualNumerators127 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 608963496407, 155035977230, 85708482881, 374474988096, 645216866088, 0, 95974191249, 705361889470, 287707656866, 357509209222]) (branchResiduals127 22 0) 6465674
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck127_22_1 :
    integerResidualCheck 127 22 1 (dualNumerators127 22 1) ∧
    integerMassCheck 127 22 1 (dualNumerators127 22 1) := by
  apply integerChecks_of_simple 127 22 1 (dualNumerators127 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 108732662288, 12539033463, 1534493418, 71511669319, 45668611868, 56748400418, 0, 0, 45668611868, 56748400418]) (branchResiduals127 22 1) 6465674
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck127_23_0 :
    integerResidualCheck 127 23 0 (dualNumerators127 23 0) ∧
    integerMassCheck 127 23 0 (dualNumerators127 23 0) := by
  apply integerChecks_of_simple 127 23 0 (dualNumerators127 23 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 540462609577, 1220447348059, 1060657349048, 0, 1487132967409, 0, 1124000645334, 2318263067540, 663125166110, 824007801299]) (branchResiduals127 23 0) 35297932
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck127_23_1 :
    integerResidualCheck 127 23 1 (dualNumerators127 23 1) ∧
    integerMassCheck 127 23 1 (dualNumerators127 23 1) := by
  apply integerChecks_of_simple 127 23 1 (dualNumerators127 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1830784228945, 211125748477, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals127 23 1) 35297932
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck127_24_0 :
    integerResidualCheck 127 24 0 (dualNumerators127 24 0) ∧
    integerMassCheck 127 24 0 (dualNumerators127 24 0) := by
  apply integerChecks_of_simple 127 24 0 (dualNumerators127 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 512185690040, 559007382209, 705016048726, 601815130180, 477654049462, 593539022787]) (branchResiduals127 24 0) 9356857
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck127_24_1 :
    integerResidualCheck 127 24 1 (dualNumerators127 24 1) ∧
    integerMassCheck 127 24 1 (dualNumerators127 24 1) := by
  apply integerChecks_of_simple 127 24 1 (dualNumerators127 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 690777049383, 178822020994, 66021086067, 82038644814, 0, 0, 66021086067, 82038644814]) (branchResiduals127 24 1) 9356857
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck127_25_0 :
    integerResidualCheck 127 25 0 (dualNumerators127 25 0) ∧
    integerMassCheck 127 25 0 (dualNumerators127 25 0) := by
  apply integerChecks_of_simple 127 25 0 (dualNumerators127 25 0)
    (![34966365041, 6437209308, 34966365041, 0, 1, 22997469043, 27231238312, 0, 632721051475, 451271169324, 515942815115, 0, 137926201422, 749203214751, 610926434029, 0, 0, 749203214752, 1519850467647, 1283552135172, 54193197479, 35643006641, 699410063567, 828169486116, 515942815115, 0, 137926201422, 749203214751, 0, 0, 799642480277, 1161164957288, 492609519496, 668555437793, 54193197479, 0, 457443319543, 523189836115, 0, 35643006641, 437272616834, 543360538824]) (branchResiduals127 25 0) 8671199
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck127_25_1 :
    integerResidualCheck 127 25 1 (dualNumerators127 25 1) ∧
    integerMassCheck 127 25 1 (dualNumerators127 25 1) := by
  apply integerChecks_of_simple 127 25 1 (dualNumerators127 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals127 25 1) 8671199
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck127_26_0 :
    integerResidualCheck 127 26 0 (dualNumerators127 26 0) ∧
    integerMassCheck 127 26 0 (dualNumerators127 26 0) := by
  apply integerChecks_of_simple 127 26 0 (dualNumerators127 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals127 26 0) 15099566
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck127_26_1 :
    integerResidualCheck 127 26 1 (dualNumerators127 26 1) ∧
    integerMassCheck 127 26 1 (dualNumerators127 26 1) := by
  apply integerChecks_of_simple 127 26 1 (dualNumerators127 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 1025837005087, 204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals127 26 1) 15099566
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck127_27_0 :
    integerResidualCheck 127 27 0 (dualNumerators127 27 0) ∧
    integerMassCheck 127 27 0 (dualNumerators127 27 0) := by
  apply integerChecks_of_simple 127 27 0 (dualNumerators127 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 436855949686, 304617712691, 340673826058, 423325647580]) (branchResiduals127 27 0) 7338775
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck127_27_1 :
    integerResidualCheck 127 27 1 (dualNumerators127 27 1) ∧
    integerMassCheck 127 27 1 (dualNumerators127 27 1) := by
  apply integerChecks_of_simple 127 27 1 (dualNumerators127 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 585228946605, 946708994604, 377837583379, 0, 538833784902, 754926527212, 385949753226, 259267112862, 236224837801, 293536000677]) (branchResiduals127 27 1) 7338775
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck127_28_0 :
    integerResidualCheck 127 28 0 (dualNumerators127 28 0) ∧
    integerMassCheck 127 28 0 (dualNumerators127 28 0) := by
  apply integerChecks_of_simple 127 28 0 (dualNumerators127 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 374399059503, 471423145846, 287707656866, 357509209222]) (branchResiduals127 28 0) 10335557
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck127_28_1 :
    integerResidualCheck 127 28 1 (dualNumerators127 28 1) ∧
    integerMassCheck 127 28 1 (dualNumerators127 28 1) := by
  apply integerChecks_of_simple 127 28 1 (dualNumerators127 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 484442151291, 449974794159, 2156352207, 100492021777, 456143077212, 332995651238, 0, 0, 64175975503, 79745886859]) (branchResiduals127 28 1) 10335557
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck127_29_0 :
    integerResidualCheck 127 29 0 (dualNumerators127 29 0) ∧
    integerMassCheck 127 29 0 (dualNumerators127 29 0) := by
  apply integerChecks_of_simple 127 29 0 (dualNumerators127 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals127 29 0) 40352153
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck127_29_1 :
    integerResidualCheck 127 29 1 (dualNumerators127 29 1) ∧
    integerMassCheck 127 29 1 (dualNumerators127 29 1) := by
  apply integerChecks_of_simple 127 29 1 (dualNumerators127 29 1)
    (![813650000253, 149790673094, 813650000253, 0, 1, 30189853607, 35747720615, 0, 1140807387415, 813650000252, 30189853607, 0, 248683411329, 1350826813920, 35747720615, 0, 0, 1350826813921, 2740317612662, 2314267487267, 1261048870572, 46790242466, 1261048870572, 1493204415423, 30189853607, 0, 248683411329, 1350826813920, 0, 0, 46790242466, 2093601213671, 1831504430445, 262096783226, 72117429420, 1188931441153, 1768099142126, 0, 46790242466, 0, 788410359408, 979688782719]) (branchResiduals127 29 1) 40352153
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck127_30_0 :
    integerResidualCheck 127 30 0 (dualNumerators127 30 0) ∧
    integerMassCheck 127 30 0 (dualNumerators127 30 0) := by
  apply integerChecks_of_simple 127 30 0 (dualNumerators127 30 0)
    (![49325597255, 9080703511, 49325597255, 0, 0, 3298611714, 3905876838, 0, 69158736213, 49325597255, 3298611714, 0, 15075840703, 81890664738, 3905876838, 0, 0, 81890664738, 166125241653, 1140296965504, 76448090321, 5112407761, 76448090321, 90521968404, 3298611714, 0, 15075840703, 81890664738, 0, 0, 5112407761, 126919597181, 108811353134, 18108244048, 6591197296, 69856893026, 104967558241, 2219249557, 5112407761, 0, 107186807798, 0]) (branchResiduals127 30 0) 7680628
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck127_30_1 :
    integerResidualCheck 127 30 1 (dualNumerators127 30 1) ∧
    integerMassCheck 127 30 1 (dualNumerators127 30 1) := by
  apply integerChecks_of_simple 127 30 1 (dualNumerators127 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 277657182166, 626992442474, 544901951702, 0, 250259619582, 513739854055, 556554858415, 372095930671, 281282522283, 482716951355]) (branchResiduals127 30 1) 7680628
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck127_31_0 :
    integerResidualCheck 127 31 0 (dualNumerators127 31 0) ∧
    integerMassCheck 127 31 0 (dualNumerators127 31 0) := by
  apply integerChecks_of_simple 127 31 0 (dualNumerators127 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 1032415642125, 1, 592902192609, 0, 1222480453651, 0, 500720887661, 0, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642125, 0, 592902192609, 0, 0, 0, 1600106408231, 776050524992, 678897187053, 97153337939, 898753891846, 674088683815, 655394283556, 0, 905514817789, 694591590443, 655394283556, 0]) (branchResiduals127 31 0) 32891612
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck127_31_1 :
    integerResidualCheck 127 31 1 (dualNumerators127 31 1) ∧
    integerMassCheck 127 31 1 (dualNumerators127 31 1) := by
  apply integerChecks_of_simple 127 31 1 (dualNumerators127 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 741061026801, 808805463926, 18993131489, 744564115640, 327950144489, 1221916346239]) (branchResiduals127 31 1) 32891612
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck127_32_0 :
    integerResidualCheck 127 32 0 (dualNumerators127 32 0) ∧
    integerMassCheck 127 32 0 (dualNumerators127 32 0) := by
  apply integerChecks_of_simple 127 32 0 (dualNumerators127 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 0, 2743468108582, 2028778803022, 0, 505064750776, 2743468108580, 1713354977902, 2, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 2028778803022, 0, 0, 0, 4252009289869, 2655471466972, 2323034456095, 332437010877, 91471945490, 1508010932335, 2242612772688, 0, 163638085097, 4088371204772, 0, 2242612772688]) (branchResiduals127 32 0) 67647473
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck127_32_1 :
    integerResidualCheck 127 32 1 (dualNumerators127 32 1) ∧
    integerMassCheck 127 32 1 (dualNumerators127 32 1) := by
  apply integerChecks_of_simple 127 32 1 (dualNumerators127 32 1)
    (![830518849052, 152896180641, 830518849053, 0, 1, 55540314888, 65765130409, 0, 1164458966499, 830518849051, 55540314888, 0, 253839194360, 1378832582089, 65765130409, 0, 0, 1378832582090, 2797130742946, 2362247611782, 1287193334063, 86080072929, 1287193334063, 1524162000997, 55540314888, 0, 253839194360, 1378832582089, 0, 0, 86080072929, 2137006415304, 1832109184628, 304897230676, 110979164901, 1176214169163, 1767389357845, 37366574157, 86080072929, 0, 1804755932001, 0]) (branchResiduals127 32 1) 67647473
    branchSparseDots127 branchIntegerCurvature127 branchDots127
    branchIntegerCurvature127_entry rfl
    (congrFun (congrFun branchResiduals127_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks127 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 127 j s (dualNumerators127 j s) ∧
    integerMassCheck 127 j s (dualNumerators127 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck127_0_0
    · exact integerCheck127_0_1
  · fin_cases s
    · exact integerCheck127_1_0
    · exact integerCheck127_1_1
  · fin_cases s
    · exact integerCheck127_2_0
    · exact integerCheck127_2_1
  · fin_cases s
    · exact integerCheck127_3_0
    · exact integerCheck127_3_1
  · fin_cases s
    · exact integerCheck127_4_0
    · exact integerCheck127_4_1
  · fin_cases s
    · exact integerCheck127_5_0
    · exact integerCheck127_5_1
  · fin_cases s
    · exact integerCheck127_6_0
    · exact integerCheck127_6_1
  · fin_cases s
    · exact integerCheck127_7_0
    · exact integerCheck127_7_1
  · fin_cases s
    · exact integerCheck127_8_0
    · exact integerCheck127_8_1
  · fin_cases s
    · exact integerCheck127_9_0
    · exact integerCheck127_9_1
  · fin_cases s
    · exact integerCheck127_10_0
    · exact integerCheck127_10_1
  · fin_cases s
    · exact integerCheck127_11_0
    · exact integerCheck127_11_1
  · fin_cases s
    · exact integerCheck127_12_0
    · exact integerCheck127_12_1
  · fin_cases s
    · exact integerCheck127_13_0
    · exact integerCheck127_13_1
  · fin_cases s
    · exact integerCheck127_14_0
    · exact integerCheck127_14_1
  · fin_cases s
    · exact integerCheck127_15_0
    · exact integerCheck127_15_1
  · fin_cases s
    · exact integerCheck127_16_0
    · exact integerCheck127_16_1
  · fin_cases s
    · exact integerCheck127_17_0
    · exact integerCheck127_17_1
  · fin_cases s
    · exact integerCheck127_18_0
    · exact integerCheck127_18_1
  · fin_cases s
    · exact integerCheck127_19_0
    · exact integerCheck127_19_1
  · fin_cases s
    · exact integerCheck127_20_0
    · exact integerCheck127_20_1
  · fin_cases s
    · exact integerCheck127_21_0
    · exact integerCheck127_21_1
  · fin_cases s
    · exact integerCheck127_22_0
    · exact integerCheck127_22_1
  · fin_cases s
    · exact integerCheck127_23_0
    · exact integerCheck127_23_1
  · fin_cases s
    · exact integerCheck127_24_0
    · exact integerCheck127_24_1
  · fin_cases s
    · exact integerCheck127_25_0
    · exact integerCheck127_25_1
  · fin_cases s
    · exact integerCheck127_26_0
    · exact integerCheck127_26_1
  · fin_cases s
    · exact integerCheck127_27_0
    · exact integerCheck127_27_1
  · fin_cases s
    · exact integerCheck127_28_0
    · exact integerCheck127_28_1
  · fin_cases s
    · exact integerCheck127_29_0
    · exact integerCheck127_29_1
  · fin_cases s
    · exact integerCheck127_30_0
    · exact integerCheck127_30_1
  · fin_cases s
    · exact integerCheck127_31_0
    · exact integerCheck127_31_1
  · fin_cases s
    · exact integerCheck127_32_0
    · exact integerCheck127_32_1

end ElevenSquare.Tasks.T06
