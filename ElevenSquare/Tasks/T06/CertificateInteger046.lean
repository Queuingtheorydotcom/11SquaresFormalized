import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual046
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
import ElevenSquare.Tasks.T06.SparseColumn35
import ElevenSquare.Tasks.T06.SparseColumn36
import ElevenSquare.Tasks.T06.SparseColumn37
import ElevenSquare.Tasks.T06.SparseColumn38
import ElevenSquare.Tasks.T06.SparseColumn39
import ElevenSquare.Tasks.T06.SparseColumn40
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn44
import ElevenSquare.Tasks.T06.SparseColumn46
import ElevenSquare.Tasks.T06.SparseColumn52
import ElevenSquare.Tasks.T06.SparseColumn53

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix046 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral43, roundedGradientLiteral44, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix046_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = branchIntegerMatrix046 := by
  change roundedGradients ∘ branchRows 46 = branchIntegerMatrix046
  rw [show branchRows 46 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 52, 53, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral43_eq, roundedGradientLiteral44_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, branchIntegerMatrix046]

theorem branchColumn046_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 0) i) = _
  rw [branchColumn046_0]
  exact sparseColumn00_sum n

theorem branchColumn046_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 1) i) = _
  rw [branchColumn046_1]
  exact sparseColumn01_sum n

theorem branchColumn046_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 2) i) = _
  rw [branchColumn046_2]
  exact sparseColumn02_sum n

theorem branchColumn046_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 3) i) = _
  rw [branchColumn046_3]
  exact sparseColumn03_sum n

theorem branchColumn046_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 4) i) = _
  rw [branchColumn046_4]
  exact sparseColumn04_sum n

theorem branchColumn046_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 5) i) = _
  rw [branchColumn046_5]
  exact sparseColumn05_sum n

theorem branchColumn046_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 6) i) = _
  rw [branchColumn046_6]
  exact sparseColumn06_sum n

theorem branchColumn046_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 7) i) = _
  rw [branchColumn046_7]
  exact sparseColumn07_sum n

theorem branchColumn046_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 8) i) = _
  rw [branchColumn046_8]
  exact sparseColumn08_sum n

theorem branchColumn046_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 9) i) = _
  rw [branchColumn046_9]
  exact sparseColumn09_sum n

theorem branchColumn046_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 10) i) = _
  rw [branchColumn046_10]
  exact sparseColumn10_sum n

theorem branchColumn046_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 11) i) = _
  rw [branchColumn046_11]
  exact sparseColumn11_sum n

theorem branchColumn046_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 12) i) = _
  rw [branchColumn046_12]
  exact sparseColumn35_sum n

theorem branchColumn046_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 13) i) = _
  rw [branchColumn046_13]
  exact sparseColumn36_sum n

theorem branchColumn046_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 14) = sparseColumn37 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 14) = sparseDot37 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 14) i) = _
  rw [branchColumn046_14]
  exact sparseColumn37_sum n

theorem branchColumn046_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 15) i) = _
  rw [branchColumn046_15]
  exact sparseColumn38_sum n

theorem branchColumn046_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 16) i) = _
  rw [branchColumn046_16]
  exact sparseColumn39_sum n

theorem branchColumn046_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 17) = sparseColumn40 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 17) = sparseDot40 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 17) i) = _
  rw [branchColumn046_17]
  exact sparseColumn40_sum n

theorem branchColumn046_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 18) i) = _
  rw [branchColumn046_18]
  exact sparseColumn18_sum n

theorem branchColumn046_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 19) i) = _
  rw [branchColumn046_19]
  exact sparseColumn19_sum n

theorem branchColumn046_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 20) = sparseColumn52 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 20) = sparseDot52 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 20) i) = _
  rw [branchColumn046_20]
  exact sparseColumn52_sum n

theorem branchColumn046_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 21) i) = _
  rw [branchColumn046_21]
  exact sparseColumn21_sum n

theorem branchColumn046_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 22) i) = _
  rw [branchColumn046_22]
  exact sparseColumn22_sum n

theorem branchColumn046_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 23) = sparseColumn53 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 23) = sparseDot53 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 23) i) = _
  rw [branchColumn046_23]
  exact sparseColumn53_sum n

theorem branchColumn046_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 24) i) = _
  rw [branchColumn046_24]
  exact sparseColumn24_sum n

theorem branchColumn046_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 25) i) = _
  rw [branchColumn046_25]
  exact sparseColumn25_sum n

theorem branchColumn046_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 26) = sparseColumn44 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 26) = sparseDot44 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 26) i) = _
  rw [branchColumn046_26]
  exact sparseColumn44_sum n

theorem branchColumn046_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 27) i) = _
  rw [branchColumn046_27]
  exact sparseColumn27_sum n

theorem branchColumn046_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 28) i) = _
  rw [branchColumn046_28]
  exact sparseColumn28_sum n

theorem branchColumn046_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 29) = sparseColumn46 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 29) = sparseDot46 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 29) i) = _
  rw [branchColumn046_29]
  exact sparseColumn46_sum n

theorem branchColumn046_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 30) i) = _
  rw [branchColumn046_30]
  exact sparseColumn30_sum n

theorem branchColumn046_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 31) i) = _
  rw [branchColumn046_31]
  exact sparseColumn31_sum n

theorem branchColumn046_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 46 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 46 i)) = _
  rw [branchIntegerMatrix046_eq]
  simp only [branchIntegerMatrix046, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot046_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 46 i) 32) i) = _
  rw [branchColumn046_32]
  exact sparseColumn43_sum n

def branchSparseDots046 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot37, sparseDot38, sparseDot39, sparseDot40, sparseDot18, sparseDot19, sparseDot52, sparseDot21, sparseDot22, sparseDot53, sparseDot24, sparseDot25, sparseDot44, sparseDot27, sparseDot28, sparseDot46, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot046_0 :
    branchSparseDots046 0 = sparseDot00 := rfl

private theorem branchSparseDot046_1 :
    branchSparseDots046 1 = sparseDot01 := rfl

private theorem branchSparseDot046_2 :
    branchSparseDots046 2 = sparseDot02 := rfl

private theorem branchSparseDot046_3 :
    branchSparseDots046 3 = sparseDot03 := rfl

private theorem branchSparseDot046_4 :
    branchSparseDots046 4 = sparseDot04 := rfl

private theorem branchSparseDot046_5 :
    branchSparseDots046 5 = sparseDot05 := rfl

private theorem branchSparseDot046_6 :
    branchSparseDots046 6 = sparseDot06 := rfl

private theorem branchSparseDot046_7 :
    branchSparseDots046 7 = sparseDot07 := rfl

private theorem branchSparseDot046_8 :
    branchSparseDots046 8 = sparseDot08 := rfl

private theorem branchSparseDot046_9 :
    branchSparseDots046 9 = sparseDot09 := rfl

private theorem branchSparseDot046_10 :
    branchSparseDots046 10 = sparseDot10 := rfl

private theorem branchSparseDot046_11 :
    branchSparseDots046 11 = sparseDot11 := rfl

private theorem branchSparseDot046_12 :
    branchSparseDots046 12 = sparseDot35 := rfl

private theorem branchSparseDot046_13 :
    branchSparseDots046 13 = sparseDot36 := rfl

private theorem branchSparseDot046_14 :
    branchSparseDots046 14 = sparseDot37 := rfl

private theorem branchSparseDot046_15 :
    branchSparseDots046 15 = sparseDot38 := rfl

private theorem branchSparseDot046_16 :
    branchSparseDots046 16 = sparseDot39 := rfl

private theorem branchSparseDot046_17 :
    branchSparseDots046 17 = sparseDot40 := rfl

private theorem branchSparseDot046_18 :
    branchSparseDots046 18 = sparseDot18 := rfl

private theorem branchSparseDot046_19 :
    branchSparseDots046 19 = sparseDot19 := rfl

private theorem branchSparseDot046_20 :
    branchSparseDots046 20 = sparseDot52 := rfl

private theorem branchSparseDot046_21 :
    branchSparseDots046 21 = sparseDot21 := rfl

private theorem branchSparseDot046_22 :
    branchSparseDots046 22 = sparseDot22 := rfl

private theorem branchSparseDot046_23 :
    branchSparseDots046 23 = sparseDot53 := rfl

private theorem branchSparseDot046_24 :
    branchSparseDots046 24 = sparseDot24 := rfl

private theorem branchSparseDot046_25 :
    branchSparseDots046 25 = sparseDot25 := rfl

private theorem branchSparseDot046_26 :
    branchSparseDots046 26 = sparseDot44 := rfl

private theorem branchSparseDot046_27 :
    branchSparseDots046 27 = sparseDot27 := rfl

private theorem branchSparseDot046_28 :
    branchSparseDots046 28 = sparseDot28 := rfl

private theorem branchSparseDot046_29 :
    branchSparseDots046 29 = sparseDot46 := rfl

private theorem branchSparseDot046_30 :
    branchSparseDots046 30 = sparseDot30 := rfl

private theorem branchSparseDot046_31 :
    branchSparseDots046 31 = sparseDot31 := rfl

private theorem branchSparseDot046_32 :
    branchSparseDots046 32 = sparseDot43 := rfl

theorem branchDots046 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 46 i) k) = branchSparseDots046 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot046_0 n
      _ = _ := congrFun branchSparseDot046_0.symm n
  · calc
      _ = sparseDot01 n := branchDot046_1 n
      _ = _ := congrFun branchSparseDot046_1.symm n
  · calc
      _ = sparseDot02 n := branchDot046_2 n
      _ = _ := congrFun branchSparseDot046_2.symm n
  · calc
      _ = sparseDot03 n := branchDot046_3 n
      _ = _ := congrFun branchSparseDot046_3.symm n
  · calc
      _ = sparseDot04 n := branchDot046_4 n
      _ = _ := congrFun branchSparseDot046_4.symm n
  · calc
      _ = sparseDot05 n := branchDot046_5 n
      _ = _ := congrFun branchSparseDot046_5.symm n
  · calc
      _ = sparseDot06 n := branchDot046_6 n
      _ = _ := congrFun branchSparseDot046_6.symm n
  · calc
      _ = sparseDot07 n := branchDot046_7 n
      _ = _ := congrFun branchSparseDot046_7.symm n
  · calc
      _ = sparseDot08 n := branchDot046_8 n
      _ = _ := congrFun branchSparseDot046_8.symm n
  · calc
      _ = sparseDot09 n := branchDot046_9 n
      _ = _ := congrFun branchSparseDot046_9.symm n
  · calc
      _ = sparseDot10 n := branchDot046_10 n
      _ = _ := congrFun branchSparseDot046_10.symm n
  · calc
      _ = sparseDot11 n := branchDot046_11 n
      _ = _ := congrFun branchSparseDot046_11.symm n
  · calc
      _ = sparseDot35 n := branchDot046_12 n
      _ = _ := congrFun branchSparseDot046_12.symm n
  · calc
      _ = sparseDot36 n := branchDot046_13 n
      _ = _ := congrFun branchSparseDot046_13.symm n
  · calc
      _ = sparseDot37 n := branchDot046_14 n
      _ = _ := congrFun branchSparseDot046_14.symm n
  · calc
      _ = sparseDot38 n := branchDot046_15 n
      _ = _ := congrFun branchSparseDot046_15.symm n
  · calc
      _ = sparseDot39 n := branchDot046_16 n
      _ = _ := congrFun branchSparseDot046_16.symm n
  · calc
      _ = sparseDot40 n := branchDot046_17 n
      _ = _ := congrFun branchSparseDot046_17.symm n
  · calc
      _ = sparseDot18 n := branchDot046_18 n
      _ = _ := congrFun branchSparseDot046_18.symm n
  · calc
      _ = sparseDot19 n := branchDot046_19 n
      _ = _ := congrFun branchSparseDot046_19.symm n
  · calc
      _ = sparseDot52 n := branchDot046_20 n
      _ = _ := congrFun branchSparseDot046_20.symm n
  · calc
      _ = sparseDot21 n := branchDot046_21 n
      _ = _ := congrFun branchSparseDot046_21.symm n
  · calc
      _ = sparseDot22 n := branchDot046_22 n
      _ = _ := congrFun branchSparseDot046_22.symm n
  · calc
      _ = sparseDot53 n := branchDot046_23 n
      _ = _ := congrFun branchSparseDot046_23.symm n
  · calc
      _ = sparseDot24 n := branchDot046_24 n
      _ = _ := congrFun branchSparseDot046_24.symm n
  · calc
      _ = sparseDot25 n := branchDot046_25 n
      _ = _ := congrFun branchSparseDot046_25.symm n
  · calc
      _ = sparseDot44 n := branchDot046_26 n
      _ = _ := congrFun branchSparseDot046_26.symm n
  · calc
      _ = sparseDot27 n := branchDot046_27 n
      _ = _ := congrFun branchSparseDot046_27.symm n
  · calc
      _ = sparseDot28 n := branchDot046_28 n
      _ = _ := congrFun branchSparseDot046_28.symm n
  · calc
      _ = sparseDot46 n := branchDot046_29 n
      _ = _ := congrFun branchSparseDot046_29.symm n
  · calc
      _ = sparseDot30 n := branchDot046_30 n
      _ = _ := congrFun branchSparseDot046_30.symm n
  · calc
      _ = sparseDot31 n := branchDot046_31 n
      _ = _ := congrFun branchSparseDot046_31.symm n
  · calc
      _ = sparseDot43 n := branchDot046_32 n
      _ = _ := congrFun branchSparseDot046_32.symm n

def branchIntegerCurvature046 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 33332260, 33780595, 79795748, 101955390, 101955390, 44932602, 44932602, 115699695, 115699695, 88123140, 88123140, 289103692, 289103692]

theorem branchIntegerCurvature046_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 46 i)) = branchIntegerCurvature046 := by
  change curvatureNumerators ∘ branchRows 46 = branchIntegerCurvature046
  rw [show branchRows 46 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 43, 44, 30, 31, 52, 53, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature046_entry (i : Fin 42) :
    curvatureNumerators (branchRows 46 i) = branchIntegerCurvature046 i :=
  congrFun branchIntegerCurvature046_eq i

def branchResiduals046 : Fin 33 → Fin 2 → ℕ := ![![1300830809160083, 33000000000000], ![1544537125645410, 33000000000000], ![1582559236705566, 1336281053561440], ![33000000000000, 1023700626813105], ![857399499449444, 33000000000000], ![1054734102044107, 893034780534369], ![720656430648453, 622122527367398], ![33000000000000, 759403503291493], ![1578770830654813, 1130699494393508], ![1024602314247607, 33000000000000], ![33000000000000, 777496447572864], ![506654482090070, 466180207358330], ![989200626813105, 66000000000000], ![33000000000000, 857389867884069], ![1052694364247674, 891534780534402], ![472644618929580, 33000000000000], ![66000000000000, 743985444367439], ![953242224117662, 328527687415132], ![621886698130741, 247405410024947], ![630656046129883, 513693640273388], ![1231898543167596, 949313872923868], ![756191434898802, 388178345140012], ![470983248534445, 103778632186673], ![1231898543167596, 949313872923868], ![670630840242895, 232003409392821], ![503932389513439, 225581994926756], ![401579096206218, 853076072054392], ![411819502736388, 550635701193468], ![286791123956719, 309993395943330], ![401579096206218, 949313872923868], ![103778632186673, 556092469195622], ![968663138331286, 650877065214062], ![2021816915245312, 949313872923868]]

theorem branchResiduals046_eq : residualNumerators 46 = branchResiduals046 := rfl

theorem integerCheck046_0_0 :
    integerResidualCheck 46 0 0 (dualNumerators046 0 0) ∧
    integerMassCheck 46 0 0 (dualNumerators046 0 0) := by
  apply integerChecks_of_simple 46 0 0 (dualNumerators046 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 511481744370, 1661564579697, 1308901425339, 0, 227681483087, 1607511062798, 1485808378804, 481205215181, 818327875519, 1016864670366]) (branchResiduals046 0 0) 18767167
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck046_0_1 :
    integerResidualCheck 46 0 1 (dualNumerators046 0 1) ∧
    integerMassCheck 46 0 1 (dualNumerators046 0 1) := by
  apply integerChecks_of_simple 46 0 1 (dualNumerators046 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals046 0 1) 18767167
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck046_1_0 :
    integerResidualCheck 46 1 0 (dualNumerators046 1 0) ∧
    integerMassCheck 46 1 0 (dualNumerators046 1 0) := by
  apply integerChecks_of_simple 46 1 0 (dualNumerators046 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 605644092726, 1967453938394, 1549866490727, 0, 269597002772, 1903449321295, 1759341515999, 569793739799, 968979732271, 1204066591796]) (branchResiduals046 1 0) 22176635
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck046_1_1 :
    integerResidualCheck 46 1 1 (dualNumerators046 1 1) ∧
    integerMassCheck 46 1 1 (dualNumerators046 1 1) := by
  apply integerChecks_of_simple 46 1 1 (dualNumerators046 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals046 1 1) 22176635
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck046_2_0 :
    integerResidualCheck 46 2 0 (dualNumerators046 2 0) ∧
    integerMassCheck 46 2 0 (dualNumerators046 2 0) := by
  apply integerChecks_of_simple 46 2 0 (dualNumerators046 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 605644092727, 1967453938395, 1549866490728, 0, 269597002773, 1903449321296, 1759341516001, 569793739799, 968979732272, 1204066591797]) (branchResiduals046 2 0) 22681452
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck046_2_1 :
    integerResidualCheck 46 2 1 (dualNumerators046 2 1) ∧
    integerMassCheck 46 2 1 (dualNumerators046 2 1) := by
  apply integerChecks_of_simple 46 2 1 (dualNumerators046 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 511481744370, 1661564579696, 1308901425338, 0, 227681483087, 1607511062796, 1485808378803, 481205215180, 818327875518, 1016864670365]) (branchResiduals046 2 1) 22681452
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck046_3_0 :
    integerResidualCheck 46 3 0 (dualNumerators046 3 0) ∧
    integerMassCheck 46 3 0 (dualNumerators046 3 0) := by
  apply integerChecks_of_simple 46 3 0 (dualNumerators046 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals046 3 0) 16360330
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck046_3_1 :
    integerResidualCheck 46 3 1 (dualNumerators046 3 1) ∧
    integerMassCheck 46 3 1 (dualNumerators046 3 1) := by
  apply integerChecks_of_simple 46 3 1 (dualNumerators046 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000001, 0, 203380245200, 1104743927907, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 403011152868, 1309194441832, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals046 3 1) 16360330
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck046_4_0 :
    integerResidualCheck 46 4 0 (dualNumerators046 4 0) ∧
    integerMassCheck 46 4 0 (dualNumerators046 4 0) := by
  apply integerChecks_of_simple 46 4 0 (dualNumerators046 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757645, 932984170265, 1000000000001, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 340353104975, 1105647796899, 870976665588, 0, 151505113461, 1069679196819, 988695101419, 320206323920, 544536410901, 676647899379]) (branchResiduals046 4 0) 13760362
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck046_4_1 :
    integerResidualCheck 46 4 1 (dualNumerators046 4 1) ∧
    integerMassCheck 46 4 1 (dualNumerators046 4 1) := by
  apply integerChecks_of_simple 46 4 1 (dualNumerators046 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals046 4 1) 13760362
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck046_5_0 :
    integerResidualCheck 46 5 0 (dualNumerators046 5 0) ∧
    integerMassCheck 46 5 0 (dualNumerators046 5 0) := by
  apply integerChecks_of_simple 46 5 0 (dualNumerators046 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245201, 1104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 403011152868, 1309194441833, 1031321016288, 0, 179396778078, 1266604123797, 1170711084557, 379155406172, 644784030255, 801216871620]) (branchResiduals046 5 0) 17641130
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck046_5_1 :
    integerResidualCheck 46 5 1 (dualNumerators046 5 1) ∧
    integerMassCheck 46 5 1 (dualNumerators046 5 1) := by
  apply integerChecks_of_simple 46 5 1 (dualNumerators046 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170264, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 340353104975, 1105647796898, 870976665588, 0, 151505113461, 1069679196818, 988695101418, 320206323920, 544536410901, 676647899378]) (branchResiduals046 5 1) 17641130
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck046_6_0 :
    integerResidualCheck 46 6 0 (dualNumerators046 6 0) ∧
    integerMassCheck 46 6 0 (dualNumerators046 6 0) := by
  apply integerChecks_of_simple 46 6 0 (dualNumerators046 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 659499318402, 1175693227483, 2719950702, 106626845062, 818327875519, 1016864670366]) (branchResiduals046 6 0) 8962451
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck046_6_1 :
    integerResidualCheck 46 6 1 (dualNumerators046 6 1) ∧
    integerMassCheck 46 6 1 (dualNumerators046 6 1) := by
  apply integerChecks_of_simple 46 6 1 (dualNumerators046 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals046 6 1) 8962451
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck046_7_0 :
    integerResidualCheck 46 7 0 (dualNumerators046 7 0) ∧
    integerMassCheck 46 7 0 (dualNumerators046 7 0) := by
  apply integerChecks_of_simple 46 7 0 (dualNumerators046 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals046 7 0) 10424794
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck046_7_1 :
    integerResidualCheck 46 7 1 (dualNumerators046 7 1) ∧
    integerMassCheck 46 7 1 (dualNumerators046 7 1) := by
  apply integerChecks_of_simple 46 7 1 (dualNumerators046 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646810, 830103123887, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675220, 1, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 302822046364, 983726969199, 774933245365, 0, 134798501387, 951724660649, 879670758001, 284896869900, 484489866137, 602033295899]) (branchResiduals046 7 1) 10424794
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck046_8_0 :
    integerResidualCheck 46 8 0 (dualNumerators046 8 0) ∧
    integerMassCheck 46 8 0 (dualNumerators046 8 0) := by
  apply integerChecks_of_simple 46 8 0 (dualNumerators046 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293619, 1660206247774, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350440, 2, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 605644092727, 1967453938397, 1549866490730, 0, 269597002773, 1903449321298, 1759341516002, 569793739800, 968979732273, 1204066591798]) (branchResiduals046 8 0) 22681452
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck046_8_1 :
    integerResidualCheck 46 8 1 (dualNumerators046 8 1) ∧
    integerMassCheck 46 8 1 (dualNumerators046 8 1) := by
  apply integerChecks_of_simple 46 8 1 (dualNumerators046 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590429, 217988955956, 0, 1402086139075, 1269150346660, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546384, 0, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 431959261166, 1403233284717, 1105400337063, 0, 192282767270, 1357583723456, 1254802730706, 406389967006, 691098574663, 858767916063]) (branchResiduals046 8 1) 22681452
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck046_9_0 :
    integerResidualCheck 46 9 0 (dualNumerators046 9 0) ∧
    integerMassCheck 46 9 0 (dualNumerators046 9 0) := by
  apply integerChecks_of_simple 46 9 0 (dualNumerators046 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 403011152868, 1309194441832, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals046 9 0) 16350530
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck046_9_1 :
    integerResidualCheck 46 9 1 (dualNumerators046 9 1) ∧
    integerMassCheck 46 9 1 (dualNumerators046 9 1) := by
  apply integerChecks_of_simple 46 9 1 (dualNumerators046 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals046 9 1) 16350530
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck046_10_0 :
    integerResidualCheck 46 10 0 (dualNumerators046 10 0) ∧
    integerMassCheck 46 10 0 (dualNumerators046 10 0) := by
  apply integerChecks_of_simple 46 10 0 (dualNumerators046 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals046 10 0) 10683139
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck046_10_1 :
    integerResidualCheck 46 10 1 (dualNumerators046 10 1) ∧
    integerMassCheck 46 10 1 (dualNumerators046 10 1) := by
  apply integerChecks_of_simple 46 10 1 (dualNumerators046 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 308083254750, 1000818170589, 788396879662, 0, 137140480825, 968259856240, 894954094286, 289846647564, 492907358117, 612492978948]) (branchResiduals046 10 1) 10683139
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck046_11_0 :
    integerResidualCheck 46 11 0 (dualNumerators046 11 0) ∧
    integerMassCheck 46 11 0 (dualNumerators046 11 0) := by
  apply integerChecks_of_simple 46 11 0 (dualNumerators046 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 191477522526, 622020771493, 489998333105, 0, 85234491332, 601785379686, 556224949284, 180143247425, 306347970271, 380671900746]) (branchResiduals046 11 0) 15120968
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck046_11_1 :
    integerResidualCheck 46 11 1 (dualNumerators046 11 1) ∧
    integerMassCheck 46 11 1 (dualNumerators046 11 1) := by
  apply integerChecks_of_simple 46 11 1 (dualNumerators046 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 174605490278, 567211442559, 446822154676, 0, 77724058423, 548759091281, 507213215908, 164269934257, 279354134309, 347129015395]) (branchResiduals046 11 1) 15120968
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck046_12_0 :
    integerResidualCheck 46 12 0 (dualNumerators046 12 0) ∧
    integerMassCheck 46 12 0 (dualNumerators046 12 0) := by
  apply integerChecks_of_simple 46 12 0 (dualNumerators046 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 403011152868, 1309194441832, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals046 12 0) 16348076
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck046_12_1 :
    integerResidualCheck 46 12 1 (dualNumerators046 12 1) ∧
    integerMassCheck 46 12 1 (dualNumerators046 12 1) := by
  apply integerChecks_of_simple 46 12 1 (dualNumerators046 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals046 12 1) 16348076
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck046_13_0 :
    integerResidualCheck 46 13 0 (dualNumerators046 13 0) ∧
    integerMassCheck 46 13 0 (dualNumerators046 13 0) := by
  apply integerChecks_of_simple 46 13 0 (dualNumerators046 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals046 13 0) 13962901
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck046_13_1 :
    integerResidualCheck 46 13 1 (dualNumerators046 13 1) ∧
    integerMassCheck 46 13 1 (dualNumerators046 13 1) := by
  apply integerChecks_of_simple 46 13 1 (dualNumerators046 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 340353104975, 1105647796899, 870976665588, 0, 151505113461, 1069679196819, 988695101419, 320206323920, 544536410901, 676647899379]) (branchResiduals046 13 1) 13962901
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck046_14_0 :
    integerResidualCheck 46 14 0 (dualNumerators046 14 0) ∧
    integerMassCheck 46 14 0 (dualNumerators046 14 0) := by
  apply integerChecks_of_simple 46 14 0 (dualNumerators046 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 403011152868, 1309194441833, 1031321016288, 0, 179396778078, 1266604123797, 1170711084557, 379155406172, 644784030255, 801216871620]) (branchResiduals046 14 0) 20161291
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck046_14_1 :
    integerResidualCheck 46 14 1 (dualNumerators046 14 1) ∧
    integerMassCheck 46 14 1 (dualNumerators046 14 1) := by
  apply integerChecks_of_simple 46 14 1 (dualNumerators046 14 1)
    (![561968834605, 103456879454, 561968834605, 0, 1, 844525275673, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 0, 1000000000000, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 340353104975, 1105647796898, 870976665588, 0, 151505113461, 1069679196818, 988695101418, 320206323920, 544536410901, 676647899378]) (branchResiduals046 14 1) 20161291
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck046_15_0 :
    integerResidualCheck 46 15 0 (dualNumerators046 15 0) ∧
    integerMassCheck 46 15 0 (dualNumerators046 15 0) := by
  apply integerChecks_of_simple 46 15 0 (dualNumerators046 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819834, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819834, 475117180167, 0, 736368196709, 813498294019, 191477522526, 622020771493, 489998333105, 0, 85234491332, 601785379685, 556224949284, 180143247425, 306347970271, 380671900746]) (branchResiduals046 15 0) 12900283
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck046_15_1 :
    integerResidualCheck 46 15 1 (dualNumerators046 15 1) ∧
    integerMassCheck 46 15 1 (dualNumerators046 15 1) := by
  apply integerChecks_of_simple 46 15 1 (dualNumerators046 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals046 15 1) 12900283
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck046_16_0 :
    integerResidualCheck 46 16 0 (dualNumerators046 16 0) ∧
    integerMassCheck 46 16 0 (dualNumerators046 16 0) := by
  apply integerChecks_of_simple 46 16 0 (dualNumerators046 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals046 16 0) 10683060
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck046_16_1 :
    integerResidualCheck 46 16 1 (dualNumerators046 16 1) ∧
    integerMassCheck 46 16 1 (dualNumerators046 16 1) := by
  apply integerChecks_of_simple 46 16 1 (dualNumerators046 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 308083254750, 1000818170589, 788396879662, 0, 137140480825, 968259856240, 894954094286, 289846647564, 492907358117, 612492978948]) (branchResiduals046 16 1) 10683060
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck046_17_0 :
    integerResidualCheck 46 17 0 (dualNumerators046 17 0) ∧
    integerMassCheck 46 17 0 (dualNumerators046 17 0) := by
  apply integerChecks_of_simple 46 17 0 (dualNumerators046 17 0)
    (![602334801078, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546386, 0, 844525275676, 602334801077, 905187143137, 0, 1184097183123, 0, 1071829546386, 0, 0, 1000000000001, 2028622458797, 1713222941254, 933538524390, 1402919220984, 933538524390, 1105400337065, 905187143137, 0, 1184097183123, 0, 0, 0, 1402919220984, 1549866490728, 364800514116, 1185065976612, 933538524390, 0, 162387657036, 1146513768304, 1059712622068, 343206598917, 583650214286, 725251211054]) (branchResiduals046 17 0) 15120968
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck046_17_1 :
    integerResidualCheck 46 17 1 (dualNumerators046 17 1) ∧
    integerMassCheck 46 17 1 (dualNumerators046 17 1) := by
  apply integerChecks_of_simple 46 17 1 (dualNumerators046 17 1)
    (![201148953074, 37030955649, 201148953074, 0, 1, 302286113723, 357936135756, 0, 282028158995, 201148953074, 0, 0, 0, 395427772555, 55650022034, 302286113723, 636234862349, 0, 677455931550, 572128657349, 311754022014, 468503118271, 311754022014, 369147059294, 0, 0, 0, 395427772555, 0, 302286113723, 468503118271, 517575975116, 121824675188, 395751299929, 311754022014, 0, 54229154860, 382876838208, 353889704043, 114613414229, 194909258696, 242196734371]) (branchResiduals046 17 1) 15120968
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck046_18_0 :
    integerResidualCheck 46 18 0 (dualNumerators046 18 0) ∧
    integerMassCheck 46 18 0 (dualNumerators046 18 0) := by
  apply integerChecks_of_simple 46 18 0 (dualNumerators046 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 211125375206, 1057271324222, 763999473637, 0, 45472526152, 1025720546096, 863239815324, 123309744339, 477654049462, 593539022787]) (branchResiduals046 18 0) 13565580
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck046_18_1 :
    integerResidualCheck 46 18 1 (dualNumerators046 18 1) ∧
    integerMassCheck 46 18 1 (dualNumerators046 18 1) := by
  apply integerChecks_of_simple 46 18 1 (dualNumerators046 18 1)
    (![538874628613, 99205301184, 538874628613, 0, 1, 173280948973, 205181483568, 0, 64396810428, 45929282541, 173280948973, 0, 90678335261, 492556886113, 205181483568, 0, 0, 492556886114, 154686685730, 130636815909, 835183729590, 268562336295, 71184255953, 84289076957, 173280948973, 1, 90678335261, 492556886113, 0, 0, 268562336295, 763397412564, 115240860334, 2939686143, 71184255953, 0, 99806458592, 0, 84824690714, 183737645581, 44504543900, 55301914693]) (branchResiduals046 18 1) 13565580
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck046_19_0 :
    integerResidualCheck 46 19 0 (dualNumerators046 19 0) ∧
    integerMassCheck 46 19 0 (dualNumerators046 19 0) := by
  apply integerChecks_of_simple 46 19 0 (dualNumerators046 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 143378777264, 927814294984, 593870256538, 51346609551, 3480759251, 901168865389, 673714962064, 0, 403390917798, 501258706842]) (branchResiduals046 19 0) 8248658
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck046_19_1 :
    integerResidualCheck 46 19 1 (dualNumerators046 19 1) ∧
    integerMassCheck 46 19 1 (dualNumerators046 19 1) := by
  apply integerChecks_of_simple 46 19 1 (dualNumerators046 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 1, 987477735649, 0, 339927093453, 424072380185, 460183470977, 0, 240148617570, 405068248519, 529741159093, 457736576556, 287707656866, 357509209222]) (branchResiduals046 19 1) 8248658
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck046_20_0 :
    integerResidualCheck 46 20 0 (dualNumerators046 20 0) ∧
    integerMassCheck 46 20 0 (dualNumerators046 20 0) := by
  apply integerChecks_of_simple 46 20 0 (dualNumerators046 20 0)
    (![525362030296, 96717669897, 525362030296, 0, 2, 1982073878105, 2346968095804, 0, 736602820676, 525362030295, 1982073878106, 0, 160571279835, 872209325038, 2346968095804, 0, 0, 872209325040, 1769383425546, 1494289025232, 814241006256, 3071949885821, 814241006256, 964140481889, 1982073878105, 2, 160571279833, 872209325039, 0, 0, 3071949885821, 1351808005779, 1318182410191, 33625595588, 814241006256, 0, 1141636028738, 0, 970267099055, 2101682786767, 509065159462, 632570869277]) (branchResiduals046 20 0) 35312013
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck046_20_1 :
    integerResidualCheck 46 20 1 (dualNumerators046 20 1) ∧
    integerMassCheck 46 20 1 (dualNumerators046 20 1) := by
  apply integerChecks_of_simple 46 20 1 (dualNumerators046 20 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 85258653367, 0, 259883317327, 1411663736071, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 0, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 832818137783, 1355072182930, 0, 1317842481106, 547079247729, 1300649428515, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals046 20 1) 35312013
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck046_21_0 :
    integerResidualCheck 46 21 0 (dualNumerators046 21 0) ∧
    integerMassCheck 46 21 0 (dualNumerators046 21 0) := by
  apply integerChecks_of_simple 46 21 0 (dualNumerators046 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 1, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 604293255477, 704608169863, 757887471419, 892563449519, 583650214286, 725251211053]) (branchResiduals046 21 0) 11182451
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck046_21_1 :
    integerResidualCheck 46 21 1 (dualNumerators046 21 1) ∧
    integerMassCheck 46 21 1 (dualNumerators046 21 1) := by
  apply integerChecks_of_simple 46 21 1 (dualNumerators046 21 1)
    (![113874129702, 20963906509, 113874129702, 0, 1, 11418112698, 13520155082, 0, 159661338854, 113874129702, 11418112698, 0, 218901591686, 1189054541590, 13520155082, 0, 0, 1189054541591, 1567617472129, 323892577801, 176489697786, 17696550257, 176489697786, 208980953998, 11418112698, 0, 218901591686, 1189054541590, 0, 0, 17696550257, 1842875789658, 918239792457, 924635997201, 0, 176489697786, 73266609994, 174187148961, 17696550257, 0, 110341723711, 137112035244]) (branchResiduals046 21 1) 11182451
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck046_22_0 :
    integerResidualCheck 46 22 0 (dualNumerators046 22 0) ∧
    integerMassCheck 46 22 0 (dualNumerators046 22 0) := by
  apply integerChecks_of_simple 46 22 0 (dualNumerators046 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 640010186655, 123989286983, 0, 460183470977, 599623014547, 45593851542, 64927501002, 736408579717, 287707656866, 357509209222]) (branchResiduals046 22 0) 6465674
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck046_22_1 :
    integerResidualCheck 46 22 1 (dualNumerators046 22 1) ∧
    integerMassCheck 46 22 1 (dualNumerators046 22 1) := by
  apply integerChecks_of_simple 46 22 1 (dualNumerators046 22 1)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 5063622582, 0, 15434809046, 83840549778, 5995821236, 0, 0, 83840549778, 1170080822236, 143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 108853458786, 21088199879, 0, 78268383123, 32491749791, 77247265314, 7847938961, 0, 48933554844, 60805460262]) (branchResiduals046 22 1) 6465674
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck046_23_0 :
    integerResidualCheck 46 23 0 (dualNumerators046 23 0) ∧
    integerMassCheck 46 23 0 (dualNumerators046 23 0) := by
  apply integerChecks_of_simple 46 23 0 (dualNumerators046 23 0)
    (![525362030296, 96717669897, 525362030296, 0, 2, 1982073878105, 2346968095804, 0, 736602820676, 525362030295, 1982073878106, 0, 160571279835, 872209325038, 2346968095804, 0, 0, 872209325040, 1769383425546, 1494289025232, 814241006256, 3071949885821, 814241006256, 964140481889, 1982073878105, 2, 160571279833, 872209325039, 0, 0, 3071949885821, 1351808005779, 318182410191, 1033625595588, 814241006256, 0, 1141636028738, 0, 970267099055, 2101682786767, 509065159462, 632570869277]) (branchResiduals046 23 0) 35297932
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck046_23_1 :
    integerResidualCheck 46 23 1 (dualNumerators046 23 1) ∧
    integerMassCheck 46 23 1 (dualNumerators046 23 1) := by
  apply integerChecks_of_simple 46 23 1 (dualNumerators046 23 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 85258653367, 0, 259883317327, 1411663736071, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 0, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 1832818137783, 355072182930, 0, 1317842481106, 547079247729, 1300649428515, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals046 23 1) 35297932
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck046_24_0 :
    integerResidualCheck 46 24 0 (dualNumerators046 24 0) ∧
    integerMassCheck 46 24 0 (dualNumerators046 24 0) := by
  apply integerChecks_of_simple 46 24 0 (dualNumerators046 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 384946583730, 686246488518, 705016048726, 601815130180, 477654049462, 593539022787]) (branchResiduals046 24 0) 9356857
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck046_24_1 :
    integerResidualCheck 46 24 1 (dualNumerators046 24 1) ∧
    integerMassCheck 46 24 1 (dualNumerators046 24 1) := by
  apply integerChecks_of_simple 46 24 1 (dualNumerators046 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623507, 113117556459, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 587483804282, 282115266095, 48434165160, 99625565721, 0, 0, 66021086067, 82038644814]) (branchResiduals046 24 1) 9356857
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck046_25_0 :
    integerResidualCheck 46 25 0 (dualNumerators046 25 0) ∧
    integerMassCheck 46 25 0 (dualNumerators046 25 0) := by
  apply integerChecks_of_simple 46 25 0 (dualNumerators046 25 0)
    (![31307490826, 5763620872, 31307490826, 0, 1, 17498922567, 20720424919, 0, 627590994654, 447612295109, 510444268639, 0, 136807905692, 743128728920, 604415620636, 0, 0, 743128728921, 1507527629264, 1273145186690, 48522430940, 27120993710, 693739297027, 821454747430, 510444268639, 1, 136807905692, 743128728920, 0, 0, 791120467347, 1151750315250, 483956334634, 667793980617, 48522430940, 0, 333537525435, 639144727060, 0, 27120993710, 433727241876, 538955010618]) (branchResiduals046 25 0) 8671199
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck046_25_1 :
    integerResidualCheck 46 25 1 (dualNumerators046 25 1) ∧
    integerMassCheck 46 25 1 (dualNumerators046 25 1) := by
  apply integerChecks_of_simple 46 25 1 (dualNumerators046 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 1, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals046 25 1) 8671199
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck046_26_0 :
    integerResidualCheck 46 26 0 (dualNumerators046 26 0) ∧
    integerMassCheck 46 26 0 (dualNumerators046 26 0) := by
  apply integerChecks_of_simple 46 26 0 (dualNumerators046 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 1, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals046 26 0) 15099566
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck046_26_1 :
    integerResidualCheck 46 26 1 (dualNumerators046 26 1) ∧
    integerMassCheck 46 26 1 (dualNumerators046 26 1) := by
  apply integerChecks_of_simple 46 26 1 (dualNumerators046 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 879744679617, 350168760452, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals046 26 1) 15099566
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck046_27_0 :
    integerResidualCheck 46 27 0 (dualNumerators046 27 0) ∧
    integerMassCheck 46 27 0 (dualNumerators046 27 0) := by
  apply integerChecks_of_simple 46 27 0 (dualNumerators046 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 1, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 436855949686, 304617712691, 340673826058, 423325647580]) (branchResiduals046 27 0) 7338775
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck046_27_1 :
    integerResidualCheck 46 27 1 (dualNumerators046 27 1) ∧
    integerMassCheck 46 27 1 (dualNumerators046 27 1) := by
  apply integerChecks_of_simple 46 27 1 (dualNumerators046 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583262, 988432197465, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 540348413221, 991589527988, 377837583379, 0, 340277028102, 953483284012, 430830286610, 214386579479, 236224837801, 293536000677]) (branchResiduals046 27 1) 7338775
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck046_28_0 :
    integerResidualCheck 46 28 0 (dualNumerators046 28 0) ∧
    integerMassCheck 46 28 0 (dualNumerators046 28 0) := by
  apply integerChecks_of_simple 46 28 0 (dualNumerators046 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 1, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 374399059503, 471423145846, 287707656866, 357509209222]) (branchResiduals046 28 0) 10335557
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck046_28_1 :
    integerResidualCheck 46 28 1 (dualNumerators046 28 1) ∧
    integerMassCheck 46 28 1 (dualNumerators046 28 1) := by
  apply integerChecks_of_simple 46 28 1 (dualNumerators046 28 1)
    (![70965414109, 13064532837, 70965414109, 0, 1, 500061019298, 592120844340, 0, 99499623476, 70965414109, 7115673227, 0, 112439668685, 610762569950, 8425648624, 0, 0, 610762569951, 1239006666393, 201847170824, 109986917328, 775027817129, 109986917328, 130235198988, 7115673227, 0, 112439668685, 610762569950, 0, 0, 11028343493, 946600440957, 484611900989, 461988539969, 0, 109986917328, 360985704208, 438442294145, 11028343493, 0, 68764047964, 85447084301]) (branchResiduals046 28 1) 10335557
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck046_29_0 :
    integerResidualCheck 46 29 0 (dualNumerators046 29 0) ∧
    integerMassCheck 46 29 0 (dualNumerators046 29 0) := by
  apply integerChecks_of_simple 46 29 0 (dualNumerators046 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 1, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals046 29 0) 40352153
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck046_29_1 :
    integerResidualCheck 46 29 1 (dualNumerators046 29 1) ∧
    integerMassCheck 46 29 1 (dualNumerators046 29 1) := by
  apply integerChecks_of_simple 46 29 1 (dualNumerators046 29 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 85258653367, 0, 259883317327, 1411663736071, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 0, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 1832818137783, 355072182930, 0, 1317842481106, 1547079247729, 300649428515, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals046 29 1) 40352153
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck046_30_0 :
    integerResidualCheck 46 30 0 (dualNumerators046 30 0) ∧
    integerMassCheck 46 30 0 (dualNumerators046 30 0) := by
  apply integerChecks_of_simple 46 30 0 (dualNumerators046 30 0)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 5063622582, 0, 15434809046, 83840549778, 5995821236, 0, 0, 83840549778, 170080822236, 1143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 108853458786, 21088199879, 0, 78268383123, 91883053566, 17855961539, 7847938961, 0, 108324858619, 1414156487]) (branchResiduals046 30 0) 7680628
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck046_30_1 :
    integerResidualCheck 46 30 1 (dualNumerators046 30 1) ∧
    integerMassCheck 46 30 1 (dualNumerators046 30 1) := by
  apply integerChecks_of_simple 46 30 1 (dualNumerators046 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195716, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 1, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 212932307485, 691717317156, 544901951702, 0, 94784895256, 669214578382, 621279733097, 307371055990, 281282522283, 482716951355]) (branchResiduals046 30 1) 7680628
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck046_31_0 :
    integerResidualCheck 46 31 0 (dualNumerators046 31 0) ∧
    integerMassCheck 46 31 0 (dualNumerators046 31 0) := by
  apply integerChecks_of_simple 46 31 0 (dualNumerators046 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 1032415642124, 2, 592902192609, 0, 1222480453651, 0, 500720887661, 0, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642124, 1, 592902192609, 0, 0, 0, 1600106408231, 776050524992, 756746629027, 19303895966, 634078107472, 938764468190, 655394283556, 0, 827665375816, 772441032416, 655394283556, 0]) (branchResiduals046 31 0) 32891612
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck046_31_1 :
    integerResidualCheck 46 31 1 (dualNumerators046 31 1) ∧
    integerMassCheck 46 31 1 (dualNumerators046 31 1) := by
  apply integerChecks_of_simple 46 31 1 (dualNumerators046 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 556963843680, 992902647048, 18993131489, 744564115640, 327950144489, 1221916346239]) (branchResiduals046 31 1) 32891612
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck046_32_0 :
    integerResidualCheck 46 32 0 (dualNumerators046 32 0) ∧
    integerMassCheck 46 32 0 (dualNumerators046 32 0) := by
  apply integerChecks_of_simple 46 32 0 (dualNumerators046 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 0, 2743468108582, 2028778803022, 0, 505064750776, 2743468108580, 1713354977902, 2, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 2028778803022, 0, 0, 0, 4252009289869, 2655471466972, 2224515654627, 430955812345, 0, 1599482877825, 1877710578357, 364902194331, 262156886566, 3989852403304, 0, 2242612772688]) (branchResiduals046 32 0) 67647473
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck046_32_1 :
    integerResidualCheck 46 32 1 (dualNumerators046 32 1) ∧
    integerMassCheck 46 32 1 (dualNumerators046 32 1) := by
  apply integerChecks_of_simple 46 32 1 (dualNumerators046 32 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 85258653367, 0, 259883317327, 1411663736071, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 0, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 1832818137783, 355072182930, 0, 1317842481106, 1547079247729, 300649428515, 132139529898, 0, 1823917842058, 23810834186]) (branchResiduals046 32 1) 67647473
    branchSparseDots046 branchIntegerCurvature046 branchDots046
    branchIntegerCurvature046_entry rfl
    (congrFun (congrFun branchResiduals046_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks046 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 46 j s (dualNumerators046 j s) ∧
    integerMassCheck 46 j s (dualNumerators046 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck046_0_0
    · exact integerCheck046_0_1
  · fin_cases s
    · exact integerCheck046_1_0
    · exact integerCheck046_1_1
  · fin_cases s
    · exact integerCheck046_2_0
    · exact integerCheck046_2_1
  · fin_cases s
    · exact integerCheck046_3_0
    · exact integerCheck046_3_1
  · fin_cases s
    · exact integerCheck046_4_0
    · exact integerCheck046_4_1
  · fin_cases s
    · exact integerCheck046_5_0
    · exact integerCheck046_5_1
  · fin_cases s
    · exact integerCheck046_6_0
    · exact integerCheck046_6_1
  · fin_cases s
    · exact integerCheck046_7_0
    · exact integerCheck046_7_1
  · fin_cases s
    · exact integerCheck046_8_0
    · exact integerCheck046_8_1
  · fin_cases s
    · exact integerCheck046_9_0
    · exact integerCheck046_9_1
  · fin_cases s
    · exact integerCheck046_10_0
    · exact integerCheck046_10_1
  · fin_cases s
    · exact integerCheck046_11_0
    · exact integerCheck046_11_1
  · fin_cases s
    · exact integerCheck046_12_0
    · exact integerCheck046_12_1
  · fin_cases s
    · exact integerCheck046_13_0
    · exact integerCheck046_13_1
  · fin_cases s
    · exact integerCheck046_14_0
    · exact integerCheck046_14_1
  · fin_cases s
    · exact integerCheck046_15_0
    · exact integerCheck046_15_1
  · fin_cases s
    · exact integerCheck046_16_0
    · exact integerCheck046_16_1
  · fin_cases s
    · exact integerCheck046_17_0
    · exact integerCheck046_17_1
  · fin_cases s
    · exact integerCheck046_18_0
    · exact integerCheck046_18_1
  · fin_cases s
    · exact integerCheck046_19_0
    · exact integerCheck046_19_1
  · fin_cases s
    · exact integerCheck046_20_0
    · exact integerCheck046_20_1
  · fin_cases s
    · exact integerCheck046_21_0
    · exact integerCheck046_21_1
  · fin_cases s
    · exact integerCheck046_22_0
    · exact integerCheck046_22_1
  · fin_cases s
    · exact integerCheck046_23_0
    · exact integerCheck046_23_1
  · fin_cases s
    · exact integerCheck046_24_0
    · exact integerCheck046_24_1
  · fin_cases s
    · exact integerCheck046_25_0
    · exact integerCheck046_25_1
  · fin_cases s
    · exact integerCheck046_26_0
    · exact integerCheck046_26_1
  · fin_cases s
    · exact integerCheck046_27_0
    · exact integerCheck046_27_1
  · fin_cases s
    · exact integerCheck046_28_0
    · exact integerCheck046_28_1
  · fin_cases s
    · exact integerCheck046_29_0
    · exact integerCheck046_29_1
  · fin_cases s
    · exact integerCheck046_30_0
    · exact integerCheck046_30_1
  · fin_cases s
    · exact integerCheck046_31_0
    · exact integerCheck046_31_1
  · fin_cases s
    · exact integerCheck046_32_0
    · exact integerCheck046_32_1

end ElevenSquare.Tasks.T06
