import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual015
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
import ElevenSquare.Tasks.T06.SparseColumn23
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
import ElevenSquare.Tasks.T06.SparseColumn44
import ElevenSquare.Tasks.T06.SparseColumn46

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix015 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix015_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = branchIntegerMatrix015 := by
  change roundedGradients ∘ branchRows 15 = branchIntegerMatrix015
  rw [show branchRows 15 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, branchIntegerMatrix015]

theorem branchColumn015_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 0) i) = _
  rw [branchColumn015_0]
  exact sparseColumn00_sum n

theorem branchColumn015_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 1) i) = _
  rw [branchColumn015_1]
  exact sparseColumn01_sum n

theorem branchColumn015_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 2) i) = _
  rw [branchColumn015_2]
  exact sparseColumn02_sum n

theorem branchColumn015_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 3) i) = _
  rw [branchColumn015_3]
  exact sparseColumn03_sum n

theorem branchColumn015_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 4) i) = _
  rw [branchColumn015_4]
  exact sparseColumn04_sum n

theorem branchColumn015_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 5) i) = _
  rw [branchColumn015_5]
  exact sparseColumn05_sum n

theorem branchColumn015_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 6) i) = _
  rw [branchColumn015_6]
  exact sparseColumn06_sum n

theorem branchColumn015_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 7) i) = _
  rw [branchColumn015_7]
  exact sparseColumn07_sum n

theorem branchColumn015_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 8) i) = _
  rw [branchColumn015_8]
  exact sparseColumn08_sum n

theorem branchColumn015_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 9) i) = _
  rw [branchColumn015_9]
  exact sparseColumn09_sum n

theorem branchColumn015_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 10) i) = _
  rw [branchColumn015_10]
  exact sparseColumn10_sum n

theorem branchColumn015_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 11) i) = _
  rw [branchColumn015_11]
  exact sparseColumn11_sum n

theorem branchColumn015_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 12) i) = _
  rw [branchColumn015_12]
  exact sparseColumn35_sum n

theorem branchColumn015_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 13) i) = _
  rw [branchColumn015_13]
  exact sparseColumn36_sum n

theorem branchColumn015_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 14) i) = _
  rw [branchColumn015_14]
  exact sparseColumn41_sum n

theorem branchColumn015_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 15) i) = _
  rw [branchColumn015_15]
  exact sparseColumn38_sum n

theorem branchColumn015_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 16) i) = _
  rw [branchColumn015_16]
  exact sparseColumn39_sum n

theorem branchColumn015_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 17) i) = _
  rw [branchColumn015_17]
  exact sparseColumn17_sum n

theorem branchColumn015_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 18) i) = _
  rw [branchColumn015_18]
  exact sparseColumn18_sum n

theorem branchColumn015_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 19) i) = _
  rw [branchColumn015_19]
  exact sparseColumn19_sum n

theorem branchColumn015_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 20) = sparseColumn20 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 20) = sparseDot20 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 20) i) = _
  rw [branchColumn015_20]
  exact sparseColumn20_sum n

theorem branchColumn015_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 21) i) = _
  rw [branchColumn015_21]
  exact sparseColumn21_sum n

theorem branchColumn015_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 22) i) = _
  rw [branchColumn015_22]
  exact sparseColumn22_sum n

theorem branchColumn015_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 23) = sparseColumn23 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 23) = sparseDot23 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 23) i) = _
  rw [branchColumn015_23]
  exact sparseColumn23_sum n

theorem branchColumn015_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 24) i) = _
  rw [branchColumn015_24]
  exact sparseColumn24_sum n

theorem branchColumn015_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 25) i) = _
  rw [branchColumn015_25]
  exact sparseColumn25_sum n

theorem branchColumn015_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 26) = sparseColumn44 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 26) = sparseDot44 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 26) i) = _
  rw [branchColumn015_26]
  exact sparseColumn44_sum n

theorem branchColumn015_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 27) i) = _
  rw [branchColumn015_27]
  exact sparseColumn27_sum n

theorem branchColumn015_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 28) i) = _
  rw [branchColumn015_28]
  exact sparseColumn28_sum n

theorem branchColumn015_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 29) = sparseColumn46 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 29) = sparseDot46 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 29) i) = _
  rw [branchColumn015_29]
  exact sparseColumn46_sum n

theorem branchColumn015_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 30) i) = _
  rw [branchColumn015_30]
  exact sparseColumn30_sum n

theorem branchColumn015_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 31) i) = _
  rw [branchColumn015_31]
  exact sparseColumn31_sum n

theorem branchColumn015_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 15 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 15 i)) = _
  rw [branchIntegerMatrix015_eq]
  simp only [branchIntegerMatrix015, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot015_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 15 i) 32) i) = _
  rw [branchColumn015_32]
  exact sparseColumn43_sum n

def branchSparseDots015 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot20, sparseDot21, sparseDot22, sparseDot23, sparseDot24, sparseDot25, sparseDot44, sparseDot27, sparseDot28, sparseDot46, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot015_0 :
    branchSparseDots015 0 = sparseDot00 := rfl

private theorem branchSparseDot015_1 :
    branchSparseDots015 1 = sparseDot01 := rfl

private theorem branchSparseDot015_2 :
    branchSparseDots015 2 = sparseDot02 := rfl

private theorem branchSparseDot015_3 :
    branchSparseDots015 3 = sparseDot03 := rfl

private theorem branchSparseDot015_4 :
    branchSparseDots015 4 = sparseDot04 := rfl

private theorem branchSparseDot015_5 :
    branchSparseDots015 5 = sparseDot05 := rfl

private theorem branchSparseDot015_6 :
    branchSparseDots015 6 = sparseDot06 := rfl

private theorem branchSparseDot015_7 :
    branchSparseDots015 7 = sparseDot07 := rfl

private theorem branchSparseDot015_8 :
    branchSparseDots015 8 = sparseDot08 := rfl

private theorem branchSparseDot015_9 :
    branchSparseDots015 9 = sparseDot09 := rfl

private theorem branchSparseDot015_10 :
    branchSparseDots015 10 = sparseDot10 := rfl

private theorem branchSparseDot015_11 :
    branchSparseDots015 11 = sparseDot11 := rfl

private theorem branchSparseDot015_12 :
    branchSparseDots015 12 = sparseDot35 := rfl

private theorem branchSparseDot015_13 :
    branchSparseDots015 13 = sparseDot36 := rfl

private theorem branchSparseDot015_14 :
    branchSparseDots015 14 = sparseDot41 := rfl

private theorem branchSparseDot015_15 :
    branchSparseDots015 15 = sparseDot38 := rfl

private theorem branchSparseDot015_16 :
    branchSparseDots015 16 = sparseDot39 := rfl

private theorem branchSparseDot015_17 :
    branchSparseDots015 17 = sparseDot17 := rfl

private theorem branchSparseDot015_18 :
    branchSparseDots015 18 = sparseDot18 := rfl

private theorem branchSparseDot015_19 :
    branchSparseDots015 19 = sparseDot19 := rfl

private theorem branchSparseDot015_20 :
    branchSparseDots015 20 = sparseDot20 := rfl

private theorem branchSparseDot015_21 :
    branchSparseDots015 21 = sparseDot21 := rfl

private theorem branchSparseDot015_22 :
    branchSparseDots015 22 = sparseDot22 := rfl

private theorem branchSparseDot015_23 :
    branchSparseDots015 23 = sparseDot23 := rfl

private theorem branchSparseDot015_24 :
    branchSparseDots015 24 = sparseDot24 := rfl

private theorem branchSparseDot015_25 :
    branchSparseDots015 25 = sparseDot25 := rfl

private theorem branchSparseDot015_26 :
    branchSparseDots015 26 = sparseDot44 := rfl

private theorem branchSparseDot015_27 :
    branchSparseDots015 27 = sparseDot27 := rfl

private theorem branchSparseDot015_28 :
    branchSparseDots015 28 = sparseDot28 := rfl

private theorem branchSparseDot015_29 :
    branchSparseDots015 29 = sparseDot46 := rfl

private theorem branchSparseDot015_30 :
    branchSparseDots015 30 = sparseDot30 := rfl

private theorem branchSparseDot015_31 :
    branchSparseDots015 31 = sparseDot31 := rfl

private theorem branchSparseDot015_32 :
    branchSparseDots015 32 = sparseDot43 := rfl

theorem branchDots015 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 15 i) k) = branchSparseDots015 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot015_0 n
      _ = _ := congrFun branchSparseDot015_0.symm n
  · calc
      _ = sparseDot01 n := branchDot015_1 n
      _ = _ := congrFun branchSparseDot015_1.symm n
  · calc
      _ = sparseDot02 n := branchDot015_2 n
      _ = _ := congrFun branchSparseDot015_2.symm n
  · calc
      _ = sparseDot03 n := branchDot015_3 n
      _ = _ := congrFun branchSparseDot015_3.symm n
  · calc
      _ = sparseDot04 n := branchDot015_4 n
      _ = _ := congrFun branchSparseDot015_4.symm n
  · calc
      _ = sparseDot05 n := branchDot015_5 n
      _ = _ := congrFun branchSparseDot015_5.symm n
  · calc
      _ = sparseDot06 n := branchDot015_6 n
      _ = _ := congrFun branchSparseDot015_6.symm n
  · calc
      _ = sparseDot07 n := branchDot015_7 n
      _ = _ := congrFun branchSparseDot015_7.symm n
  · calc
      _ = sparseDot08 n := branchDot015_8 n
      _ = _ := congrFun branchSparseDot015_8.symm n
  · calc
      _ = sparseDot09 n := branchDot015_9 n
      _ = _ := congrFun branchSparseDot015_9.symm n
  · calc
      _ = sparseDot10 n := branchDot015_10 n
      _ = _ := congrFun branchSparseDot015_10.symm n
  · calc
      _ = sparseDot11 n := branchDot015_11 n
      _ = _ := congrFun branchSparseDot015_11.symm n
  · calc
      _ = sparseDot35 n := branchDot015_12 n
      _ = _ := congrFun branchSparseDot015_12.symm n
  · calc
      _ = sparseDot36 n := branchDot015_13 n
      _ = _ := congrFun branchSparseDot015_13.symm n
  · calc
      _ = sparseDot41 n := branchDot015_14 n
      _ = _ := congrFun branchSparseDot015_14.symm n
  · calc
      _ = sparseDot38 n := branchDot015_15 n
      _ = _ := congrFun branchSparseDot015_15.symm n
  · calc
      _ = sparseDot39 n := branchDot015_16 n
      _ = _ := congrFun branchSparseDot015_16.symm n
  · calc
      _ = sparseDot17 n := branchDot015_17 n
      _ = _ := congrFun branchSparseDot015_17.symm n
  · calc
      _ = sparseDot18 n := branchDot015_18 n
      _ = _ := congrFun branchSparseDot015_18.symm n
  · calc
      _ = sparseDot19 n := branchDot015_19 n
      _ = _ := congrFun branchSparseDot015_19.symm n
  · calc
      _ = sparseDot20 n := branchDot015_20 n
      _ = _ := congrFun branchSparseDot015_20.symm n
  · calc
      _ = sparseDot21 n := branchDot015_21 n
      _ = _ := congrFun branchSparseDot015_21.symm n
  · calc
      _ = sparseDot22 n := branchDot015_22 n
      _ = _ := congrFun branchSparseDot015_22.symm n
  · calc
      _ = sparseDot23 n := branchDot015_23 n
      _ = _ := congrFun branchSparseDot015_23.symm n
  · calc
      _ = sparseDot24 n := branchDot015_24 n
      _ = _ := congrFun branchSparseDot015_24.symm n
  · calc
      _ = sparseDot25 n := branchDot015_25 n
      _ = _ := congrFun branchSparseDot015_25.symm n
  · calc
      _ = sparseDot44 n := branchDot015_26 n
      _ = _ := congrFun branchSparseDot015_26.symm n
  · calc
      _ = sparseDot27 n := branchDot015_27 n
      _ = _ := congrFun branchSparseDot015_27.symm n
  · calc
      _ = sparseDot28 n := branchDot015_28 n
      _ = _ := congrFun branchSparseDot015_28.symm n
  · calc
      _ = sparseDot46 n := branchDot015_29 n
      _ = _ := congrFun branchSparseDot015_29.symm n
  · calc
      _ = sparseDot30 n := branchDot015_30 n
      _ = _ := congrFun branchSparseDot015_30.symm n
  · calc
      _ = sparseDot31 n := branchDot015_31 n
      _ = _ := congrFun branchSparseDot015_31.symm n
  · calc
      _ = sparseDot43 n := branchDot015_32 n
      _ = _ := congrFun branchSparseDot015_32.symm n

def branchIntegerCurvature015 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101981296, 101981296, 44932602, 44932602, 115699695, 115699695, 88123140, 88123140, 289103692, 289103692]

theorem branchIntegerCurvature015_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 15 i)) = branchIntegerCurvature015 := by
  change curvatureNumerators ∘ branchRows 15 = branchIntegerCurvature015
  rw [show branchRows 15 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature015_entry (i : Fin 42) :
    curvatureNumerators (branchRows 15 i) = branchIntegerCurvature015 i :=
  congrFun branchIntegerCurvature015_eq i

def branchResiduals015 : Fin 33 → Fin 2 → ℕ := ![![1300580532618599, 33000000000000], ![1545342476798598, 33000000000000], ![1582895989501194, 1336080526090008], ![33000000000000, 1021727734628020], ![857484968245910, 33000000000000], ![1052671000530872, 891559005628906], ![720475735294167, 622122527367398], ![33000000000000, 760278655633685], ![1579380611496047, 1129499627291951], ![1024445694323207, 33000000000000], ![33000000000000, 777496447572864], ![508673265942299, 466704601686204], ![989044006888705, 66000000000000], ![33000000000000, 859910985088990], ![1052631262734472, 485891140073101], ![471859969658862, 33000000000000], ![66000000000000, 743985444367439], ![663597062655695, 464565000765832], ![621274194448585, 243408882377443], ![628550145229946, 508752477741374], ![1230975872252892, 948557656510944], ![753505966780669, 387586934288278], ![469430375052114, 104116699803623], ![1232836462785735, 948557656510944], ![671216933163092, 230071553353688], ![501748597220204, 221360137673294], ![398805840068707, 852626669416348], ![407429719971413, 548960205719397], ![283944620155412, 307920661383665], ![398805840068707, 948557656510944], ![104116699803623, 552690633861837], ![967647205331585, 648581743166449], ![2024447003078323, 948557656510944]]

theorem branchResiduals015_eq : residualNumerators 15 = branchResiduals015 := rfl

theorem integerCheck015_0_0 :
    integerResidualCheck 15 0 0 (dualNumerators015 0 0) ∧
    integerMassCheck 15 0 0 (dualNumerators015 0 0) := by
  apply integerChecks_of_simple 15 0 0 (dualNumerators015 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1607511062796, 565535261271, 1308901425339, 0, 227681483087, 1607511062798, 1485808378804, 481205215181, 818327875519, 1016864670366]) (branchResiduals015 0 0) 18767167
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck015_0_1 :
    integerResidualCheck 15 0 1 (dualNumerators015 0 1) ∧
    integerMassCheck 15 0 1 (dualNumerators015 0 1) := by
  apply integerChecks_of_simple 15 0 1 (dualNumerators015 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals015 0 1) 18767167
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck015_1_0 :
    integerResidualCheck 15 1 0 (dualNumerators015 1 0) ∧
    integerMassCheck 15 1 0 (dualNumerators015 1 0) := by
  apply integerChecks_of_simple 15 1 0 (dualNumerators015 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 1903449321293, 669648709827, 1549866490727, 0, 269597002772, 1903449321295, 1759341515999, 569793739799, 968979732271, 1204066591796]) (branchResiduals015 1 0) 22176635
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck015_1_1 :
    integerResidualCheck 15 1 1 (dualNumerators015 1 1) ∧
    integerMassCheck 15 1 1 (dualNumerators015 1 1) := by
  apply integerChecks_of_simple 15 1 1 (dualNumerators015 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals015 1 1) 22176635
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck015_2_0 :
    integerResidualCheck 15 2 0 (dualNumerators015 2 0) ∧
    integerMassCheck 15 2 0 (dualNumerators015 2 0) := by
  apply integerChecks_of_simple 15 2 0 (dualNumerators015 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 1903449321295, 669648709827, 1549866490728, 0, 269597002773, 1903449321296, 1759341516001, 569793739799, 968979732272, 1204066591797]) (branchResiduals015 2 0) 22681452
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck015_2_1 :
    integerResidualCheck 15 2 1 (dualNumerators015 2 1) ∧
    integerMassCheck 15 2 1 (dualNumerators015 2 1) := by
  apply integerChecks_of_simple 15 2 1 (dualNumerators015 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1607511062795, 565535261271, 1308901425338, 0, 227681483087, 1607511062796, 1485808378803, 481205215180, 818327875518, 1016864670365]) (branchResiduals015 2 1) 22681452
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck015_3_0 :
    integerResidualCheck 15 3 0 (dualNumerators015 3 0) ∧
    integerMassCheck 15 3 0 (dualNumerators015 3 0) := by
  apply integerChecks_of_simple 15 3 0 (dualNumerators015 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals015 3 0) 16360330
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck015_3_1 :
    integerResidualCheck 15 3 1 (dualNumerators015 3 1) ∧
    integerMassCheck 15 3 1 (dualNumerators015 3 1) := by
  apply integerChecks_of_simple 15 3 1 (dualNumerators015 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000000, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals015 3 1) 16360330
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck015_4_0 :
    integerResidualCheck 15 4 0 (dualNumerators015 4 0) ∧
    integerMassCheck 15 4 0 (dualNumerators015 4 0) := by
  apply integerChecks_of_simple 15 4 0 (dualNumerators015 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1069679196818, 376321705057, 870976665588, 0, 151505113461, 1069679196819, 988695101419, 320206323920, 544536410901, 676647899379]) (branchResiduals015 4 0) 13760362
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck015_4_1 :
    integerResidualCheck 15 4 1 (dualNumerators015 4 1) ∧
    integerMassCheck 15 4 1 (dualNumerators015 4 1) := by
  apply integerChecks_of_simple 15 4 1 (dualNumerators015 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals015 4 1) 13760362
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck015_5_0 :
    integerResidualCheck 15 5 0 (dualNumerators015 5 0) ∧
    integerMassCheck 15 5 0 (dualNumerators015 5 0) := by
  apply integerChecks_of_simple 15 5 0 (dualNumerators015 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1266604123796, 445601470905, 1031321016288, 0, 179396778078, 1266604123797, 1170711084557, 379155406172, 644784030255, 801216871620]) (branchResiduals015 5 0) 17641130
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck015_5_1 :
    integerResidualCheck 15 5 1 (dualNumerators015 5 1) ∧
    integerMassCheck 15 5 1 (dualNumerators015 5 1) := by
  apply integerChecks_of_simple 15 5 1 (dualNumerators015 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1069679196817, 376321705056, 870976665588, 0, 151505113461, 1069679196818, 988695101418, 320206323920, 544536410901, 676647899378]) (branchResiduals015 5 1) 17641130
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck015_6_0 :
    integerResidualCheck 15 6 0 (dualNumerators015 6 0) ∧
    integerMassCheck 15 6 0 (dualNumerators015 6 0) := by
  apply integerChecks_of_simple 15 6 0 (dualNumerators015 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 659499318402, 1175693227483, 2719950702, 106626845062, 818327875519, 1016864670366]) (branchResiduals015 6 0) 8962451
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck015_6_1 :
    integerResidualCheck 15 6 1 (dualNumerators015 6 1) ∧
    integerMassCheck 15 6 1 (dualNumerators015 6 1) := by
  apply integerChecks_of_simple 15 6 1 (dualNumerators015 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals015 6 1) 8962451
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck015_7_0 :
    integerResidualCheck 15 7 0 (dualNumerators015 7 0) ∧
    integerMassCheck 15 7 0 (dualNumerators015 7 0) := by
  apply integerChecks_of_simple 15 7 0 (dualNumerators015 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals015 7 0) 10424794
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck015_7_1 :
    integerResidualCheck 15 7 1 (dualNumerators015 7 1) ∧
    integerMassCheck 15 7 1 (dualNumerators015 7 1) := by
  apply integerChecks_of_simple 15 7 1 (dualNumerators015 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 951724660649, 334824354914, 774933245365, 0, 134798501387, 951724660649, 879670758001, 284896869900, 484489866137, 602033295899]) (branchResiduals015 7 1) 10424794
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck015_8_0 :
    integerResidualCheck 15 8 0 (dualNumerators015 8 0) ∧
    integerMassCheck 15 8 0 (dualNumerators015 8 0) := by
  apply integerChecks_of_simple 15 8 0 (dualNumerators015 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 1903449321297, 669648709828, 1549866490730, 0, 269597002773, 1903449321298, 1759341516002, 569793739800, 968979732273, 1204066591798]) (branchResiduals015 8 0) 22681452
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck015_8_1 :
    integerResidualCheck 15 8 1 (dualNumerators015 8 1) ∧
    integerMassCheck 15 8 1 (dualNumerators015 8 1) := by
  apply integerChecks_of_simple 15 8 1 (dualNumerators015 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1357583723455, 477608822428, 1105400337063, 0, 192282767270, 1357583723456, 1254802730706, 406389967006, 691098574663, 858767916063]) (branchResiduals015 8 1) 22681452
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck015_9_0 :
    integerResidualCheck 15 9 0 (dualNumerators015 9 0) ∧
    integerMassCheck 15 9 0 (dualNumerators015 9 0) := by
  apply integerChecks_of_simple 15 9 0 (dualNumerators015 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals015 9 0) 16350530
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck015_9_1 :
    integerResidualCheck 15 9 1 (dualNumerators015 9 1) ∧
    integerMassCheck 15 9 1 (dualNumerators015 9 1) := by
  apply integerChecks_of_simple 15 9 1 (dualNumerators015 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals015 9 1) 16350530
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck015_10_0 :
    integerResidualCheck 15 10 0 (dualNumerators015 10 0) ∧
    integerMassCheck 15 10 0 (dualNumerators015 10 0) := by
  apply integerChecks_of_simple 15 10 0 (dualNumerators015 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals015 10 0) 10683139
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck015_10_1 :
    integerResidualCheck 15 10 1 (dualNumerators015 10 1) ∧
    integerMassCheck 15 10 1 (dualNumerators015 10 1) := by
  apply integerChecks_of_simple 15 10 1 (dualNumerators015 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 968259856239, 340641569100, 788396879662, 0, 137140480825, 968259856240, 894954094286, 289846647564, 492907358117, 612492978948]) (branchResiduals015 10 1) 10683139
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck015_11_0 :
    integerResidualCheck 15 11 0 (dualNumerators015 11 0) ∧
    integerMassCheck 15 11 0 (dualNumerators015 11 0) := by
  apply integerChecks_of_simple 15 11 0 (dualNumerators015 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 601785379685, 211712914335, 489998333105, 0, 85234491332, 601785379686, 556224949284, 180143247425, 306347970271, 380671900746]) (branchResiduals015 11 0) 15120968
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck015_11_1 :
    integerResidualCheck 15 11 1 (dualNumerators015 11 1) ∧
    integerMassCheck 15 11 1 (dualNumerators015 11 1) := by
  apply integerChecks_of_simple 15 11 1 (dualNumerators015 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 548759091280, 193057841557, 446822154676, 0, 77724058423, 548759091281, 507213215908, 164269934257, 279354134309, 347129015395]) (branchResiduals015 11 1) 15120968
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck015_12_0 :
    integerResidualCheck 15 12 0 (dualNumerators015 12 0) ∧
    integerMassCheck 15 12 0 (dualNumerators015 12 0) := by
  apply integerChecks_of_simple 15 12 0 (dualNumerators015 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals015 12 0) 16348076
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck015_12_1 :
    integerResidualCheck 15 12 1 (dualNumerators015 12 1) ∧
    integerMassCheck 15 12 1 (dualNumerators015 12 1) := by
  apply integerChecks_of_simple 15 12 1 (dualNumerators015 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals015 12 1) 16348076
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck015_13_0 :
    integerResidualCheck 15 13 0 (dualNumerators015 13 0) ∧
    integerMassCheck 15 13 0 (dualNumerators015 13 0) := by
  apply integerChecks_of_simple 15 13 0 (dualNumerators015 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals015 13 0) 13962901
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck015_13_1 :
    integerResidualCheck 15 13 1 (dualNumerators015 13 1) ∧
    integerMassCheck 15 13 1 (dualNumerators015 13 1) := by
  apply integerChecks_of_simple 15 13 1 (dualNumerators015 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1069679196818, 376321705057, 870976665588, 0, 151505113461, 1069679196819, 988695101419, 320206323920, 544536410901, 676647899379]) (branchResiduals015 13 1) 13962901
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck015_14_0 :
    integerResidualCheck 15 14 0 (dualNumerators015 14 0) ∧
    integerMassCheck 15 14 0 (dualNumerators015 14 0) := by
  apply integerChecks_of_simple 15 14 0 (dualNumerators015 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1266604123796, 445601470905, 1031321016288, 0, 179396778078, 1266604123797, 1170711084557, 379155406172, 644784030255, 801216871620]) (branchResiduals015 14 0) 20161291
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck015_14_1 :
    integerResidualCheck 15 14 1 (dualNumerators015 14 1) ∧
    integerMassCheck 15 14 1 (dualNumerators015 14 1) := by
  apply integerChecks_of_simple 15 14 1 (dualNumerators015 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 579921137935, 204020899046, 472195570901, 0, 82137726959, 579921137935, 536016022365, 173598230474, 295217646558, 366841218336]) (branchResiduals015 14 1) 20161291
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck015_15_0 :
    integerResidualCheck 15 15 0 (dualNumerators015 15 0) ∧
    integerMassCheck 15 15 0 (dualNumerators015 15 0) := by
  apply integerChecks_of_simple 15 15 0 (dualNumerators015 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 601785379685, 211712914334, 489998333105, 0, 85234491332, 601785379685, 556224949284, 180143247425, 306347970271, 380671900746]) (branchResiduals015 15 0) 12900283
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck015_15_1 :
    integerResidualCheck 15 15 1 (dualNumerators015 15 1) ∧
    integerMassCheck 15 15 1 (dualNumerators015 15 1) := by
  apply integerChecks_of_simple 15 15 1 (dualNumerators015 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals015 15 1) 12900283
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck015_16_0 :
    integerResidualCheck 15 16 0 (dualNumerators015 16 0) ∧
    integerMassCheck 15 16 0 (dualNumerators015 16 0) := by
  apply integerChecks_of_simple 15 16 0 (dualNumerators015 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals015 16 0) 10683060
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck015_16_1 :
    integerResidualCheck 15 16 1 (dualNumerators015 16 1) ∧
    integerMassCheck 15 16 1 (dualNumerators015 16 1) := by
  apply integerChecks_of_simple 15 16 1 (dualNumerators015 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 968259856239, 340641569100, 788396879662, 0, 137140480825, 968259856240, 894954094286, 289846647564, 492907358117, 612492978948]) (branchResiduals015 16 1) 10683060
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck015_17_0 :
    integerResidualCheck 15 17 0 (dualNumerators015 17 0) ∧
    integerMassCheck 15 17 0 (dualNumerators015 17 0) := by
  apply integerChecks_of_simple 15 17 0 (dualNumerators015 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 789287375867, 277677617691, 642670147151, 0, 111791529451, 789287375867, 729531400118, 236271594227, 401798703857, 499280201462]) (branchResiduals015 17 0) 15120968
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck015_17_1 :
    integerResidualCheck 15 17 1 (dualNumerators015 17 1) ∧
    integerMassCheck 15 17 1 (dualNumerators015 17 1) := by
  apply integerChecks_of_simple 15 17 1 (dualNumerators015 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 548759091280, 193057841557, 446822154676, 0, 77724058423, 548759091280, 507213215908, 164269934257, 279354134309, 347129015395]) (branchResiduals015 17 1) 15120968
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck015_18_0 :
    integerResidualCheck 15 18 0 (dualNumerators015 18 0) ∧
    integerMassCheck 15 18 0 (dualNumerators015 18 0) := by
  apply integerChecks_of_simple 15 18 0 (dualNumerators015 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 1025720546095, 242676153333, 763999473637, 0, 45472526152, 1025720546096, 863239815324, 123309744339, 477654049462, 593539022787]) (branchResiduals015 18 0) 13565580
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck015_18_1 :
    integerResidualCheck 15 18 1 (dualNumerators015 18 1) ∧
    integerMassCheck 15 18 1 (dualNumerators015 18 1) := by
  apply integerChecks_of_simple 15 18 1 (dualNumerators015 18 1)
    (![538874628613, 99205301184, 538874628613, 0, 1, 173280948973, 205181483568, 0, 64396810428, 45929282541, 173280948973, 0, 90678335261, 492556886113, 205181483568, 0, 0, 492556886114, 154686685730, 130636815909, 835183729590, 268562336295, 71184255953, 84289076957, 173280948973, 0, 90678335261, 492556886113, 0, 0, 268562336295, 763397412564, 0, 118180546476, 71184255953, 0, 99806458592, 1, 84824690714, 183737645581, 44504543900, 55301914693]) (branchResiduals015 18 1) 13565580
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck015_19_0 :
    integerResidualCheck 15 19 0 (dualNumerators015 19 0) ∧
    integerMassCheck 15 19 0 (dualNumerators015 19 0) := by
  apply integerChecks_of_simple 15 19 0 (dualNumerators015 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 901168865389, 170024206859, 593870256538, 51346609551, 3480759251, 901168865389, 673714962064, 0, 403390917798, 501258706842]) (branchResiduals015 19 0) 8248658
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck015_19_1 :
    integerResidualCheck 15 19 1 (dualNumerators015 19 1) ∧
    integerMassCheck 15 19 1 (dualNumerators015 19 1) := by
  apply integerChecks_of_simple 15 19 1 (dualNumerators015 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 405068248518, 358931225119, 460183470977, 0, 240148617570, 405068248519, 529741159093, 457736576556, 287707656866, 357509209222]) (branchResiduals015 19 1) 8248658
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck015_20_0 :
    integerResidualCheck 15 20 0 (dualNumerators015 20 0) ∧
    integerMassCheck 15 20 0 (dualNumerators015 20 0) := by
  apply integerChecks_of_simple 15 20 0 (dualNumerators015 20 0)
    (![525362030296, 96717669897, 525362030297, 0, 2, 1982073878105, 2346968095805, 0, 736602820676, 525362030296, 1982073878107, 0, 160571279833, 872209325040, 2346968095805, 0, 0, 872209325041, 1769383425548, 1494289025233, 814241006257, 3071949885822, 814241006257, 964140481890, 1982073878107, 0, 160571279833, 872209325040, 0, 0, 3071949885822, 1351808005780, 0, 1351808005780, 814241006257, 0, 1141636028738, 1, 970267099056, 2101682786767, 509065159462, 632570869278]) (branchResiduals015 20 0) 35312013
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck015_20_1 :
    integerResidualCheck 15 20 1 (dualNumerators015 20 1) ∧
    integerMassCheck 15 20 1 (dualNumerators015 20 1) := by
  apply integerChecks_of_simple 15 20 1 (dualNumerators015 20 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 85258653367, 0, 259883317327, 1411663736071, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 0, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 1300649428514, 887240892199, 0, 1317842481106, 547079247729, 1300649428515, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals015 20 1) 35312013
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck015_21_0 :
    integerResidualCheck 15 21 0 (dualNumerators015 21 0) ∧
    integerMassCheck 15 21 0 (dualNumerators015 21 0) := by
  apply integerChecks_of_simple 15 21 0 (dualNumerators015 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 604293255477, 704608169863, 757887471419, 892563449519, 583650214286, 725251211053]) (branchResiduals015 21 0) 11182451
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck015_21_1 :
    integerResidualCheck 15 21 1 (dualNumerators015 21 1) ∧
    integerMassCheck 15 21 1 (dualNumerators015 21 1) := by
  apply integerChecks_of_simple 15 21 1 (dualNumerators015 21 1)
    (![113874129702, 20963906509, 113874129702, 0, 1, 11418112698, 13520155082, 0, 159661338854, 113874129702, 11418112698, 0, 218901591686, 1189054541590, 13520155082, 0, 0, 1189054541591, 1567617472129, 323892577801, 176489697786, 17696550257, 176489697786, 208980953998, 11418112698, 0, 218901591686, 1189054541590, 0, 0, 17696550257, 1842875789658, 878795318822, 964080470836, 0, 176489697786, 73266609994, 174187148961, 17696550257, 0, 110341723711, 137112035244]) (branchResiduals015 21 1) 11182451
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck015_22_0 :
    integerResidualCheck 15 22 0 (dualNumerators015 22 0) ∧
    integerMassCheck 15 22 0 (dualNumerators015 22 0) := by
  apply integerChecks_of_simple 15 22 0 (dualNumerators015 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 104985155316, 659014318321, 0, 460183470977, 599623014547, 45593851542, 64927501002, 736408579717, 287707656866, 357509209222]) (branchResiduals015 22 0) 6465674
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck015_22_1 :
    integerResidualCheck 15 22 1 (dualNumerators015 22 1) ∧
    integerMassCheck 15 22 1 (dualNumerators015 22 1) := by
  apply integerChecks_of_simple 15 22 1 (dualNumerators015 22 1)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 5063622582, 0, 15434809046, 83840549778, 5995821236, 0, 0, 83840549778, 1170080822236, 143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 17855961539, 112085697126, 0, 78268383123, 32491749791, 77247265314, 7847938961, 0, 48933554844, 60805460262]) (branchResiduals015 22 1) 6465674
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck015_23_0 :
    integerResidualCheck 15 23 0 (dualNumerators015 23 0) ∧
    integerMassCheck 15 23 0 (dualNumerators015 23 0) := by
  apply integerChecks_of_simple 15 23 0 (dualNumerators015 23 0)
    (![525362030296, 96717669897, 525362030296, 0, 2, 1982073878105, 2346968095804, 0, 736602820676, 525362030295, 1982073878106, 0, 160571279833, 872209325039, 2346968095804, 0, 0, 872209325040, 1769383425546, 1494289025232, 814241006256, 3071949885821, 814241006256, 964140481889, 1982073878106, 0, 160571279833, 872209325039, 0, 0, 3071949885821, 1351808005779, 1000000000000, 351808005780, 814241006256, 0, 1141636028738, 0, 970267099055, 2101682786767, 509065159462, 632570869277]) (branchResiduals015 23 0) 35297932
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck015_23_1 :
    integerResidualCheck 15 23 1 (dualNumerators015 23 1) ∧
    integerMassCheck 15 23 1 (dualNumerators015 23 1) := by
  apply integerChecks_of_simple 15 23 1 (dualNumerators015 23 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 85258653367, 0, 259883317327, 1411663736071, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 0, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 547079247729, 1300649428515, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals015 23 1) 35297932
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck015_24_0 :
    integerResidualCheck 15 24 0 (dualNumerators015 24 0) ∧
    integerMassCheck 15 24 0 (dualNumerators015 24 0) := by
  apply integerChecks_of_simple 15 24 0 (dualNumerators015 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 384946583730, 686246488518, 705016048726, 601815130180, 477654049462, 593539022787]) (branchResiduals015 24 0) 9356857
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck015_24_1 :
    integerResidualCheck 15 24 1 (dualNumerators015 24 1) ∧
    integerMassCheck 15 24 1 (dualNumerators015 24 1) := by
  apply integerChecks_of_simple 15 24 1 (dualNumerators015 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 587483804282, 282115266095, 48434165160, 99625565721, 0, 0, 66021086067, 82038644814]) (branchResiduals015 24 1) 9356857
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck015_25_0 :
    integerResidualCheck 15 25 0 (dualNumerators015 25 0) ∧
    integerMassCheck 15 25 0 (dualNumerators015 25 0) := by
  apply integerChecks_of_simple 15 25 0 (dualNumerators015 25 0)
    (![31307490826, 5763620872, 31307490826, 0, 1, 17498922567, 20720424919, 0, 627590994654, 447612295109, 510444268639, 0, 136807905692, 743128728920, 604415620636, 0, 0, 743128728921, 1507527629264, 1273145186690, 48522430940, 27120993710, 693739297027, 821454747430, 510444268639, 0, 136807905692, 743128728920, 0, 0, 791120467347, 1151750315250, 639144727059, 512605588192, 48522430940, 0, 333537525435, 639144727060, 0, 27120993710, 433727241876, 538955010618]) (branchResiduals015 25 0) 8671199
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck015_25_1 :
    integerResidualCheck 15 25 1 (dualNumerators015 25 1) ∧
    integerMassCheck 15 25 1 (dualNumerators015 25 1) := by
  apply integerChecks_of_simple 15 25 1 (dualNumerators015 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals015 25 1) 8671199
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck015_26_0 :
    integerResidualCheck 15 26 0 (dualNumerators015 26 0) ∧
    integerMassCheck 15 26 0 (dualNumerators015 26 0) := by
  apply integerChecks_of_simple 15 26 0 (dualNumerators015 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals015 26 0) 15099566
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck015_26_1 :
    integerResidualCheck 15 26 1 (dualNumerators015 26 1) ∧
    integerMassCheck 15 26 1 (dualNumerators015 26 1) := by
  apply integerChecks_of_simple 15 26 1 (dualNumerators015 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 879744679617, 350168760452, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals015 26 1) 15099566
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck015_27_0 :
    integerResidualCheck 15 27 0 (dualNumerators015 27 0) ∧
    integerMassCheck 15 27 0 (dualNumerators015 27 0) := by
  apply integerChecks_of_simple 15 27 0 (dualNumerators015 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 436855949686, 304617712691, 340673826058, 423325647580]) (branchResiduals015 27 0) 7338775
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck015_27_1 :
    integerResidualCheck 15 27 1 (dualNumerators015 27 1) ∧
    integerMassCheck 15 27 1 (dualNumerators015 27 1) := by
  apply integerChecks_of_simple 15 27 1 (dualNumerators015 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 953483284011, 578454657198, 377837583379, 0, 340277028102, 953483284012, 430830286610, 214386579479, 236224837801, 293536000677]) (branchResiduals015 27 1) 7338775
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck015_28_0 :
    integerResidualCheck 15 28 0 (dualNumerators015 28 0) ∧
    integerMassCheck 15 28 0 (dualNumerators015 28 0) := by
  apply integerChecks_of_simple 15 28 0 (dualNumerators015 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 374399059503, 471423145846, 287707656866, 357509209222]) (branchResiduals015 28 0) 10335557
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck015_28_1 :
    integerResidualCheck 15 28 1 (dualNumerators015 28 1) ∧
    integerMassCheck 15 28 1 (dualNumerators015 28 1) := by
  apply integerChecks_of_simple 15 28 1 (dualNumerators015 28 1)
    (![70965414109, 13064532837, 70965414109, 0, 1, 500061019298, 592120844340, 0, 99499623476, 70965414109, 7115673227, 0, 112439668685, 610762569950, 8425648624, 0, 0, 610762569951, 1239006666393, 201847170824, 109986917328, 775027817129, 109986917328, 130235198988, 7115673227, 0, 112439668685, 610762569950, 0, 0, 11028343493, 946600440957, 438442294144, 508158146813, 0, 109986917328, 360985704208, 438442294145, 11028343493, 0, 68764047964, 85447084301]) (branchResiduals015 28 1) 10335557
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck015_29_0 :
    integerResidualCheck 15 29 0 (dualNumerators015 29 0) ∧
    integerMassCheck 15 29 0 (dualNumerators015 29 0) := by
  apply integerChecks_of_simple 15 29 0 (dualNumerators015 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals015 29 0) 40352153
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck015_29_1 :
    integerResidualCheck 15 29 1 (dualNumerators015 29 1) ∧
    integerMassCheck 15 29 1 (dualNumerators015 29 1) := by
  apply integerChecks_of_simple 15 29 1 (dualNumerators015 29 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 85258653367, 0, 259883317327, 1411663736071, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 0, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 1547079247729, 300649428515, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals015 29 1) 40352153
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck015_30_0 :
    integerResidualCheck 15 30 0 (dualNumerators015 30 0) ∧
    integerMassCheck 15 30 0 (dualNumerators015 30 0) := by
  apply integerChecks_of_simple 15 30 0 (dualNumerators015 30 0)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 5063622582, 0, 15434809046, 83840549778, 5995821236, 0, 0, 83840549778, 170080822236, 1143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 17855961539, 112085697126, 0, 78268383123, 91883053566, 17855961539, 7847938961, 0, 108324858619, 1414156487]) (branchResiduals015 30 0) 7680628
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck015_30_1 :
    integerResidualCheck 15 30 1 (dualNumerators015 30 1) ∧
    integerMassCheck 15 30 1 (dualNumerators015 30 1) := by
  apply integerChecks_of_simple 15 30 1 (dualNumerators015 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 669214578381, 235435046259, 544901951702, 0, 94784895256, 669214578382, 621279733097, 307371055990, 281282522283, 482716951355]) (branchResiduals015 30 1) 7680628
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck015_31_0 :
    integerResidualCheck 15 31 0 (dualNumerators015 31 0) ∧
    integerMassCheck 15 31 0 (dualNumerators015 31 0) := by
  apply integerChecks_of_simple 15 31 0 (dualNumerators015 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 1032415642125, 1, 592902192609, 0, 1222480453651, 0, 500720887661, 0, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642125, 0, 592902192609, 0, 0, 0, 1600106408231, 776050524992, 0, 776050524992, 634078107472, 938764468189, 655394283555, 1, 827665375816, 772441032416, 655394283556, 0]) (branchResiduals015 31 0) 32891612
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck015_31_1 :
    integerResidualCheck 15 31 1 (dualNumerators015 31 1) ∧
    integerMassCheck 15 31 1 (dualNumerators015 31 1) := by
  apply integerChecks_of_simple 15 31 1 (dualNumerators015 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 556963843680, 992902647048, 18993131489, 744564115640, 327950144489, 1221916346239]) (branchResiduals015 31 1) 32891612
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck015_32_0 :
    integerResidualCheck 15 32 0 (dualNumerators015 32 0) ∧
    integerMassCheck 15 32 0 (dualNumerators015 32 0) := by
  apply integerChecks_of_simple 15 32 0 (dualNumerators015 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 0, 2743468108582, 2028778803022, 0, 505064750776, 2743468108580, 1713354977902, 2, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 2028778803022, 0, 0, 0, 4252009289869, 2655471466972, 364902194330, 2290569272643, 0, 1599482877825, 1877710578357, 364902194331, 262156886566, 3989852403304, 0, 2242612772688]) (branchResiduals015 32 0) 67647473
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck015_32_1 :
    integerResidualCheck 15 32 1 (dualNumerators015 32 1) ∧
    integerMassCheck 15 32 1 (dualNumerators015 32 1) := by
  apply integerChecks_of_simple 15 32 1 (dualNumerators015 32 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 85258653367, 0, 259883317327, 1411663736071, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 0, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 1547079247729, 300649428515, 132139529898, 0, 1823917842058, 23810834186]) (branchResiduals015 32 1) 67647473
    branchSparseDots015 branchIntegerCurvature015 branchDots015
    branchIntegerCurvature015_entry rfl
    (congrFun (congrFun branchResiduals015_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks015 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 15 j s (dualNumerators015 j s) ∧
    integerMassCheck 15 j s (dualNumerators015 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck015_0_0
    · exact integerCheck015_0_1
  · fin_cases s
    · exact integerCheck015_1_0
    · exact integerCheck015_1_1
  · fin_cases s
    · exact integerCheck015_2_0
    · exact integerCheck015_2_1
  · fin_cases s
    · exact integerCheck015_3_0
    · exact integerCheck015_3_1
  · fin_cases s
    · exact integerCheck015_4_0
    · exact integerCheck015_4_1
  · fin_cases s
    · exact integerCheck015_5_0
    · exact integerCheck015_5_1
  · fin_cases s
    · exact integerCheck015_6_0
    · exact integerCheck015_6_1
  · fin_cases s
    · exact integerCheck015_7_0
    · exact integerCheck015_7_1
  · fin_cases s
    · exact integerCheck015_8_0
    · exact integerCheck015_8_1
  · fin_cases s
    · exact integerCheck015_9_0
    · exact integerCheck015_9_1
  · fin_cases s
    · exact integerCheck015_10_0
    · exact integerCheck015_10_1
  · fin_cases s
    · exact integerCheck015_11_0
    · exact integerCheck015_11_1
  · fin_cases s
    · exact integerCheck015_12_0
    · exact integerCheck015_12_1
  · fin_cases s
    · exact integerCheck015_13_0
    · exact integerCheck015_13_1
  · fin_cases s
    · exact integerCheck015_14_0
    · exact integerCheck015_14_1
  · fin_cases s
    · exact integerCheck015_15_0
    · exact integerCheck015_15_1
  · fin_cases s
    · exact integerCheck015_16_0
    · exact integerCheck015_16_1
  · fin_cases s
    · exact integerCheck015_17_0
    · exact integerCheck015_17_1
  · fin_cases s
    · exact integerCheck015_18_0
    · exact integerCheck015_18_1
  · fin_cases s
    · exact integerCheck015_19_0
    · exact integerCheck015_19_1
  · fin_cases s
    · exact integerCheck015_20_0
    · exact integerCheck015_20_1
  · fin_cases s
    · exact integerCheck015_21_0
    · exact integerCheck015_21_1
  · fin_cases s
    · exact integerCheck015_22_0
    · exact integerCheck015_22_1
  · fin_cases s
    · exact integerCheck015_23_0
    · exact integerCheck015_23_1
  · fin_cases s
    · exact integerCheck015_24_0
    · exact integerCheck015_24_1
  · fin_cases s
    · exact integerCheck015_25_0
    · exact integerCheck015_25_1
  · fin_cases s
    · exact integerCheck015_26_0
    · exact integerCheck015_26_1
  · fin_cases s
    · exact integerCheck015_27_0
    · exact integerCheck015_27_1
  · fin_cases s
    · exact integerCheck015_28_0
    · exact integerCheck015_28_1
  · fin_cases s
    · exact integerCheck015_29_0
    · exact integerCheck015_29_1
  · fin_cases s
    · exact integerCheck015_30_0
    · exact integerCheck015_30_1
  · fin_cases s
    · exact integerCheck015_31_0
    · exact integerCheck015_31_1
  · fin_cases s
    · exact integerCheck015_32_0
    · exact integerCheck015_32_1

end ElevenSquare.Tasks.T06
