import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual071
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
import ElevenSquare.Tasks.T06.SparseColumn42
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn55
import ElevenSquare.Tasks.T06.SparseColumn56

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix071 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix071_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = branchIntegerMatrix071 := by
  change roundedGradients ∘ branchRows 71 = branchIntegerMatrix071
  rw [show branchRows 71 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 54, 55, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix071]

theorem branchColumn071_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 0) i) = _
  rw [branchColumn071_0]
  exact sparseColumn00_sum n

theorem branchColumn071_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 1) i) = _
  rw [branchColumn071_1]
  exact sparseColumn01_sum n

theorem branchColumn071_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 2) i) = _
  rw [branchColumn071_2]
  exact sparseColumn02_sum n

theorem branchColumn071_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 3) i) = _
  rw [branchColumn071_3]
  exact sparseColumn03_sum n

theorem branchColumn071_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 4) i) = _
  rw [branchColumn071_4]
  exact sparseColumn04_sum n

theorem branchColumn071_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 5) i) = _
  rw [branchColumn071_5]
  exact sparseColumn05_sum n

theorem branchColumn071_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 6) i) = _
  rw [branchColumn071_6]
  exact sparseColumn06_sum n

theorem branchColumn071_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 7) i) = _
  rw [branchColumn071_7]
  exact sparseColumn07_sum n

theorem branchColumn071_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 8) i) = _
  rw [branchColumn071_8]
  exact sparseColumn08_sum n

theorem branchColumn071_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 9) i) = _
  rw [branchColumn071_9]
  exact sparseColumn09_sum n

theorem branchColumn071_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 10) i) = _
  rw [branchColumn071_10]
  exact sparseColumn10_sum n

theorem branchColumn071_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 11) i) = _
  rw [branchColumn071_11]
  exact sparseColumn11_sum n

theorem branchColumn071_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 12) i) = _
  rw [branchColumn071_12]
  exact sparseColumn35_sum n

theorem branchColumn071_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 13) i) = _
  rw [branchColumn071_13]
  exact sparseColumn36_sum n

theorem branchColumn071_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 14) i) = _
  rw [branchColumn071_14]
  exact sparseColumn41_sum n

theorem branchColumn071_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 15) i) = _
  rw [branchColumn071_15]
  exact sparseColumn38_sum n

theorem branchColumn071_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 16) i) = _
  rw [branchColumn071_16]
  exact sparseColumn39_sum n

theorem branchColumn071_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 17) i) = _
  rw [branchColumn071_17]
  exact sparseColumn17_sum n

theorem branchColumn071_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 18) i) = _
  rw [branchColumn071_18]
  exact sparseColumn18_sum n

theorem branchColumn071_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 19) i) = _
  rw [branchColumn071_19]
  exact sparseColumn19_sum n

theorem branchColumn071_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 20) = sparseColumn55 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 20) = sparseDot55 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 20) i) = _
  rw [branchColumn071_20]
  exact sparseColumn55_sum n

theorem branchColumn071_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 21) i) = _
  rw [branchColumn071_21]
  exact sparseColumn21_sum n

theorem branchColumn071_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 22) i) = _
  rw [branchColumn071_22]
  exact sparseColumn22_sum n

theorem branchColumn071_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 23) = sparseColumn23 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 23) = sparseDot23 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 23) i) = _
  rw [branchColumn071_23]
  exact sparseColumn23_sum n

theorem branchColumn071_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 24) i) = _
  rw [branchColumn071_24]
  exact sparseColumn24_sum n

theorem branchColumn071_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 25) i) = _
  rw [branchColumn071_25]
  exact sparseColumn25_sum n

theorem branchColumn071_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 26) = sparseColumn56 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 26) = sparseDot56 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 26) i) = _
  rw [branchColumn071_26]
  exact sparseColumn56_sum n

theorem branchColumn071_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 27) i) = _
  rw [branchColumn071_27]
  exact sparseColumn27_sum n

theorem branchColumn071_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 28) i) = _
  rw [branchColumn071_28]
  exact sparseColumn28_sum n

theorem branchColumn071_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 29) = sparseColumn42 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 29) = sparseDot42 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 29) i) = _
  rw [branchColumn071_29]
  exact sparseColumn42_sum n

theorem branchColumn071_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 30) i) = _
  rw [branchColumn071_30]
  exact sparseColumn30_sum n

theorem branchColumn071_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 31) i) = _
  rw [branchColumn071_31]
  exact sparseColumn31_sum n

theorem branchColumn071_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 71 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 71 i)) = _
  rw [branchIntegerMatrix071_eq]
  simp only [branchIntegerMatrix071, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot071_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 71 i) 32) i) = _
  rw [branchColumn071_32]
  exact sparseColumn43_sum n

def branchSparseDots071 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot55, sparseDot21, sparseDot22, sparseDot23, sparseDot24, sparseDot25, sparseDot56, sparseDot27, sparseDot28, sparseDot42, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot071_0 :
    branchSparseDots071 0 = sparseDot00 := rfl

private theorem branchSparseDot071_1 :
    branchSparseDots071 1 = sparseDot01 := rfl

private theorem branchSparseDot071_2 :
    branchSparseDots071 2 = sparseDot02 := rfl

private theorem branchSparseDot071_3 :
    branchSparseDots071 3 = sparseDot03 := rfl

private theorem branchSparseDot071_4 :
    branchSparseDots071 4 = sparseDot04 := rfl

private theorem branchSparseDot071_5 :
    branchSparseDots071 5 = sparseDot05 := rfl

private theorem branchSparseDot071_6 :
    branchSparseDots071 6 = sparseDot06 := rfl

private theorem branchSparseDot071_7 :
    branchSparseDots071 7 = sparseDot07 := rfl

private theorem branchSparseDot071_8 :
    branchSparseDots071 8 = sparseDot08 := rfl

private theorem branchSparseDot071_9 :
    branchSparseDots071 9 = sparseDot09 := rfl

private theorem branchSparseDot071_10 :
    branchSparseDots071 10 = sparseDot10 := rfl

private theorem branchSparseDot071_11 :
    branchSparseDots071 11 = sparseDot11 := rfl

private theorem branchSparseDot071_12 :
    branchSparseDots071 12 = sparseDot35 := rfl

private theorem branchSparseDot071_13 :
    branchSparseDots071 13 = sparseDot36 := rfl

private theorem branchSparseDot071_14 :
    branchSparseDots071 14 = sparseDot41 := rfl

private theorem branchSparseDot071_15 :
    branchSparseDots071 15 = sparseDot38 := rfl

private theorem branchSparseDot071_16 :
    branchSparseDots071 16 = sparseDot39 := rfl

private theorem branchSparseDot071_17 :
    branchSparseDots071 17 = sparseDot17 := rfl

private theorem branchSparseDot071_18 :
    branchSparseDots071 18 = sparseDot18 := rfl

private theorem branchSparseDot071_19 :
    branchSparseDots071 19 = sparseDot19 := rfl

private theorem branchSparseDot071_20 :
    branchSparseDots071 20 = sparseDot55 := rfl

private theorem branchSparseDot071_21 :
    branchSparseDots071 21 = sparseDot21 := rfl

private theorem branchSparseDot071_22 :
    branchSparseDots071 22 = sparseDot22 := rfl

private theorem branchSparseDot071_23 :
    branchSparseDots071 23 = sparseDot23 := rfl

private theorem branchSparseDot071_24 :
    branchSparseDots071 24 = sparseDot24 := rfl

private theorem branchSparseDot071_25 :
    branchSparseDots071 25 = sparseDot25 := rfl

private theorem branchSparseDot071_26 :
    branchSparseDots071 26 = sparseDot56 := rfl

private theorem branchSparseDot071_27 :
    branchSparseDots071 27 = sparseDot27 := rfl

private theorem branchSparseDot071_28 :
    branchSparseDots071 28 = sparseDot28 := rfl

private theorem branchSparseDot071_29 :
    branchSparseDots071 29 = sparseDot42 := rfl

private theorem branchSparseDot071_30 :
    branchSparseDots071 30 = sparseDot30 := rfl

private theorem branchSparseDot071_31 :
    branchSparseDots071 31 = sparseDot31 := rfl

private theorem branchSparseDot071_32 :
    branchSparseDots071 32 = sparseDot43 := rfl

theorem branchDots071 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 71 i) k) = branchSparseDots071 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot071_0 n
      _ = _ := congrFun branchSparseDot071_0.symm n
  · calc
      _ = sparseDot01 n := branchDot071_1 n
      _ = _ := congrFun branchSparseDot071_1.symm n
  · calc
      _ = sparseDot02 n := branchDot071_2 n
      _ = _ := congrFun branchSparseDot071_2.symm n
  · calc
      _ = sparseDot03 n := branchDot071_3 n
      _ = _ := congrFun branchSparseDot071_3.symm n
  · calc
      _ = sparseDot04 n := branchDot071_4 n
      _ = _ := congrFun branchSparseDot071_4.symm n
  · calc
      _ = sparseDot05 n := branchDot071_5 n
      _ = _ := congrFun branchSparseDot071_5.symm n
  · calc
      _ = sparseDot06 n := branchDot071_6 n
      _ = _ := congrFun branchSparseDot071_6.symm n
  · calc
      _ = sparseDot07 n := branchDot071_7 n
      _ = _ := congrFun branchSparseDot071_7.symm n
  · calc
      _ = sparseDot08 n := branchDot071_8 n
      _ = _ := congrFun branchSparseDot071_8.symm n
  · calc
      _ = sparseDot09 n := branchDot071_9 n
      _ = _ := congrFun branchSparseDot071_9.symm n
  · calc
      _ = sparseDot10 n := branchDot071_10 n
      _ = _ := congrFun branchSparseDot071_10.symm n
  · calc
      _ = sparseDot11 n := branchDot071_11 n
      _ = _ := congrFun branchSparseDot071_11.symm n
  · calc
      _ = sparseDot35 n := branchDot071_12 n
      _ = _ := congrFun branchSparseDot071_12.symm n
  · calc
      _ = sparseDot36 n := branchDot071_13 n
      _ = _ := congrFun branchSparseDot071_13.symm n
  · calc
      _ = sparseDot41 n := branchDot071_14 n
      _ = _ := congrFun branchSparseDot071_14.symm n
  · calc
      _ = sparseDot38 n := branchDot071_15 n
      _ = _ := congrFun branchSparseDot071_15.symm n
  · calc
      _ = sparseDot39 n := branchDot071_16 n
      _ = _ := congrFun branchSparseDot071_16.symm n
  · calc
      _ = sparseDot17 n := branchDot071_17 n
      _ = _ := congrFun branchSparseDot071_17.symm n
  · calc
      _ = sparseDot18 n := branchDot071_18 n
      _ = _ := congrFun branchSparseDot071_18.symm n
  · calc
      _ = sparseDot19 n := branchDot071_19 n
      _ = _ := congrFun branchSparseDot071_19.symm n
  · calc
      _ = sparseDot55 n := branchDot071_20 n
      _ = _ := congrFun branchSparseDot071_20.symm n
  · calc
      _ = sparseDot21 n := branchDot071_21 n
      _ = _ := congrFun branchSparseDot071_21.symm n
  · calc
      _ = sparseDot22 n := branchDot071_22 n
      _ = _ := congrFun branchSparseDot071_22.symm n
  · calc
      _ = sparseDot23 n := branchDot071_23 n
      _ = _ := congrFun branchSparseDot071_23.symm n
  · calc
      _ = sparseDot24 n := branchDot071_24 n
      _ = _ := congrFun branchSparseDot071_24.symm n
  · calc
      _ = sparseDot25 n := branchDot071_25 n
      _ = _ := congrFun branchSparseDot071_25.symm n
  · calc
      _ = sparseDot56 n := branchDot071_26 n
      _ = _ := congrFun branchSparseDot071_26.symm n
  · calc
      _ = sparseDot27 n := branchDot071_27 n
      _ = _ := congrFun branchSparseDot071_27.symm n
  · calc
      _ = sparseDot28 n := branchDot071_28 n
      _ = _ := congrFun branchSparseDot071_28.symm n
  · calc
      _ = sparseDot42 n := branchDot071_29 n
      _ = _ := congrFun branchSparseDot071_29.symm n
  · calc
      _ = sparseDot30 n := branchDot071_30 n
      _ = _ := congrFun branchSparseDot071_30.symm n
  · calc
      _ = sparseDot31 n := branchDot071_31 n
      _ = _ := congrFun branchSparseDot071_31.symm n
  · calc
      _ = sparseDot43 n := branchDot071_32 n
      _ = _ := congrFun branchSparseDot071_32.symm n

def branchIntegerCurvature071 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101981296, 101981296, 79086693, 79086693, 115699695, 115699695, 48290998, 48290998, 289103692, 289103692]

theorem branchIntegerCurvature071_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 71 i)) = branchIntegerCurvature071 := by
  change curvatureNumerators ∘ branchRows 71 = branchIntegerCurvature071
  rw [show branchRows 71 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 54, 55, 36, 37, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature071_entry (i : Fin 42) :
    curvatureNumerators (branchRows 71 i) = branchIntegerCurvature071 i :=
  congrFun branchIntegerCurvature071_eq i

def branchResiduals071 : Fin 33 → Fin 2 → ℕ := ![![1298062648000904, 33000000000000], ![1546631512471428, 33000000000000], ![1581939653070566, 1334780787543421], ![33000000000000, 1021346397345738], ![857887371571166, 33000000000000], ![1052073096392510, 893570175606621], ![718257204289986, 624777238175104], ![33000000000000, 760079485303505], ![1576989689005104, 1128902210052645], ![1024064357040925, 33000000000000], ![33000000000000, 774415690938721], ![508881454004626, 463036157794575], ![988662669606423, 66000000000000], ![33000000000000, 860323019979621], ![1052033358596110, 485220088890799], ![474115181952813, 33000000000000], ![66000000000000, 740904687733296], ![662962526781216, 460389900399984], ![622795825683979, 256840141033836], ![629383085475973, 511344382751990], ![1317222505951093, 852031070359942], ![751019970632309, 374549059863808], ![470441009569099, 91293199863085], ![1317425653450208, 852031070359942], ![669664059680761, 230382126611112], ![506986350042259, 218713669397988], ![396136216194598, 852031070359942], ![407377540739132, 545743724710572], ![283888335003034, 298234366589561], ![396136216194598, 852031070359942], ![97453635560617, 553153156150881], ![967267804214635, 648448846285741], ![2021220220362480, 917924671277156]]

theorem branchResiduals071_eq : residualNumerators 71 = branchResiduals071 := rfl

theorem integerCheck071_0_0 :
    integerResidualCheck 71 0 0 (dualNumerators071 0 0) ∧
    integerMassCheck 71 0 0 (dualNumerators071 0 0) := by
  apply integerChecks_of_simple 71 0 0 (dualNumerators071 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 143134913131, 2029911410936, 0, 1308901425339, 1692057632752, 143134913133, 1896652816305, 70360777679, 818327875519, 1016864670366]) (branchResiduals071 0 0) 18767167
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck071_0_1 :
    integerResidualCheck 71 0 1 (dualNumerators071 0 1) ∧
    integerMassCheck 71 0 1 (dualNumerators071 0 1) := by
  apply integerChecks_of_simple 71 0 1 (dualNumerators071 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals071 0 1) 18767167
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck071_1_0 :
    integerResidualCheck 71 1 0 (dualNumerators071 1 0) ∧
    integerMassCheck 71 1 0 (dualNumerators071 1 0) := by
  apply integerChecks_of_simple 71 1 0 (dualNumerators071 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 169485647445, 2403612383675, 0, 1549866490727, 2003560676621, 169485647447, 2245821257146, 83313998652, 968979732271, 1204066591796]) (branchResiduals071 1 0) 22176635
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck071_1_1 :
    integerResidualCheck 71 1 1 (dualNumerators071 1 1) ∧
    integerMassCheck 71 1 1 (dualNumerators071 1 1) := by
  apply integerChecks_of_simple 71 1 1 (dualNumerators071 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals071 1 1) 22176635
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck071_2_0 :
    integerResidualCheck 71 2 0 (dualNumerators071 2 0) ∧
    integerMassCheck 71 2 0 (dualNumerators071 2 0) := by
  apply integerChecks_of_simple 71 2 0 (dualNumerators071 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 169485647445, 2403612383677, 0, 1549866490728, 2003560676622, 169485647447, 2245821257148, 83313998652, 968979732272, 1204066591797]) (branchResiduals071 2 0) 22681452
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck071_2_1 :
    integerResidualCheck 71 2 1 (dualNumerators071 2 1) ∧
    integerMassCheck 71 2 1 (dualNumerators071 2 1) := by
  apply integerChecks_of_simple 71 2 1 (dualNumerators071 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 143134913131, 2029911410934, 0, 1308901425338, 1692057632751, 143134913133, 1896652816304, 70360777679, 818327875518, 1016864670365]) (branchResiduals071 2 1) 22681452
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck071_3_0 :
    integerResidualCheck 71 3 0 (dualNumerators071 3 0) ∧
    integerMassCheck 71 3 0 (dualNumerators071 3 0) := by
  apply integerChecks_of_simple 71 3 0 (dualNumerators071 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals071 3 0) 16360330
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck071_3_1 :
    integerResidualCheck 71 3 1 (dualNumerators071 3 1) ∧
    integerMassCheck 71 3 1 (dualNumerators071 3 1) := by
  apply integerChecks_of_simple 71 3 1 (dualNumerators071 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000000, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 112780107974, 1599425486726, 0, 1031321016287, 1333220793899, 112780107975, 1494427213684, 55439277044, 644784030255, 801216871619]) (branchResiduals071 3 1) 16360330
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck071_4_0 :
    integerResidualCheck 71 4 0 (dualNumerators071 4 0) ∧
    integerMassCheck 71 4 0 (dualNumerators071 4 0) := by
  apply integerChecks_of_simple 71 4 0 (dualNumerators071 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 95245651777, 1350755250097, 0, 870976665588, 1125938658502, 95245651778, 1262081554611, 46819870729, 544536410901, 676647899379]) (branchResiduals071 4 0) 13760362
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck071_4_1 :
    integerResidualCheck 71 4 1 (dualNumerators071 4 1) ∧
    integerMassCheck 71 4 1 (dualNumerators071 4 1) := by
  apply integerChecks_of_simple 71 4 1 (dualNumerators071 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals071 4 1) 13760362
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck071_5_0 :
    integerResidualCheck 71 5 0 (dualNumerators071 5 0) ∧
    integerMassCheck 71 5 0 (dualNumerators071 5 0) := by
  apply integerChecks_of_simple 71 5 0 (dualNumerators071 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 112780107974, 1599425486727, 0, 1031321016288, 1333220793900, 112780107975, 1494427213685, 55439277044, 644784030255, 801216871620]) (branchResiduals071 5 0) 17641130
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck071_5_1 :
    integerResidualCheck 71 5 1 (dualNumerators071 5 1) ∧
    integerMassCheck 71 5 1 (dualNumerators071 5 1) := by
  apply integerChecks_of_simple 71 5 1 (dualNumerators071 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 95245651777, 1350755250096, 0, 870976665588, 1125938658501, 95245651778, 1262081554610, 46819870729, 544536410901, 676647899378]) (branchResiduals071 5 1) 17641130
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck071_6_0 :
    integerResidualCheck 71 6 0 (dualNumerators071 6 0) ∧
    integerMassCheck 71 6 0 (dualNumerators071 6 0) := by
  apply integerChecks_of_simple 71 6 0 (dualNumerators071 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 659499318402, 1175693227483, 103906894360, 5439901403, 818327875519, 1016864670366]) (branchResiduals071 6 0) 8962451
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck071_6_1 :
    integerResidualCheck 71 6 1 (dualNumerators071 6 1) ∧
    integerMassCheck 71 6 1 (dualNumerators071 6 1) := by
  apply integerChecks_of_simple 71 6 1 (dualNumerators071 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 760187607595, 1097479190627, 0, 0]) (branchResiduals071 6 1) 8962451
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck071_7_0 :
    integerResidualCheck 71 7 0 (dualNumerators071 7 0) ∧
    integerMassCheck 71 7 0 (dualNumerators071 7 0) := by
  apply integerChecks_of_simple 71 7 0 (dualNumerators071 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals071 7 0) 10424794
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck071_7_1 :
    integerResidualCheck 71 7 1 (dualNumerators071 7 1) ∧
    integerMassCheck 71 7 1 (dualNumerators071 7 1) := by
  apply integerChecks_of_simple 71 7 1 (dualNumerators071 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 84742823723, 1201806191840, 0, 774933245365, 1001780338312, 84742823724, 1122910628575, 41656999326, 484489866137, 602033295899]) (branchResiduals071 7 1) 10424794
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck071_8_0 :
    integerResidualCheck 71 8 0 (dualNumerators071 8 0) ∧
    integerMassCheck 71 8 0 (dualNumerators071 8 0) := by
  apply integerChecks_of_simple 71 8 0 (dualNumerators071 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 169485647445, 2403612383679, 0, 1549866490730, 2003560676624, 169485647447, 2245821257150, 83313998652, 968979732273, 1204066591798]) (branchResiduals071 8 0) 22681452
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck071_8_1 :
    integerResidualCheck 71 8 1 (dualNumerators071 8 1) ∧
    integerMassCheck 71 8 1 (dualNumerators071 8 1) := by
  apply integerChecks_of_simple 71 8 1 (dualNumerators071 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 120881051971, 1714311493912, 0, 1105400337063, 1428985438754, 120881051972, 1601771242546, 59421455166, 691098574663, 858767916063]) (branchResiduals071 8 1) 22681452
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck071_9_0 :
    integerResidualCheck 71 9 0 (dualNumerators071 9 0) ∧
    integerMassCheck 71 9 0 (dualNumerators071 9 0) := by
  apply integerChecks_of_simple 71 9 0 (dualNumerators071 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 112780107974, 1599425486726, 0, 1031321016287, 1333220793899, 112780107975, 1494427213684, 55439277044, 644784030255, 801216871619]) (branchResiduals071 9 0) 16350530
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck071_9_1 :
    integerResidualCheck 71 9 1 (dualNumerators071 9 1) ∧
    integerMassCheck 71 9 1 (dualNumerators071 9 1) := by
  apply integerChecks_of_simple 71 9 1 (dualNumerators071 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals071 9 1) 16350530
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck071_10_0 :
    integerResidualCheck 71 10 0 (dualNumerators071 10 0) ∧
    integerMassCheck 71 10 0 (dualNumerators071 10 0) := by
  apply integerChecks_of_simple 71 10 0 (dualNumerators071 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals071 10 0) 10683139
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck071_10_1 :
    integerResidualCheck 71 10 1 (dualNumerators071 10 1) ∧
    integerMassCheck 71 10 1 (dualNumerators071 10 1) := by
  apply integerChecks_of_simple 71 10 1 (dualNumerators071 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 86215139428, 1222686285911, 0, 788396879662, 1019185197635, 86215139429, 1142419996822, 42380745027, 492907358117, 612492978948]) (branchResiduals071 10 1) 10683139
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck071_11_0 :
    integerResidualCheck 71 11 0 (dualNumerators071 11 0) ∧
    integerMassCheck 71 11 0 (dualNumerators071 11 0) := by
  apply integerChecks_of_simple 71 11 0 (dualNumerators071 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 53583766880, 759914527140, 0, 489998333105, 633436104137, 53583766880, 710028043730, 26340152980, 306347970271, 380671900746]) (branchResiduals071 11 0) 15120968
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck071_11_1 :
    integerResidualCheck 71 11 1 (dualNumerators071 11 1) ∧
    integerMassCheck 71 11 1 (dualNumerators071 11 1) := by
  apply integerChecks_of_simple 71 11 1 (dualNumerators071 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 48862235961, 692954696876, 0, 446822154676, 577620913742, 48862235962, 647463958437, 24019191727, 279354134309, 347129015395]) (branchResiduals071 11 1) 15120968
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck071_12_0 :
    integerResidualCheck 71 12 0 (dualNumerators071 12 0) ∧
    integerMassCheck 71 12 0 (dualNumerators071 12 0) := by
  apply integerChecks_of_simple 71 12 0 (dualNumerators071 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 112780107974, 1599425486726, 0, 1031321016287, 1333220793899, 112780107975, 1494427213684, 55439277044, 644784030255, 801216871619]) (branchResiduals071 12 0) 16348076
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck071_12_1 :
    integerResidualCheck 71 12 1 (dualNumerators071 12 1) ∧
    integerMassCheck 71 12 1 (dualNumerators071 12 1) := by
  apply integerChecks_of_simple 71 12 1 (dualNumerators071 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals071 12 1) 16348076
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck071_13_0 :
    integerResidualCheck 71 13 0 (dualNumerators071 13 0) ∧
    integerMassCheck 71 13 0 (dualNumerators071 13 0) := by
  apply integerChecks_of_simple 71 13 0 (dualNumerators071 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals071 13 0) 13962901
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck071_13_1 :
    integerResidualCheck 71 13 1 (dualNumerators071 13 1) ∧
    integerMassCheck 71 13 1 (dualNumerators071 13 1) := by
  apply integerChecks_of_simple 71 13 1 (dualNumerators071 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000001, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 95245651777, 1350755250097, 0, 870976665588, 1125938658502, 95245651778, 1262081554611, 46819870729, 544536410901, 676647899379]) (branchResiduals071 13 1) 13962901
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck071_14_0 :
    integerResidualCheck 71 14 0 (dualNumerators071 14 0) ∧
    integerMassCheck 71 14 0 (dualNumerators071 14 0) := by
  apply integerChecks_of_simple 71 14 0 (dualNumerators071 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 112780107974, 1599425486727, 0, 1031321016288, 1333220793900, 112780107975, 1494427213685, 55439277044, 644784030255, 801216871620]) (branchResiduals071 14 0) 20161291
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck071_14_1 :
    integerResidualCheck 71 14 1 (dualNumerators071 14 1) ∧
    integerMassCheck 71 14 1 (dualNumerators071 14 1) := by
  apply integerChecks_of_simple 71 14 1 (dualNumerators071 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 51636945849, 732305091132, 0, 472195570901, 610421919044, 51636945850, 684231097972, 25383154867, 295217646558, 366841218336]) (branchResiduals071 14 1) 20161291
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck071_15_0 :
    integerResidualCheck 71 15 0 (dualNumerators071 15 0) ∧
    integerMassCheck 71 15 0 (dualNumerators071 15 0) := by
  apply integerChecks_of_simple 71 15 0 (dualNumerators071 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 53583766880, 759914527140, 0, 489998333105, 633436104137, 53583766880, 710028043729, 26340152980, 306347970271, 380671900746]) (branchResiduals071 15 0) 12900283
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck071_15_1 :
    integerResidualCheck 71 15 1 (dualNumerators071 15 1) ∧
    integerMassCheck 71 15 1 (dualNumerators071 15 1) := by
  apply integerChecks_of_simple 71 15 1 (dualNumerators071 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals071 15 1) 12900283
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck071_16_0 :
    integerResidualCheck 71 16 0 (dualNumerators071 16 0) ∧
    integerMassCheck 71 16 0 (dualNumerators071 16 0) := by
  apply integerChecks_of_simple 71 16 0 (dualNumerators071 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals071 16 0) 10683060
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck071_16_1 :
    integerResidualCheck 71 16 1 (dualNumerators071 16 1) ∧
    integerMassCheck 71 16 1 (dualNumerators071 16 1) := by
  apply integerChecks_of_simple 71 16 1 (dualNumerators071 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 86215139428, 1222686285911, 0, 788396879662, 1019185197635, 86215139429, 1142419996822, 42380745027, 492907358117, 612492978948]) (branchResiduals071 16 1) 10683060
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck071_17_0 :
    integerResidualCheck 71 17 0 (dualNumerators071 17 0) ∧
    integerMassCheck 71 17 0 (dualNumerators071 17 0) := by
  apply integerChecks_of_simple 71 17 0 (dualNumerators071 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 70279192844, 996685800714, 0, 642670147151, 830799712474, 70279192844, 931255876838, 34547117506, 401798703857, 499280201462]) (branchResiduals071 17 0) 15120968
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck071_17_1 :
    integerResidualCheck 71 17 1 (dualNumerators071 17 1) ∧
    integerMassCheck 71 17 1 (dualNumerators071 17 1) := by
  apply integerChecks_of_simple 71 17 1 (dualNumerators071 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 48862235961, 692954696875, 0, 446822154676, 577620913742, 48862235962, 647463958437, 24019191727, 279354134309, 347129015395]) (branchResiduals071 17 1) 15120968
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck071_18_0 :
    integerResidualCheck 71 18 0 (dualNumerators071 18 0) ∧
    integerMassCheck 71 18 0 (dualNumerators071 18 0) := by
  apply integerChecks_of_simple 71 18 0 (dualNumerators071 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 170971222814, 1097425476614, 0, 763999473637, 900221849434, 170971222815, 953519106044, 33030453619, 477654049462, 593539022787]) (branchResiduals071 18 0) 13565580
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck071_18_1 :
    integerResidualCheck 71 18 1 (dualNumerators071 18 1) ∧
    integerMassCheck 71 18 1 (dualNumerators071 18 1) := by
  apply integerChecks_of_simple 71 18 1 (dualNumerators071 18 1)
    (![543792441172, 100110656623, 543792441172, 0, 1, 180671424657, 213932525007, 0, 71292007252, 50847095100, 180671424657, 0, 92181412018, 500721469249, 213932525007, 0, 0, 500721469250, 171249542446, 144624567044, 842805682483, 280016586907, 78806208846, 93314209907, 180671424657, 0, 92181412018, 500721469249, 0, 0, 280016586907, 776051426377, 0, 130834560290, 78806208846, 0, 110493093096, 1, 188935308970, 91081277938, 49269804597, 61223288500]) (branchResiduals071 18 1) 13565580
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck071_19_0 :
    integerResidualCheck 71 19 0 (dualNumerators071 19 0) ∧
    integerMassCheck 71 19 0 (dualNumerators071 19 0) := by
  apply integerChecks_of_simple 71 19 0 (dualNumerators071 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 230658067063, 840535005185, 0, 645216866088, 673991557577, 230658067064, 653752451905, 19962510160, 403390917798, 501258706842]) (branchResiduals071 19 0) 8248658
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck071_19_1 :
    integerResidualCheck 71 19 1 (dualNumerators071 19 1) ∧
    integerMassCheck 71 19 1 (dualNumerators071 19 1) := by
  apply integerChecks_of_simple 71 19 1 (dualNumerators071 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 0, 763999473637, 109777015093, 350406455885, 645216866088, 1, 838241775551, 149235960098, 287707656866, 357509209222]) (branchResiduals071 19 1) 8248658
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck071_20_0 :
    integerResidualCheck 71 20 0 (dualNumerators071 20 0) ∧
    integerMassCheck 71 20 0 (dualNumerators071 20 0) := by
  apply integerChecks_of_simple 71 20 0 (dualNumerators071 20 0)
    (![581614421967, 107073576748, 581614421967, 0, 2, 2066609823264, 2447066870339, 0, 815473519328, 581614421966, 2066609823265, 0, 177764221088, 965599897144, 2447066870339, 0, 0, 965599897145, 1958837637558, 1654287895858, 901424703130, 3202969314486, 901424703130, 1067374451772, 2066609823265, 0, 177764221088, 965599897144, 0, 0, 3202969314486, 1496550924034, 0, 1496550924034, 901424703130, 0, 1263875081678, 1, 2161136251736, 1041833062750, 563572586883, 700302494797]) (branchResiduals071 20 0) 35312013
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck071_20_1 :
    integerResidualCheck 71 20 1 (dualNumerators071 20 1) ∧
    integerMassCheck 71 20 1 (dualNumerators071 20 1) := by
  apply integerChecks_of_simple 71 20 1 (dualNumerators071 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 25837005087, 1204076434982, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals071 20 1) 35312013
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck071_21_0 :
    integerResidualCheck 71 21 0 (dualNumerators071 21 0) ∧
    integerMassCheck 71 21 0 (dualNumerators071 21 0) := by
  apply integerChecks_of_simple 71 21 0 (dualNumerators071 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 604293255477, 704608169863, 851509250277, 798941670661, 583650214286, 725251211053]) (branchResiduals071 21 0) 11182451
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck071_21_1 :
    integerResidualCheck 71 21 1 (dualNumerators071 21 1) ∧
    integerMassCheck 71 21 1 (dualNumerators071 21 1) := by
  apply integerChecks_of_simple 71 21 1 (dualNumerators071 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 860003851037, 963321782180, 3460174706, 161253783489, 75547476522, 155395681176, 0, 0, 102979506989, 127963650709]) (branchResiduals071 21 1) 11182451
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck071_22_0 :
    integerResidualCheck 71 22 0 (dualNumerators071 22 0) ∧
    integerMassCheck 71 22 0 (dualNumerators071 22 0) := by
  apply integerChecks_of_simple 71 22 0 (dualNumerators071 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 510506833659, 253492639979, 460183470977, 0, 194101336204, 451115529884, 310954038967, 490382041752, 287707656866, 357509209222]) (branchResiduals071 22 0) 6465674
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck071_22_1 :
    integerResidualCheck 71 22 1 (dualNumerators071 22 1) ∧
    integerMassCheck 71 22 1 (dualNumerators071 22 1) := by
  apply integerChecks_of_simple 71 22 1 (dualNumerators071 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 9522456419, 111749239332, 1534493418, 71511669319, 33503252091, 68913760194, 0, 0, 45668611868, 56748400418]) (branchResiduals071 22 1) 6465674
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck071_23_0 :
    integerResidualCheck 71 23 0 (dualNumerators071 23 0) ∧
    integerMassCheck 71 23 0 (dualNumerators071 23 0) := by
  apply integerChecks_of_simple 71 23 0 (dualNumerators071 23 0)
    (![581614421966, 107073576748, 581614421967, 0, 2, 2066609823263, 2447066870339, 0, 815473519327, 581614421966, 2066609823265, 0, 177764221088, 965599897143, 2447066870339, 0, 0, 965599897144, 1958837637556, 1654287895857, 901424703129, 3202969314485, 901424703129, 1067374451772, 2066609823265, 0, 177764221088, 965599897143, 0, 0, 3202969314485, 1496550924032, 1000000000000, 496550924033, 901424703129, 0, 1263875081678, 0, 2161136251736, 1041833062749, 563572586882, 700302494796]) (branchResiduals071 23 0) 35297932
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck071_23_1 :
    integerResidualCheck 71 23 1 (dualNumerators071 23 1) ∧
    integerMassCheck 71 23 1 (dualNumerators071 23 1) := by
  apply integerChecks_of_simple 71 23 1 (dualNumerators071 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 160334187224, 1881575790198, 25837005087, 1204076434982, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals071 23 1) 35297932
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck071_24_0 :
    integerResidualCheck 71 24 0 (dualNumerators071 24 0) ∧
    integerMassCheck 71 24 0 (dualNumerators071 24 0) := by
  apply integerChecks_of_simple 71 24 0 (dualNumerators071 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 384946583730, 686246488518, 569308312247, 737522866658, 477654049462, 593539022787]) (branchResiduals071 24 0) 9356857
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck071_24_1 :
    integerResidualCheck 71 24 1 (dualNumerators071 24 1) ∧
    integerMassCheck 71 24 1 (dualNumerators071 24 1) := by
  apply integerChecks_of_simple 71 24 1 (dualNumerators071 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 690777049383, 178822020994, 48434165160, 99625565721, 0, 0, 66021086067, 82038644814]) (branchResiduals071 24 1) 9356857
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck071_25_0 :
    integerResidualCheck 71 25 0 (dualNumerators071 25 0) ∧
    integerMassCheck 71 25 0 (dualNumerators071 25 0) := by
  apply integerChecks_of_simple 71 25 0 (dualNumerators071 25 0)
    (![34423495944, 6337268637, 34423495944, 0, 1, 22181646803, 26265225496, 0, 631959902239, 450728300227, 515126992874, 0, 137760279295, 748301940085, 609960421212, 0, 0, 748301940086, 1518022121617, 1282008050738, 53351822857, 34378591088, 698568688945, 827173216796, 515126992874, 0, 137760279295, 748301940085, 0, 0, 798378064725, 1159768101884, 638738616250, 521029485635, 53351822857, 0, 340714859712, 638738616250, 34378591088, 0, 436746587681, 542706888281]) (branchResiduals071 25 0) 8671199
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck071_25_1 :
    integerResidualCheck 71 25 1 (dualNumerators071 25 1) ∧
    integerMassCheck 71 25 1 (dualNumerators071 25 1) := by
  apply integerChecks_of_simple 71 25 1 (dualNumerators071 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 415529968297, 599898615461, 0, 0]) (branchResiduals071 25 1) 8671199
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck071_26_0 :
    integerResidualCheck 71 26 0 (dualNumerators071 26 0) ∧
    integerMassCheck 71 26 0 (dualNumerators071 26 0) := by
  apply integerChecks_of_simple 71 26 0 (dualNumerators071 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0]) (branchResiduals071 26 0) 15099566
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck071_26_1 :
    integerResidualCheck 71 26 1 (dualNumerators071 26 1) ∧
    integerMassCheck 71 26 1 (dualNumerators071 26 1) := by
  apply integerChecks_of_simple 71 26 1 (dualNumerators071 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 1025837005087, 204076434982, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals071 26 1) 15099566
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck071_27_0 :
    integerResidualCheck 71 27 0 (dualNumerators071 27 0) ∧
    integerMassCheck 71 27 0 (dualNumerators071 27 0) := by
  apply integerChecks_of_simple 71 27 0 (dualNumerators071 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 286173900105, 455299762271, 340673826058, 423325647580]) (branchResiduals071 27 0) 7338775
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck071_27_1 :
    integerResidualCheck 71 27 1 (dualNumerators071 27 1) ∧
    integerMassCheck 71 27 1 (dualNumerators071 27 1) := by
  apply integerChecks_of_simple 71 27 1 (dualNumerators071 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 530765167249, 1001172773960, 0, 377837583379, 762995144865, 530765167250, 621055226706, 24161639382, 236224837801, 293536000677]) (branchResiduals071 27 1) 7338775
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck071_28_0 :
    integerResidualCheck 71 28 0 (dualNumerators071 28 0) ∧
    integerMassCheck 71 28 0 (dualNumerators071 28 0) := by
  apply integerChecks_of_simple 71 28 0 (dualNumerators071 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 450383711774, 395438493575, 287707656866, 357509209222]) (branchResiduals071 28 0) 10335557
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck071_28_1 :
    integerResidualCheck 71 28 1 (dualNumerators071 28 1) ∧
    integerMassCheck 71 28 1 (dualNumerators071 28 1) := by
  apply integerChecks_of_simple 71 28 1 (dualNumerators071 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 426731607120, 507685338329, 2156352207, 100492021777, 362407121329, 426731607121, 0, 0, 64175975503, 79745886859]) (branchResiduals071 28 1) 10335557
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck071_29_0 :
    integerResidualCheck 71 29 0 (dualNumerators071 29 0) ∧
    integerMassCheck 71 29 0 (dualNumerators071 29 0) := by
  apply integerChecks_of_simple 71 29 0 (dualNumerators071 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0]) (branchResiduals071 29 0) 40352153
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck071_29_1 :
    integerResidualCheck 71 29 1 (dualNumerators071 29 1) ∧
    integerMassCheck 71 29 1 (dualNumerators071 29 1) := by
  apply integerChecks_of_simple 71 29 1 (dualNumerators071 29 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 160334187224, 1881575790198, 25837005087, 1204076434982, 1564110399358, 160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals071 29 1) 40352153
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck071_30_0 :
    integerResidualCheck 71 30 0 (dualNumerators071 30 0) ∧
    integerMassCheck 71 30 0 (dualNumerators071 30 0) := by
  apply integerChecks_of_simple 71 30 0 (dualNumerators071 30 0)
    (![49325597255, 9080703511, 49325597255, 0, 0, 3298611714, 3905876838, 0, 69158736213, 49325597255, 3298611714, 0, 15075840703, 81890664738, 3905876838, 0, 0, 81890664738, 166125241653, 1140296965504, 76448090321, 5112407761, 76448090321, 90521968404, 3298611714, 0, 15075840703, 81890664738, 0, 0, 5112407761, 126919597181, 9711601556, 117207995625, 1351620770, 75096469552, 97475206242, 9711601556, 5112407761, 0, 107186807798, 0]) (branchResiduals071 30 0) 7680628
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck071_30_1 :
    integerResidualCheck 71 30 1 (dualNumerators071 30 1) ∧
    integerMassCheck 71 30 1 (dualNumerators071 30 1) := by
  apply integerChecks_of_simple 71 30 1 (dualNumerators071 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 59587751998, 845061872643, 0, 544901951702, 704411721639, 59587751998, 893898125793, 34752663293, 281282522283, 482716951355]) (branchResiduals071 30 1) 7680628
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck071_31_0 :
    integerResidualCheck 71 31 0 (dualNumerators071 31 0) ∧
    integerMassCheck 71 31 0 (dualNumerators071 31 0) := by
  apply integerChecks_of_simple 71 31 0 (dualNumerators071 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 1032415642125, 1, 592902192609, 0, 1222480453651, 0, 500720887661, 0, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642125, 0, 592902192609, 0, 0, 0, 1600106408231, 776050524992, 0, 776050524992, 820904449873, 751938125788, 655394283555, 1, 732639129519, 867467278713, 655394283556, 0]) (branchResiduals071 31 0) 32891612
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck071_31_1 :
    integerResidualCheck 71 31 1 (dualNumerators071 31 1) ∧
    integerMassCheck 71 31 1 (dualNumerators071 31 1) := by
  apply integerChecks_of_simple 71 31 1 (dualNumerators071 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 556963843680, 992902647048, 725570984152, 37986262977, 327950144489, 1221916346239]) (branchResiduals071 31 1) 32891612
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck071_32_0 :
    integerResidualCheck 71 32 0 (dualNumerators071 32 0) ∧
    integerMassCheck 71 32 0 (dualNumerators071 32 0) := by
  apply integerChecks_of_simple 71 32 0 (dualNumerators071 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 0, 2743468108582, 2028778803022, 0, 505064750776, 2743468108580, 1713354977902, 2, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 2028778803022, 0, 0, 0, 4252009289869, 2655471466972, 174911447372, 2480560019601, 0, 1599482877825, 2067701325315, 174911447373, 4074076396250, 177932893619, 0, 2242612772688]) (branchResiduals071 32 0) 67647473
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck071_32_1 :
    integerResidualCheck 71 32 1 (dualNumerators071 32 1) ∧
    integerMassCheck 71 32 1 (dualNumerators071 32 1) := by
  apply integerChecks_of_simple 71 32 1 (dualNumerators071 32 1)
    (![830518849052, 152896180641, 830518849053, 0, 1, 55540314888, 65765130409, 0, 1164458966499, 830518849051, 55540314888, 0, 253839194360, 1378832582089, 65765130409, 0, 0, 1378832582090, 2797130742946, 2362247611782, 1287193334063, 86080072929, 1287193334063, 1524162000997, 55540314888, 0, 253839194360, 1378832582089, 0, 0, 86080072929, 2137006415304, 163518915030, 1973487500274, 22757890183, 1264435443881, 1641237016970, 163518915031, 86080072929, 0, 1804755932001, 0]) (branchResiduals071 32 1) 67647473
    branchSparseDots071 branchIntegerCurvature071 branchDots071
    branchIntegerCurvature071_entry rfl
    (congrFun (congrFun branchResiduals071_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks071 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 71 j s (dualNumerators071 j s) ∧
    integerMassCheck 71 j s (dualNumerators071 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck071_0_0
    · exact integerCheck071_0_1
  · fin_cases s
    · exact integerCheck071_1_0
    · exact integerCheck071_1_1
  · fin_cases s
    · exact integerCheck071_2_0
    · exact integerCheck071_2_1
  · fin_cases s
    · exact integerCheck071_3_0
    · exact integerCheck071_3_1
  · fin_cases s
    · exact integerCheck071_4_0
    · exact integerCheck071_4_1
  · fin_cases s
    · exact integerCheck071_5_0
    · exact integerCheck071_5_1
  · fin_cases s
    · exact integerCheck071_6_0
    · exact integerCheck071_6_1
  · fin_cases s
    · exact integerCheck071_7_0
    · exact integerCheck071_7_1
  · fin_cases s
    · exact integerCheck071_8_0
    · exact integerCheck071_8_1
  · fin_cases s
    · exact integerCheck071_9_0
    · exact integerCheck071_9_1
  · fin_cases s
    · exact integerCheck071_10_0
    · exact integerCheck071_10_1
  · fin_cases s
    · exact integerCheck071_11_0
    · exact integerCheck071_11_1
  · fin_cases s
    · exact integerCheck071_12_0
    · exact integerCheck071_12_1
  · fin_cases s
    · exact integerCheck071_13_0
    · exact integerCheck071_13_1
  · fin_cases s
    · exact integerCheck071_14_0
    · exact integerCheck071_14_1
  · fin_cases s
    · exact integerCheck071_15_0
    · exact integerCheck071_15_1
  · fin_cases s
    · exact integerCheck071_16_0
    · exact integerCheck071_16_1
  · fin_cases s
    · exact integerCheck071_17_0
    · exact integerCheck071_17_1
  · fin_cases s
    · exact integerCheck071_18_0
    · exact integerCheck071_18_1
  · fin_cases s
    · exact integerCheck071_19_0
    · exact integerCheck071_19_1
  · fin_cases s
    · exact integerCheck071_20_0
    · exact integerCheck071_20_1
  · fin_cases s
    · exact integerCheck071_21_0
    · exact integerCheck071_21_1
  · fin_cases s
    · exact integerCheck071_22_0
    · exact integerCheck071_22_1
  · fin_cases s
    · exact integerCheck071_23_0
    · exact integerCheck071_23_1
  · fin_cases s
    · exact integerCheck071_24_0
    · exact integerCheck071_24_1
  · fin_cases s
    · exact integerCheck071_25_0
    · exact integerCheck071_25_1
  · fin_cases s
    · exact integerCheck071_26_0
    · exact integerCheck071_26_1
  · fin_cases s
    · exact integerCheck071_27_0
    · exact integerCheck071_27_1
  · fin_cases s
    · exact integerCheck071_28_0
    · exact integerCheck071_28_1
  · fin_cases s
    · exact integerCheck071_29_0
    · exact integerCheck071_29_1
  · fin_cases s
    · exact integerCheck071_30_0
    · exact integerCheck071_30_1
  · fin_cases s
    · exact integerCheck071_31_0
    · exact integerCheck071_31_1
  · fin_cases s
    · exact integerCheck071_32_0
    · exact integerCheck071_32_1

end ElevenSquare.Tasks.T06
