import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual087
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
import ElevenSquare.Tasks.T06.SparseColumn47
import ElevenSquare.Tasks.T06.SparseColumn49
import ElevenSquare.Tasks.T06.SparseColumn55
import ElevenSquare.Tasks.T06.SparseColumn56

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix087 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix087_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = branchIntegerMatrix087 := by
  change roundedGradients ∘ branchRows 87 = branchIntegerMatrix087
  rw [show branchRows 87 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 54, 55, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix087]

theorem branchColumn087_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 0) i) = _
  rw [branchColumn087_0]
  exact sparseColumn00_sum n

theorem branchColumn087_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 1) i) = _
  rw [branchColumn087_1]
  exact sparseColumn01_sum n

theorem branchColumn087_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 2) i) = _
  rw [branchColumn087_2]
  exact sparseColumn02_sum n

theorem branchColumn087_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 3) i) = _
  rw [branchColumn087_3]
  exact sparseColumn03_sum n

theorem branchColumn087_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 4) i) = _
  rw [branchColumn087_4]
  exact sparseColumn04_sum n

theorem branchColumn087_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 5) i) = _
  rw [branchColumn087_5]
  exact sparseColumn05_sum n

theorem branchColumn087_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 6) i) = _
  rw [branchColumn087_6]
  exact sparseColumn06_sum n

theorem branchColumn087_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 7) i) = _
  rw [branchColumn087_7]
  exact sparseColumn07_sum n

theorem branchColumn087_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 8) i) = _
  rw [branchColumn087_8]
  exact sparseColumn08_sum n

theorem branchColumn087_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 9) i) = _
  rw [branchColumn087_9]
  exact sparseColumn09_sum n

theorem branchColumn087_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 10) i) = _
  rw [branchColumn087_10]
  exact sparseColumn10_sum n

theorem branchColumn087_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 11) i) = _
  rw [branchColumn087_11]
  exact sparseColumn11_sum n

theorem branchColumn087_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 12) i) = _
  rw [branchColumn087_12]
  exact sparseColumn35_sum n

theorem branchColumn087_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 13) i) = _
  rw [branchColumn087_13]
  exact sparseColumn36_sum n

theorem branchColumn087_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 14) i) = _
  rw [branchColumn087_14]
  exact sparseColumn41_sum n

theorem branchColumn087_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 15) i) = _
  rw [branchColumn087_15]
  exact sparseColumn38_sum n

theorem branchColumn087_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 16) i) = _
  rw [branchColumn087_16]
  exact sparseColumn39_sum n

theorem branchColumn087_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 17) i) = _
  rw [branchColumn087_17]
  exact sparseColumn17_sum n

theorem branchColumn087_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 18) i) = _
  rw [branchColumn087_18]
  exact sparseColumn18_sum n

theorem branchColumn087_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 19) i) = _
  rw [branchColumn087_19]
  exact sparseColumn19_sum n

theorem branchColumn087_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 20) = sparseColumn55 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 20) = sparseDot55 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 20) i) = _
  rw [branchColumn087_20]
  exact sparseColumn55_sum n

theorem branchColumn087_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 21) i) = _
  rw [branchColumn087_21]
  exact sparseColumn21_sum n

theorem branchColumn087_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 22) i) = _
  rw [branchColumn087_22]
  exact sparseColumn22_sum n

theorem branchColumn087_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 23) = sparseColumn47 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 23) = sparseDot47 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 23) i) = _
  rw [branchColumn087_23]
  exact sparseColumn47_sum n

theorem branchColumn087_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 24) i) = _
  rw [branchColumn087_24]
  exact sparseColumn24_sum n

theorem branchColumn087_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 25) i) = _
  rw [branchColumn087_25]
  exact sparseColumn25_sum n

theorem branchColumn087_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 26) = sparseColumn56 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 26) = sparseDot56 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 26) i) = _
  rw [branchColumn087_26]
  exact sparseColumn56_sum n

theorem branchColumn087_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 27) i) = _
  rw [branchColumn087_27]
  exact sparseColumn27_sum n

theorem branchColumn087_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 28) i) = _
  rw [branchColumn087_28]
  exact sparseColumn28_sum n

theorem branchColumn087_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 29) = sparseColumn49 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 29) = sparseDot49 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 29) i) = _
  rw [branchColumn087_29]
  exact sparseColumn49_sum n

theorem branchColumn087_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 30) i) = _
  rw [branchColumn087_30]
  exact sparseColumn30_sum n

theorem branchColumn087_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 31) i) = _
  rw [branchColumn087_31]
  exact sparseColumn31_sum n

theorem branchColumn087_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 87 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 87 i)) = _
  rw [branchIntegerMatrix087_eq]
  simp only [branchIntegerMatrix087, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot087_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 87 i) 32) i) = _
  rw [branchColumn087_32]
  exact sparseColumn43_sum n

def branchSparseDots087 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot55, sparseDot21, sparseDot22, sparseDot47, sparseDot24, sparseDot25, sparseDot56, sparseDot27, sparseDot28, sparseDot49, sparseDot30, sparseDot31, sparseDot43]

/-- Keep the finite case proof independent of the large arithmetic expressions. -/
private theorem branchDots087_cases (P : Fin 33 → Prop)
    (h0 : P 0)
    (h1 : P 1)
    (h2 : P 2)
    (h3 : P 3)
    (h4 : P 4)
    (h5 : P 5)
    (h6 : P 6)
    (h7 : P 7)
    (h8 : P 8)
    (h9 : P 9)
    (h10 : P 10)
    (h11 : P 11)
    (h12 : P 12)
    (h13 : P 13)
    (h14 : P 14)
    (h15 : P 15)
    (h16 : P 16)
    (h17 : P 17)
    (h18 : P 18)
    (h19 : P 19)
    (h20 : P 20)
    (h21 : P 21)
    (h22 : P 22)
    (h23 : P 23)
    (h24 : P 24)
    (h25 : P 25)
    (h26 : P 26)
    (h27 : P 27)
    (h28 : P 28)
    (h29 : P 29)
    (h30 : P 30)
    (h31 : P 31)
    (h32 : P 32)
    (k : Fin 33) : P k := by
  revert k
  refine Fin.cases h0 ?_
  refine Fin.cases h1 ?_
  refine Fin.cases h2 ?_
  refine Fin.cases h3 ?_
  refine Fin.cases h4 ?_
  refine Fin.cases h5 ?_
  refine Fin.cases h6 ?_
  refine Fin.cases h7 ?_
  refine Fin.cases h8 ?_
  refine Fin.cases h9 ?_
  refine Fin.cases h10 ?_
  refine Fin.cases h11 ?_
  refine Fin.cases h12 ?_
  refine Fin.cases h13 ?_
  refine Fin.cases h14 ?_
  refine Fin.cases h15 ?_
  refine Fin.cases h16 ?_
  refine Fin.cases h17 ?_
  refine Fin.cases h18 ?_
  refine Fin.cases h19 ?_
  refine Fin.cases h20 ?_
  refine Fin.cases h21 ?_
  refine Fin.cases h22 ?_
  refine Fin.cases h23 ?_
  refine Fin.cases h24 ?_
  refine Fin.cases h25 ?_
  refine Fin.cases h26 ?_
  refine Fin.cases h27 ?_
  refine Fin.cases h28 ?_
  refine Fin.cases h29 ?_
  refine Fin.cases h30 ?_
  refine Fin.cases h31 ?_
  refine Fin.cases h32 ?_
  intro i
  exact Fin.elim0 i

theorem branchDots087 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) k) = branchSparseDots087 k n := by
  exact branchDots087_cases
    (fun j => (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 87 i) j) =
      branchSparseDots087 j n)
    (branchDot087_0 n) (branchDot087_1 n) (branchDot087_2 n)
    (branchDot087_3 n) (branchDot087_4 n) (branchDot087_5 n)
    (branchDot087_6 n) (branchDot087_7 n) (branchDot087_8 n)
    (branchDot087_9 n) (branchDot087_10 n) (branchDot087_11 n)
    (branchDot087_12 n) (branchDot087_13 n) (branchDot087_14 n)
    (branchDot087_15 n) (branchDot087_16 n) (branchDot087_17 n)
    (branchDot087_18 n) (branchDot087_19 n) (branchDot087_20 n)
    (branchDot087_21 n) (branchDot087_22 n) (branchDot087_23 n)
    (branchDot087_24 n) (branchDot087_25 n) (branchDot087_26 n)
    (branchDot087_27 n) (branchDot087_28 n) (branchDot087_29 n)
    (branchDot087_30 n) (branchDot087_31 n) (branchDot087_32 n)
    k

def branchIntegerCurvature087 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101981296, 101981296, 79086693, 79086693, 106371291, 106371291, 48290998, 48290998, 289103692, 289103692]

theorem branchIntegerCurvature087_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 87 i)) = branchIntegerCurvature087 := by
  change curvatureNumerators ∘ branchRows 87 = branchIntegerCurvature087
  rw [show branchRows 87 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 54, 55, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature087_entry (i : Fin 42) :
    curvatureNumerators (branchRows 87 i) = branchIntegerCurvature087 i :=
  congrFun branchIntegerCurvature087_eq i

def branchResiduals087 : Fin 33 → Fin 2 → ℕ := ![![1301452954943346, 33000000000000], ![1546923810827226, 33000000000000], ![1584292301458661, 1336526049516882], ![33000000000000, 1023208217410656], ![860572074281336, 33000000000000], ![1053883511438614, 893869431298363], ![719547090372426, 624777238175104], ![33000000000000, 763944526475052], ![1579159678879425, 1129675608102811], ![1025926177105843, 33000000000000], ![33000000000000, 776990022433660], ![507229054866348, 463509294755407], ![990524489671341, 66000000000000], ![33000000000000, 862998091124416], ![1053843773642214, 489881844151573], ![471801868736130, 33000000000000], ![66000000000000, 743479019228235], ![663468262244906, 462448637518321], ![622795825683979, 269417921297689], ![629223857852173, 510626792386973], ![1476959482758784, 851858990529808], ![750873121411385, 374549059863808], ![471034922606877, 90602725914513], ![1476959482758784, 851858990529808], ![669000005539485, 230313982650212], ![505936894074485, 218713669397988], ![396136216194598, 851858990529808], ![407377540739132, 546417668864042], ![283888335003034, 298620828727661], ![396136216194598, 888751663165629], ![93513265731919, 553148660826509], ![966617222949435, 648577798406985], ![2021340894768456, 920353462619134]]

theorem branchResiduals087_eq : residualNumerators 87 = branchResiduals087 := rfl

theorem integerCheck087_0_0 :
    integerResidualCheck 87 0 0 (dualNumerators087 0 0) ∧
    integerMassCheck 87 0 0 (dualNumerators087 0 0) := by
  apply integerChecks_of_simple 87 0 0 (dualNumerators087 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 217988955954, 1955057368113, 74854042823, 1234047382517, 1835192545884, 0, 1821798773483, 145214820501, 818327875519, 1016864670366]) (branchResiduals087 0 0) 18767167
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck087_0_1 :
    integerResidualCheck 87 0 1 (dualNumerators087 0 1) ∧
    integerMassCheck 87 0 1 (dualNumerators087 0 1) := by
  apply integerChecks_of_simple 87 0 1 (dualNumerators087 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals087 0 1) 18767167
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck087_1_0 :
    integerResidualCheck 87 1 0 (dualNumerators087 1 0) ∧
    integerMassCheck 87 1 0 (dualNumerators087 1 0) := by
  apply integerChecks_of_simple 87 1 0 (dualNumerators087 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 258120108696, 2314977922424, 88634461252, 1461232029476, 2173046324067, 0, 2157186795895, 171948459903, 968979732271, 1204066591796]) (branchResiduals087 1 0) 22176635
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck087_1_1 :
    integerResidualCheck 87 1 1 (dualNumerators087 1 1) ∧
    integerMassCheck 87 1 1 (dualNumerators087 1 1) := by
  apply integerChecks_of_simple 87 1 1 (dualNumerators087 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals087 1 1) 22176635
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck087_2_0 :
    integerResidualCheck 87 2 0 (dualNumerators087 2 0) ∧
    integerMassCheck 87 2 0 (dualNumerators087 2 0) := by
  apply integerChecks_of_simple 87 2 0 (dualNumerators087 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 258120108697, 2314977922426, 88634461252, 1461232029477, 2173046324068, 0, 2157186795897, 171948459903, 968979732272, 1204066591797]) (branchResiduals087 2 0) 22681452
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck087_2_1 :
    integerResidualCheck 87 2 1 (dualNumerators087 2 1) ∧
    integerMassCheck 87 2 1 (dualNumerators087 2 1) := by
  apply integerChecks_of_simple 87 2 1 (dualNumerators087 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 217988955954, 1955057368112, 74854042823, 1234047382516, 1835192545883, 0, 1821798773482, 145214820501, 818327875518, 1016864670365]) (branchResiduals087 2 1) 22681452
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck087_3_0 :
    integerResidualCheck 87 3 0 (dualNumerators087 3 0) ∧
    integerMassCheck 87 3 0 (dualNumerators087 3 0) := by
  apply integerChecks_of_simple 87 3 0 (dualNumerators087 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals087 3 0) 16360330
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck087_3_1 :
    integerResidualCheck 87 3 1 (dualNumerators087 3 1) ∧
    integerMassCheck 87 3 1 (dualNumerators087 3 1) := by
  apply integerChecks_of_simple 87 3 1 (dualNumerators087 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000000, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 171759757642, 1540445837058, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 644784030255, 801216871619]) (branchResiduals087 3 1) 16360330
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck087_4_0 :
    integerResidualCheck 87 4 0 (dualNumerators087 4 0) ∧
    integerMassCheck 87 4 0 (dualNumerators087 4 0) := by
  apply integerChecks_of_simple 87 4 0 (dualNumerators087 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 145055456673, 1300945445202, 49809804896, 821166860693, 1221184310279, 0, 1212271749715, 96629675624, 544536410901, 676647899379]) (branchResiduals087 4 0) 13760362
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck087_4_1 :
    integerResidualCheck 87 4 1 (dualNumerators087 4 1) ∧
    integerMassCheck 87 4 1 (dualNumerators087 4 1) := by
  apply integerChecks_of_simple 87 4 1 (dualNumerators087 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals087 4 1) 13760362
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck087_5_0 :
    integerResidualCheck 87 5 0 (dualNumerators087 5 0) ∧
    integerMassCheck 87 5 0 (dualNumerators087 5 0) := by
  apply integerChecks_of_simple 87 5 0 (dualNumerators087 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 171759757642, 1540445837059, 58979649669, 972341366620, 1446000901875, 0, 1435447564017, 114418926712, 644784030255, 801216871620]) (branchResiduals087 5 0) 17641130
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck087_5_1 :
    integerResidualCheck 87 5 1 (dualNumerators087 5 1) ∧
    integerMassCheck 87 5 1 (dualNumerators087 5 1) := by
  apply integerChecks_of_simple 87 5 1 (dualNumerators087 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 145055456672, 1300945445201, 49809804896, 821166860692, 1221184310279, 0, 1212271749715, 96629675624, 544536410901, 676647899378]) (branchResiduals087 5 1) 17641130
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck087_6_0 :
    integerResidualCheck 87 6 0 (dualNumerators087 6 0) ∧
    integerMassCheck 87 6 0 (dualNumerators087 6 0) := by
  apply integerChecks_of_simple 87 6 0 (dualNumerators087 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 877488274356, 957704271528, 103906894360, 5439901403, 818327875519, 1016864670366]) (branchResiduals087 6 0) 8962451
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck087_6_1 :
    integerResidualCheck 87 6 1 (dualNumerators087 6 1) ∧
    integerMassCheck 87 6 1 (dualNumerators087 6 1) := by
  apply integerChecks_of_simple 87 6 1 (dualNumerators087 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 760187607595, 1097479190627, 0, 0]) (branchResiduals087 6 1) 8962451
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck087_7_0 :
    integerResidualCheck 87 7 0 (dualNumerators087 7 0) ∧
    integerMassCheck 87 7 0 (dualNumerators087 7 0) := by
  apply integerChecks_of_simple 87 7 0 (dualNumerators087 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals087 7 0) 10424794
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck087_7_1 :
    integerResidualCheck 87 7 1 (dualNumerators087 7 1) ∧
    integerMassCheck 87 7 1 (dualNumerators087 7 1) := by
  apply integerChecks_of_simple 87 7 1 (dualNumerators087 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 129060054349, 1157488961214, 44317230626, 730616014740, 1086523162035, 0, 1078593397950, 85974229952, 484489866137, 602033295899]) (branchResiduals087 7 1) 10424794
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck087_8_0 :
    integerResidualCheck 87 8 0 (dualNumerators087 8 0) ∧
    integerMassCheck 87 8 0 (dualNumerators087 8 0) := by
  apply integerChecks_of_simple 87 8 0 (dualNumerators087 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 258120108697, 2314977922428, 88634461252, 1461232029479, 2173046324070, 0, 2157186795899, 171948459903, 968979732273, 1204066591798]) (branchResiduals087 8 0) 22681452
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck087_8_1 :
    integerResidualCheck 87 8 1 (dualNumerators087 8 1) ∧
    integerMassCheck 87 8 1 (dualNumerators087 8 1) := by
  apply integerChecks_of_simple 87 8 1 (dualNumerators087 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 184097183121, 1651095362762, 63216131150, 1042184205913, 1549866490725, 0, 1538555111396, 122637586316, 691098574663, 858767916063]) (branchResiduals087 8 1) 22681452
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck087_9_0 :
    integerResidualCheck 87 9 0 (dualNumerators087 9 0) ∧
    integerMassCheck 87 9 0 (dualNumerators087 9 0) := by
  apply integerChecks_of_simple 87 9 0 (dualNumerators087 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 171759757642, 1540445837058, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 644784030255, 801216871619]) (branchResiduals087 9 0) 16350530
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck087_9_1 :
    integerResidualCheck 87 9 1 (dualNumerators087 9 1) ∧
    integerMassCheck 87 9 1 (dualNumerators087 9 1) := by
  apply integerChecks_of_simple 87 9 1 (dualNumerators087 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals087 9 1) 16350530
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck087_10_0 :
    integerResidualCheck 87 10 0 (dualNumerators087 10 0) ∧
    integerMassCheck 87 10 0 (dualNumerators087 10 0) := by
  apply integerChecks_of_simple 87 10 0 (dualNumerators087 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals087 10 0) 10683139
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck087_10_1 :
    integerResidualCheck 87 10 1 (dualNumerators087 10 1) ∧
    integerMassCheck 87 10 1 (dualNumerators087 10 1) := by
  apply integerChecks_of_simple 87 10 1 (dualNumerators087 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 131302334422, 1177599090918, 45087194994, 743309684668, 1105400337064, 0, 1097332801829, 87467940020, 492907358117, 612492978948]) (branchResiduals087 10 1) 10683139
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck087_11_0 :
    integerResidualCheck 87 11 0 (dualNumerators087 11 0) ∧
    integerMassCheck 87 11 0 (dualNumerators087 11 0) := by
  apply integerChecks_of_simple 87 11 0 (dualNumerators087 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 81606011717, 731892282302, 28022244838, 461976088268, 687019871017, 0, 682005798892, 54362397817, 306347970271, 380671900746]) (branchResiduals087 11 0) 15120968
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck087_11_1 :
    integerResidualCheck 87 11 1 (dualNumerators087 11 1) ∧
    integerMassCheck 87 11 1 (dualNumerators087 11 1) := by
  apply integerChecks_of_simple 87 11 1 (dualNumerators087 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 74415302107, 667401630730, 25553066146, 421269088530, 626483149703, 0, 621910892291, 49572257873, 279354134309, 347129015395]) (branchResiduals087 11 1) 15120968
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck087_12_0 :
    integerResidualCheck 87 12 0 (dualNumerators087 12 0) ∧
    integerMassCheck 87 12 0 (dualNumerators087 12 0) := by
  apply integerChecks_of_simple 87 12 0 (dualNumerators087 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 171759757642, 1540445837058, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 644784030255, 801216871619]) (branchResiduals087 12 0) 16348076
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck087_12_1 :
    integerResidualCheck 87 12 1 (dualNumerators087 12 1) ∧
    integerMassCheck 87 12 1 (dualNumerators087 12 1) := by
  apply integerChecks_of_simple 87 12 1 (dualNumerators087 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals087 12 1) 16348076
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck087_13_0 :
    integerResidualCheck 87 13 0 (dualNumerators087 13 0) ∧
    integerMassCheck 87 13 0 (dualNumerators087 13 0) := by
  apply integerChecks_of_simple 87 13 0 (dualNumerators087 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals087 13 0) 13962901
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck087_13_1 :
    integerResidualCheck 87 13 1 (dualNumerators087 13 1) ∧
    integerMassCheck 87 13 1 (dualNumerators087 13 1) := by
  apply integerChecks_of_simple 87 13 1 (dualNumerators087 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 145055456673, 1300945445202, 49809804896, 821166860693, 1221184310279, 0, 1212271749715, 96629675624, 544536410901, 676647899379]) (branchResiduals087 13 1) 13962901
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck087_14_0 :
    integerResidualCheck 87 14 0 (dualNumerators087 14 0) ∧
    integerMassCheck 87 14 0 (dualNumerators087 14 0) := by
  apply integerChecks_of_simple 87 14 0 (dualNumerators087 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 171759757642, 1540445837059, 58979649669, 972341366620, 1446000901875, 0, 1435447564017, 114418926712, 644784030255, 801216871620]) (branchResiduals087 14 0) 20161291
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck087_14_1 :
    integerResidualCheck 87 14 1 (dualNumerators087 14 1) ∧
    integerMassCheck 87 14 1 (dualNumerators087 14 1) := by
  apply integerChecks_of_simple 87 14 1 (dualNumerators087 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 78641078323, 705300958658, 27004132474, 445191438428, 662058864893, 0, 657226965498, 52387287341, 295217646558, 366841218336]) (branchResiduals087 14 1) 20161291
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck087_15_0 :
    integerResidualCheck 87 15 0 (dualNumerators087 15 0) ∧
    integerMassCheck 87 15 0 (dualNumerators087 15 0) := by
  apply integerChecks_of_simple 87 15 0 (dualNumerators087 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 81606011717, 731892282302, 28022244838, 461976088267, 687019871016, 0, 682005798892, 54362397817, 306347970271, 380671900746]) (branchResiduals087 15 0) 12900283
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck087_15_1 :
    integerResidualCheck 87 15 1 (dualNumerators087 15 1) ∧
    integerMassCheck 87 15 1 (dualNumerators087 15 1) := by
  apply integerChecks_of_simple 87 15 1 (dualNumerators087 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals087 15 1) 12900283
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck087_16_0 :
    integerResidualCheck 87 16 0 (dualNumerators087 16 0) ∧
    integerMassCheck 87 16 0 (dualNumerators087 16 0) := by
  apply integerChecks_of_simple 87 16 0 (dualNumerators087 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals087 16 0) 10683060
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck087_16_1 :
    integerResidualCheck 87 16 1 (dualNumerators087 16 1) ∧
    integerMassCheck 87 16 1 (dualNumerators087 16 1) := by
  apply integerChecks_of_simple 87 16 1 (dualNumerators087 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 131302334422, 1177599090918, 45087194994, 743309684668, 1105400337064, 0, 1097332801829, 87467940020, 492907358117, 612492978948]) (branchResiduals087 16 1) 10683060
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck087_17_0 :
    integerResidualCheck 87 17 0 (dualNumerators087 17 0) ∧
    integerMassCheck 87 17 0 (dualNumerators087 17 0) := by
  apply integerChecks_of_simple 87 17 0 (dualNumerators087 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 107032501981, 959932491577, 36753309138, 605916838014, 901078905318, 0, 894502567701, 71300426643, 401798703857, 499280201462]) (branchResiduals087 17 0) 15120968
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck087_17_1 :
    integerResidualCheck 87 17 1 (dualNumerators087 17 1) ∧
    integerMassCheck 87 17 1 (dualNumerators087 17 1) := by
  apply integerChecks_of_simple 87 17 1 (dualNumerators087 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 74415302107, 667401630730, 25553066146, 421269088530, 626483149703, 0, 621910892291, 49572257873, 279354134309, 347129015395]) (branchResiduals087 17 1) 15120968
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck087_18_0 :
    integerResidualCheck 87 18 0 (dualNumerators087 18 0) ∧
    integerMassCheck 87 18 0 (dualNumerators087 18 0) := by
  apply integerChecks_of_simple 87 18 0 (dualNumerators087 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 170971222814, 1097425476614, 0, 763999473637, 1027460955744, 43732116505, 953519106044, 33030453619, 477654049462, 593539022787]) (branchResiduals087 18 0) 13565580
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck087_18_1 :
    integerResidualCheck 87 18 1 (dualNumerators087 18 1) ∧
    integerMassCheck 87 18 1 (dualNumerators087 18 1) := by
  apply integerChecks_of_simple 87 18 1 (dualNumerators087 18 1)
    (![552774353318, 101764201348, 552774353318, 0, 1, 194169418432, 229915461414, 0, 83885421775, 59829007246, 194169418432, 0, 94926637302, 515633295911, 229915461414, 0, 0, 515633295912, 201500008915, 170171850577, 856726447141, 300936675152, 92726973504, 109797748126, 194169418432, 0, 94926637302, 515633295911, 0, 0, 300936675152, 799162766836, 15443069854, 138502830895, 92726973504, 0, 130011204269, 0, 195186313540, 105750361613, 57973095424, 72038108846]) (branchResiduals087 18 1) 13565580
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck087_19_0 :
    integerResidualCheck 87 19 0 (dualNumerators087 19 0) ∧
    integerMassCheck 87 19 0 (dualNumerators087 19 0) := by
  apply integerChecks_of_simple 87 19 0 (dualNumerators087 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 230658067063, 840535005185, 0, 645216866088, 781448198910, 123201425731, 653752451905, 19962510160, 403390917798, 501258706842]) (branchResiduals087 19 0) 8248658
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck087_19_1 :
    integerResidualCheck 87 19 1 (dualNumerators087 19 1) ∧
    integerMassCheck 87 19 1 (dualNumerators087 19 1) := by
  apply integerChecks_of_simple 87 19 1 (dualNumerators087 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 76640541789, 687358931849, 186417556881, 273765914097, 645216866088, 0, 761601233763, 225876501886, 287707656866, 357509209222]) (branchResiduals087 19 1) 8248658
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck087_20_0 :
    integerResidualCheck 87 20 0 (dualNumerators087 20 0) ∧
    integerMassCheck 87 20 0 (dualNumerators087 20 0) := by
  apply integerChecks_of_simple 87 20 0 (dualNumerators087 20 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 176645531640, 1584264425996, 1060657349048, 0, 1487132967409, 0, 2232638358246, 1209625354629, 663125166110, 824007801299]) (branchResiduals087 20 0) 35312013
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck087_20_1 :
    integerResidualCheck 87 20 1 (dualNumerators087 20 1) ∧
    integerMassCheck 87 20 1 (dualNumerators087 20 1) := by
  apply integerChecks_of_simple 87 20 1 (dualNumerators087 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals087 20 1) 35312013
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck087_21_0 :
    integerResidualCheck 87 21 0 (dualNumerators087 21 0) ∧
    integerMassCheck 87 21 0 (dualNumerators087 21 0) := by
  apply integerChecks_of_simple 87 21 0 (dualNumerators087 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 759767979803, 549133445537, 851509250277, 798941670661, 583650214286, 725251211053]) (branchResiduals087 21 0) 11182451
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck087_21_1 :
    integerResidualCheck 87 21 1 (dualNumerators087 21 1) ∧
    integerMassCheck 87 21 1 (dualNumerators087 21 1) := by
  apply integerChecks_of_simple 87 21 1 (dualNumerators087 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 860003851037, 963321782180, 3460174706, 161253783489, 102979506989, 127963650709, 0, 0, 102979506989, 127963650709]) (branchResiduals087 21 1) 11182451
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck087_22_0 :
    integerResidualCheck 87 22 0 (dualNumerators087 22 0) ∧
    integerMassCheck 87 22 0 (dualNumerators087 22 0) := by
  apply integerChecks_of_simple 87 22 0 (dualNumerators087 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 510506833659, 253492639979, 460183470977, 0, 270741877993, 374474988096, 310954038967, 490382041752, 287707656866, 357509209222]) (branchResiduals087 22 0) 6465674
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck087_22_1 :
    integerResidualCheck 87 22 1 (dualNumerators087 22 1) ∧
    integerMassCheck 87 22 1 (dualNumerators087 22 1) := by
  apply integerChecks_of_simple 87 22 1 (dualNumerators087 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 9522456419, 111749239332, 1534493418, 71511669319, 45668611868, 56748400418, 0, 0, 45668611868, 56748400418]) (branchResiduals087 22 1) 6465674
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck087_23_0 :
    integerResidualCheck 87 23 0 (dualNumerators087 23 0) ∧
    integerMassCheck 87 23 0 (dualNumerators087 23 0) := by
  apply integerChecks_of_simple 87 23 0 (dualNumerators087 23 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 1176645531640, 584264425996, 1060657349048, 0, 1487132967409, 0, 2232638358246, 1209625354629, 663125166110, 824007801299]) (branchResiduals087 23 0) 35297932
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck087_23_1 :
    integerResidualCheck 87 23 1 (dualNumerators087 23 1) ∧
    integerMassCheck 87 23 1 (dualNumerators087 23 1) := by
  apply integerChecks_of_simple 87 23 1 (dualNumerators087 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 160334187224, 1881575790198, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals087 23 1) 35297932
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck087_24_0 :
    integerResidualCheck 87 24 0 (dualNumerators087 24 0) ∧
    integerMassCheck 87 24 0 (dualNumerators087 24 0) := by
  apply integerChecks_of_simple 87 24 0 (dualNumerators087 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 512185690040, 559007382209, 569308312247, 737522866658, 477654049462, 593539022787]) (branchResiduals087 24 0) 9356857
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck087_24_1 :
    integerResidualCheck 87 24 1 (dualNumerators087 24 1) ∧
    integerMassCheck 87 24 1 (dualNumerators087 24 1) := by
  apply integerChecks_of_simple 87 24 1 (dualNumerators087 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 690777049383, 178822020994, 66021086067, 82038644814, 0, 0, 66021086067, 82038644814]) (branchResiduals087 24 1) 9356857
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck087_25_0 :
    integerResidualCheck 87 25 0 (dualNumerators087 25 0) ∧
    integerMassCheck 87 25 0 (dualNumerators087 25 0) := by
  apply integerChecks_of_simple 87 25 0 (dualNumerators087 25 0)
    (![34423495944, 6337268637, 34423495944, 0, 1, 22181646803, 26265225496, 0, 631959902239, 450728300227, 515126992874, 0, 137760279295, 748301940085, 609960421212, 0, 0, 748301940086, 1518022121617, 1282008050738, 53351822857, 34378591088, 698568688945, 827173216796, 515126992874, 0, 137760279295, 748301940085, 0, 0, 798378064725, 1159768101884, 638738616250, 521029485635, 53351822857, 0, 457056897559, 522396578403, 34378591088, 0, 436746587681, 542706888281]) (branchResiduals087 25 0) 8671199
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck087_25_1 :
    integerResidualCheck 87 25 1 (dualNumerators087 25 1) ∧
    integerMassCheck 87 25 1 (dualNumerators087 25 1) := by
  apply integerChecks_of_simple 87 25 1 (dualNumerators087 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 415529968297, 599898615461, 0, 0]) (branchResiduals087 25 1) 8671199
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck087_26_0 :
    integerResidualCheck 87 26 0 (dualNumerators087 26 0) ∧
    integerMassCheck 87 26 0 (dualNumerators087 26 0) := by
  apply integerChecks_of_simple 87 26 0 (dualNumerators087 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0]) (branchResiduals087 26 0) 15099566
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck087_26_1 :
    integerResidualCheck 87 26 1 (dualNumerators087 26 1) ∧
    integerMassCheck 87 26 1 (dualNumerators087 26 1) := by
  apply integerChecks_of_simple 87 26 1 (dualNumerators087 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 1025837005087, 204076434982, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals087 26 1) 15099566
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck087_27_0 :
    integerResidualCheck 87 27 0 (dualNumerators087 27 0) ∧
    integerMassCheck 87 27 0 (dualNumerators087 27 0) := by
  apply integerChecks_of_simple 87 27 0 (dualNumerators087 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 286173900105, 455299762271, 340673826058, 423325647580]) (branchResiduals087 27 0) 7338775
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck087_27_1 :
    integerResidualCheck 87 27 1 (dualNumerators087 27 1) ∧
    integerMassCheck 87 27 1 (dualNumerators087 27 1) := by
  apply integerChecks_of_simple 87 27 1 (dualNumerators087 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 530765167249, 1001172773960, 0, 377837583379, 916671368281, 377088943834, 621055226706, 24161639382, 236224837801, 293536000677]) (branchResiduals087 27 1) 7338775
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck087_28_0 :
    integerResidualCheck 87 28 0 (dualNumerators087 28 0) ∧
    integerMassCheck 87 28 0 (dualNumerators087 28 0) := by
  apply integerChecks_of_simple 87 28 0 (dualNumerators087 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 450383711774, 395438493575, 287707656866, 357509209222]) (branchResiduals087 28 0) 10335557
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck087_28_1 :
    integerResidualCheck 87 28 1 (dualNumerators087 28 1) ∧
    integerMassCheck 87 28 1 (dualNumerators087 28 1) := by
  apply integerChecks_of_simple 87 28 1 (dualNumerators087 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 426731607120, 507685338329, 2156352207, 100492021777, 456143077212, 332995651238, 0, 0, 64175975503, 79745886859]) (branchResiduals087 28 1) 10335557
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck087_29_0 :
    integerResidualCheck 87 29 0 (dualNumerators087 29 0) ∧
    integerMassCheck 87 29 0 (dualNumerators087 29 0) := by
  apply integerChecks_of_simple 87 29 0 (dualNumerators087 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0]) (branchResiduals087 29 0) 40352153
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck087_29_1 :
    integerResidualCheck 87 29 1 (dualNumerators087 29 1) ∧
    integerMassCheck 87 29 1 (dualNumerators087 29 1) := by
  apply integerChecks_of_simple 87 29 1 (dualNumerators087 29 1)
    (![814189538844, 149890000629, 814189538844, 0, 1, 31000670773, 36707806937, 0, 1141563866996, 814189538843, 31000670773, 0, 248848315523, 1351722559260, 36707806937, 0, 0, 1351722559261, 2742134741776, 2315802098733, 1261885083355, 48046900821, 1261885083355, 1494194572624, 31000670773, 0, 248848315523, 1351722559260, 0, 0, 48046900821, 2094989499358, 210158692266, 1884830807092, 72165251132, 1189719832223, 1769271584479, 0, 0, 48046900821, 788933161367, 980338423112]) (branchResiduals087 29 1) 40352153
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck087_30_0 :
    integerResidualCheck 87 30 0 (dualNumerators087 30 0) ∧
    integerMassCheck 87 30 0 (dualNumerators087 30 0) := by
  apply integerChecks_of_simple 87 30 0 (dualNumerators087 30 0)
    (![49325597255, 9080703511, 49325597255, 0, 0, 3298611714, 3905876838, 0, 69158736213, 49325597255, 3298611714, 0, 15075840703, 81890664738, 3905876838, 0, 0, 81890664738, 166125241653, 1140296965504, 76448090321, 5112407761, 76448090321, 90521968404, 3298611714, 0, 15075840703, 81890664738, 0, 0, 5112407761, 126919597181, 12731928525, 114187668656, 4371947739, 72076142582, 107186807798, 0, 2092080791, 3020326970, 107186807798, 0]) (branchResiduals087 30 0) 7680628
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck087_30_1 :
    integerResidualCheck 87 30 1 (dualNumerators087 30 1) ∧
    integerMassCheck 87 30 1 (dualNumerators087 30 1) := by
  apply integerChecks_of_simple 87 30 1 (dualNumerators087 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 90749849645, 813899774996, 31162097647, 513739854055, 763999473637, 0, 862736028146, 65914760940, 281282522283, 482716951355]) (branchResiduals087 30 1) 7680628
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck087_31_0 :
    integerResidualCheck 87 31 0 (dualNumerators087 31 0) ∧
    integerMassCheck 87 31 0 (dualNumerators087 31 0) := by
  apply integerChecks_of_simple 87 31 0 (dualNumerators087 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 1032415642125, 1, 592902192609, 0, 1222480453651, 0, 500720887661, 0, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642125, 0, 592902192609, 0, 0, 0, 1600106408231, 776050524992, 77849441973, 698201083019, 898753891846, 674088683815, 655394283556, 0, 654789687546, 945316720686, 655394283556, 0]) (branchResiduals087 31 0) 32891612
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck087_31_1 :
    integerResidualCheck 87 31 1 (dualNumerators087 31 1) ∧
    integerMassCheck 87 31 1 (dualNumerators087 31 1) := by
  apply integerChecks_of_simple 87 31 1 (dualNumerators087 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 741061026801, 808805463926, 725570984152, 37986262977, 327950144489, 1221916346239]) (branchResiduals087 31 1) 32891612
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck087_32_0 :
    integerResidualCheck 87 32 0 (dualNumerators087 32 0) ∧
    integerMassCheck 87 32 0 (dualNumerators087 32 0) := by
  apply integerChecks_of_simple 87 32 0 (dualNumerators087 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 0, 2743468108582, 2028778803022, 0, 505064750776, 2743468108580, 1713354977902, 2, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 2028778803022, 0, 0, 0, 4252009289869, 2655471466972, 266383392861, 2389088074111, 91471945490, 1508010932335, 2242612772688, 0, 3982604450761, 269404839109, 0, 2242612772688]) (branchResiduals087 32 0) 67647473
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck087_32_1 :
    integerResidualCheck 87 32 1 (dualNumerators087 32 1) ∧
    integerMassCheck 87 32 1 (dualNumerators087 32 1) := by
  apply integerChecks_of_simple 87 32 1 (dualNumerators087 32 1)
    (![830518849052, 152896180641, 830518849053, 0, 1, 55540314888, 65765130409, 0, 1164458966499, 830518849051, 55540314888, 0, 253839194360, 1378832582089, 65765130409, 0, 0, 1378832582090, 2797130742946, 2362247611782, 1287193334063, 86080072929, 1287193334063, 1524162000997, 55540314888, 0, 253839194360, 1378832582089, 0, 0, 86080072929, 2137006415304, 214373615592, 1922632799713, 73612590745, 1213580743319, 1804755932001, 0, 35225372368, 50854700562, 1804755932001, 0]) (branchResiduals087 32 1) 67647473
    branchSparseDots087 branchIntegerCurvature087 branchDots087
    branchIntegerCurvature087_entry rfl
    (congrFun (congrFun branchResiduals087_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks087 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 87 j s (dualNumerators087 j s) ∧
    integerMassCheck 87 j s (dualNumerators087 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck087_0_0
    · exact integerCheck087_0_1
  · fin_cases s
    · exact integerCheck087_1_0
    · exact integerCheck087_1_1
  · fin_cases s
    · exact integerCheck087_2_0
    · exact integerCheck087_2_1
  · fin_cases s
    · exact integerCheck087_3_0
    · exact integerCheck087_3_1
  · fin_cases s
    · exact integerCheck087_4_0
    · exact integerCheck087_4_1
  · fin_cases s
    · exact integerCheck087_5_0
    · exact integerCheck087_5_1
  · fin_cases s
    · exact integerCheck087_6_0
    · exact integerCheck087_6_1
  · fin_cases s
    · exact integerCheck087_7_0
    · exact integerCheck087_7_1
  · fin_cases s
    · exact integerCheck087_8_0
    · exact integerCheck087_8_1
  · fin_cases s
    · exact integerCheck087_9_0
    · exact integerCheck087_9_1
  · fin_cases s
    · exact integerCheck087_10_0
    · exact integerCheck087_10_1
  · fin_cases s
    · exact integerCheck087_11_0
    · exact integerCheck087_11_1
  · fin_cases s
    · exact integerCheck087_12_0
    · exact integerCheck087_12_1
  · fin_cases s
    · exact integerCheck087_13_0
    · exact integerCheck087_13_1
  · fin_cases s
    · exact integerCheck087_14_0
    · exact integerCheck087_14_1
  · fin_cases s
    · exact integerCheck087_15_0
    · exact integerCheck087_15_1
  · fin_cases s
    · exact integerCheck087_16_0
    · exact integerCheck087_16_1
  · fin_cases s
    · exact integerCheck087_17_0
    · exact integerCheck087_17_1
  · fin_cases s
    · exact integerCheck087_18_0
    · exact integerCheck087_18_1
  · fin_cases s
    · exact integerCheck087_19_0
    · exact integerCheck087_19_1
  · fin_cases s
    · exact integerCheck087_20_0
    · exact integerCheck087_20_1
  · fin_cases s
    · exact integerCheck087_21_0
    · exact integerCheck087_21_1
  · fin_cases s
    · exact integerCheck087_22_0
    · exact integerCheck087_22_1
  · fin_cases s
    · exact integerCheck087_23_0
    · exact integerCheck087_23_1
  · fin_cases s
    · exact integerCheck087_24_0
    · exact integerCheck087_24_1
  · fin_cases s
    · exact integerCheck087_25_0
    · exact integerCheck087_25_1
  · fin_cases s
    · exact integerCheck087_26_0
    · exact integerCheck087_26_1
  · fin_cases s
    · exact integerCheck087_27_0
    · exact integerCheck087_27_1
  · fin_cases s
    · exact integerCheck087_28_0
    · exact integerCheck087_28_1
  · fin_cases s
    · exact integerCheck087_29_0
    · exact integerCheck087_29_1
  · fin_cases s
    · exact integerCheck087_30_0
    · exact integerCheck087_30_1
  · fin_cases s
    · exact integerCheck087_31_0
    · exact integerCheck087_31_1
  · fin_cases s
    · exact integerCheck087_32_0
    · exact integerCheck087_32_1

end ElevenSquare.Tasks.T06
