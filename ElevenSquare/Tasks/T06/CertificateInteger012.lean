import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual012
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
import ElevenSquare.Tasks.T06.SparseColumn12
import ElevenSquare.Tasks.T06.SparseColumn13
import ElevenSquare.Tasks.T06.SparseColumn14
import ElevenSquare.Tasks.T06.SparseColumn15
import ElevenSquare.Tasks.T06.SparseColumn16
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
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn44
import ElevenSquare.Tasks.T06.SparseColumn46

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix012 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral28, roundedGradientLiteral29, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral36, roundedGradientLiteral37, roundedGradientLiteral48, roundedGradientLiteral49, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix012_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = branchIntegerMatrix012 := by
  change roundedGradients ∘ branchRows 12 = branchIntegerMatrix012
  rw [show branchRows 12 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral28_eq, roundedGradientLiteral29_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral36_eq, roundedGradientLiteral37_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral48_eq, roundedGradientLiteral49_eq, branchIntegerMatrix012]

theorem branchColumn012_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 0) i) = _
  rw [branchColumn012_0]
  exact sparseColumn00_sum n

theorem branchColumn012_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 1) i) = _
  rw [branchColumn012_1]
  exact sparseColumn01_sum n

theorem branchColumn012_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 2) i) = _
  rw [branchColumn012_2]
  exact sparseColumn02_sum n

theorem branchColumn012_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 3) i) = _
  rw [branchColumn012_3]
  exact sparseColumn03_sum n

theorem branchColumn012_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 4) i) = _
  rw [branchColumn012_4]
  exact sparseColumn04_sum n

theorem branchColumn012_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 5) i) = _
  rw [branchColumn012_5]
  exact sparseColumn05_sum n

theorem branchColumn012_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 6) i) = _
  rw [branchColumn012_6]
  exact sparseColumn06_sum n

theorem branchColumn012_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 7) i) = _
  rw [branchColumn012_7]
  exact sparseColumn07_sum n

theorem branchColumn012_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 8) i) = _
  rw [branchColumn012_8]
  exact sparseColumn08_sum n

theorem branchColumn012_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 9) i) = _
  rw [branchColumn012_9]
  exact sparseColumn09_sum n

theorem branchColumn012_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 10) i) = _
  rw [branchColumn012_10]
  exact sparseColumn10_sum n

theorem branchColumn012_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 11) i) = _
  rw [branchColumn012_11]
  exact sparseColumn11_sum n

theorem branchColumn012_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 12) = sparseColumn12 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 12) = sparseDot12 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 12) i) = _
  rw [branchColumn012_12]
  exact sparseColumn12_sum n

theorem branchColumn012_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 13) = sparseColumn13 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 13) = sparseDot13 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 13) i) = _
  rw [branchColumn012_13]
  exact sparseColumn13_sum n

theorem branchColumn012_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 14) = sparseColumn14 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 14) = sparseDot14 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 14) i) = _
  rw [branchColumn012_14]
  exact sparseColumn14_sum n

theorem branchColumn012_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 15) = sparseColumn15 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 15) = sparseDot15 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 15) i) = _
  rw [branchColumn012_15]
  exact sparseColumn15_sum n

theorem branchColumn012_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 16) = sparseColumn16 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 16) = sparseDot16 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 16) i) = _
  rw [branchColumn012_16]
  exact sparseColumn16_sum n

theorem branchColumn012_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 17) i) = _
  rw [branchColumn012_17]
  exact sparseColumn17_sum n

theorem branchColumn012_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 18) i) = _
  rw [branchColumn012_18]
  exact sparseColumn18_sum n

theorem branchColumn012_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 19) i) = _
  rw [branchColumn012_19]
  exact sparseColumn19_sum n

theorem branchColumn012_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 20) = sparseColumn20 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 20) = sparseDot20 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 20) i) = _
  rw [branchColumn012_20]
  exact sparseColumn20_sum n

theorem branchColumn012_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 21) i) = _
  rw [branchColumn012_21]
  exact sparseColumn21_sum n

theorem branchColumn012_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 22) i) = _
  rw [branchColumn012_22]
  exact sparseColumn22_sum n

theorem branchColumn012_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 23) = sparseColumn23 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 23) = sparseDot23 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 23) i) = _
  rw [branchColumn012_23]
  exact sparseColumn23_sum n

theorem branchColumn012_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 24) i) = _
  rw [branchColumn012_24]
  exact sparseColumn24_sum n

theorem branchColumn012_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 25) i) = _
  rw [branchColumn012_25]
  exact sparseColumn25_sum n

theorem branchColumn012_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 26) = sparseColumn44 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 26) = sparseDot44 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 26) i) = _
  rw [branchColumn012_26]
  exact sparseColumn44_sum n

theorem branchColumn012_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 27) i) = _
  rw [branchColumn012_27]
  exact sparseColumn27_sum n

theorem branchColumn012_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 28) i) = _
  rw [branchColumn012_28]
  exact sparseColumn28_sum n

theorem branchColumn012_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 29) = sparseColumn46 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 29) = sparseDot46 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 29) i) = _
  rw [branchColumn012_29]
  exact sparseColumn46_sum n

theorem branchColumn012_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 30) i) = _
  rw [branchColumn012_30]
  exact sparseColumn30_sum n

theorem branchColumn012_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 31) i) = _
  rw [branchColumn012_31]
  exact sparseColumn31_sum n

theorem branchColumn012_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 12 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 12 i)) = _
  rw [branchIntegerMatrix012_eq]
  simp only [branchIntegerMatrix012, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot012_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 12 i) 32) i) = _
  rw [branchColumn012_32]
  exact sparseColumn43_sum n

def branchSparseDots012 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot12, sparseDot13, sparseDot14, sparseDot15, sparseDot16, sparseDot17, sparseDot18, sparseDot19, sparseDot20, sparseDot21, sparseDot22, sparseDot23, sparseDot24, sparseDot25, sparseDot44, sparseDot27, sparseDot28, sparseDot46, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot012_0 :
    branchSparseDots012 0 = sparseDot00 := rfl

private theorem branchSparseDot012_1 :
    branchSparseDots012 1 = sparseDot01 := rfl

private theorem branchSparseDot012_2 :
    branchSparseDots012 2 = sparseDot02 := rfl

private theorem branchSparseDot012_3 :
    branchSparseDots012 3 = sparseDot03 := rfl

private theorem branchSparseDot012_4 :
    branchSparseDots012 4 = sparseDot04 := rfl

private theorem branchSparseDot012_5 :
    branchSparseDots012 5 = sparseDot05 := rfl

private theorem branchSparseDot012_6 :
    branchSparseDots012 6 = sparseDot06 := rfl

private theorem branchSparseDot012_7 :
    branchSparseDots012 7 = sparseDot07 := rfl

private theorem branchSparseDot012_8 :
    branchSparseDots012 8 = sparseDot08 := rfl

private theorem branchSparseDot012_9 :
    branchSparseDots012 9 = sparseDot09 := rfl

private theorem branchSparseDot012_10 :
    branchSparseDots012 10 = sparseDot10 := rfl

private theorem branchSparseDot012_11 :
    branchSparseDots012 11 = sparseDot11 := rfl

private theorem branchSparseDot012_12 :
    branchSparseDots012 12 = sparseDot12 := rfl

private theorem branchSparseDot012_13 :
    branchSparseDots012 13 = sparseDot13 := rfl

private theorem branchSparseDot012_14 :
    branchSparseDots012 14 = sparseDot14 := rfl

private theorem branchSparseDot012_15 :
    branchSparseDots012 15 = sparseDot15 := rfl

private theorem branchSparseDot012_16 :
    branchSparseDots012 16 = sparseDot16 := rfl

private theorem branchSparseDot012_17 :
    branchSparseDots012 17 = sparseDot17 := rfl

private theorem branchSparseDot012_18 :
    branchSparseDots012 18 = sparseDot18 := rfl

private theorem branchSparseDot012_19 :
    branchSparseDots012 19 = sparseDot19 := rfl

private theorem branchSparseDot012_20 :
    branchSparseDots012 20 = sparseDot20 := rfl

private theorem branchSparseDot012_21 :
    branchSparseDots012 21 = sparseDot21 := rfl

private theorem branchSparseDot012_22 :
    branchSparseDots012 22 = sparseDot22 := rfl

private theorem branchSparseDot012_23 :
    branchSparseDots012 23 = sparseDot23 := rfl

private theorem branchSparseDot012_24 :
    branchSparseDots012 24 = sparseDot24 := rfl

private theorem branchSparseDot012_25 :
    branchSparseDots012 25 = sparseDot25 := rfl

private theorem branchSparseDot012_26 :
    branchSparseDots012 26 = sparseDot44 := rfl

private theorem branchSparseDot012_27 :
    branchSparseDots012 27 = sparseDot27 := rfl

private theorem branchSparseDot012_28 :
    branchSparseDots012 28 = sparseDot28 := rfl

private theorem branchSparseDot012_29 :
    branchSparseDots012 29 = sparseDot46 := rfl

private theorem branchSparseDot012_30 :
    branchSparseDots012 30 = sparseDot30 := rfl

private theorem branchSparseDot012_31 :
    branchSparseDots012 31 = sparseDot31 := rfl

private theorem branchSparseDot012_32 :
    branchSparseDots012 32 = sparseDot43 := rfl

theorem branchDots012 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 12 i) k) = branchSparseDots012 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot012_0 n
      _ = _ := congrFun branchSparseDot012_0.symm n
  · calc
      _ = sparseDot01 n := branchDot012_1 n
      _ = _ := congrFun branchSparseDot012_1.symm n
  · calc
      _ = sparseDot02 n := branchDot012_2 n
      _ = _ := congrFun branchSparseDot012_2.symm n
  · calc
      _ = sparseDot03 n := branchDot012_3 n
      _ = _ := congrFun branchSparseDot012_3.symm n
  · calc
      _ = sparseDot04 n := branchDot012_4 n
      _ = _ := congrFun branchSparseDot012_4.symm n
  · calc
      _ = sparseDot05 n := branchDot012_5 n
      _ = _ := congrFun branchSparseDot012_5.symm n
  · calc
      _ = sparseDot06 n := branchDot012_6 n
      _ = _ := congrFun branchSparseDot012_6.symm n
  · calc
      _ = sparseDot07 n := branchDot012_7 n
      _ = _ := congrFun branchSparseDot012_7.symm n
  · calc
      _ = sparseDot08 n := branchDot012_8 n
      _ = _ := congrFun branchSparseDot012_8.symm n
  · calc
      _ = sparseDot09 n := branchDot012_9 n
      _ = _ := congrFun branchSparseDot012_9.symm n
  · calc
      _ = sparseDot10 n := branchDot012_10 n
      _ = _ := congrFun branchSparseDot012_10.symm n
  · calc
      _ = sparseDot11 n := branchDot012_11 n
      _ = _ := congrFun branchSparseDot012_11.symm n
  · calc
      _ = sparseDot12 n := branchDot012_12 n
      _ = _ := congrFun branchSparseDot012_12.symm n
  · calc
      _ = sparseDot13 n := branchDot012_13 n
      _ = _ := congrFun branchSparseDot012_13.symm n
  · calc
      _ = sparseDot14 n := branchDot012_14 n
      _ = _ := congrFun branchSparseDot012_14.symm n
  · calc
      _ = sparseDot15 n := branchDot012_15 n
      _ = _ := congrFun branchSparseDot012_15.symm n
  · calc
      _ = sparseDot16 n := branchDot012_16 n
      _ = _ := congrFun branchSparseDot012_16.symm n
  · calc
      _ = sparseDot17 n := branchDot012_17 n
      _ = _ := congrFun branchSparseDot012_17.symm n
  · calc
      _ = sparseDot18 n := branchDot012_18 n
      _ = _ := congrFun branchSparseDot012_18.symm n
  · calc
      _ = sparseDot19 n := branchDot012_19 n
      _ = _ := congrFun branchSparseDot012_19.symm n
  · calc
      _ = sparseDot20 n := branchDot012_20 n
      _ = _ := congrFun branchSparseDot012_20.symm n
  · calc
      _ = sparseDot21 n := branchDot012_21 n
      _ = _ := congrFun branchSparseDot012_21.symm n
  · calc
      _ = sparseDot22 n := branchDot012_22 n
      _ = _ := congrFun branchSparseDot012_22.symm n
  · calc
      _ = sparseDot23 n := branchDot012_23 n
      _ = _ := congrFun branchSparseDot012_23.symm n
  · calc
      _ = sparseDot24 n := branchDot012_24 n
      _ = _ := congrFun branchSparseDot012_24.symm n
  · calc
      _ = sparseDot25 n := branchDot012_25 n
      _ = _ := congrFun branchSparseDot012_25.symm n
  · calc
      _ = sparseDot44 n := branchDot012_26 n
      _ = _ := congrFun branchSparseDot012_26.symm n
  · calc
      _ = sparseDot27 n := branchDot012_27 n
      _ = _ := congrFun branchSparseDot012_27.symm n
  · calc
      _ = sparseDot28 n := branchDot012_28 n
      _ = _ := congrFun branchSparseDot012_28.symm n
  · calc
      _ = sparseDot46 n := branchDot012_29 n
      _ = _ := congrFun branchSparseDot012_29.symm n
  · calc
      _ = sparseDot30 n := branchDot012_30 n
      _ = _ := congrFun branchSparseDot012_30.symm n
  · calc
      _ = sparseDot31 n := branchDot012_31 n
      _ = _ := congrFun branchSparseDot012_31.symm n
  · calc
      _ = sparseDot43 n := branchDot012_32 n
      _ = _ := congrFun branchSparseDot012_32.symm n

def branchIntegerCurvature012 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101981296, 101981296, 44932602, 44932602, 115699695, 115699695, 88123140, 88123140, 289103692, 289103692]

theorem branchIntegerCurvature012_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 12 i)) = branchIntegerCurvature012 := by
  change curvatureNumerators ∘ branchRows 12 = branchIntegerCurvature012
  rw [show branchRows 12 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 48, 49, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature012_entry (i : Fin 42) :
    curvatureNumerators (branchRows 12 i) = branchIntegerCurvature012 i :=
  congrFun branchIntegerCurvature012_eq i

def branchResiduals012 : Fin 33 → Fin 2 → ℕ := ![![1300580532618599, 33000000000000], ![1545342476798598, 33000000000000], ![1582895989501194, 1337580526090041], ![33000000000000, 1023544006888705], ![857910985088990, 33000000000000], ![1054631262734472, 892499725526973], ![723975735294233, 622122527367398], ![33000000000000, 760278655633685], ![1580880611496080, 1129499627291951], ![1025202189527057, 33000000000000], ![33000000000000, 777891858653372], ![510633528145932, 466704601686204], ![989044006888705, 66000000000000], ![33000000000000, 416308890034192], ![316086737854369, 892499725526973], ![922664502487628, 33000000000000], ![66000000000000, 743986816007489], ![955177172348427, 810700129912935], ![622817537800452, 245883132922146], ![631138895246779, 510525028120531], ![1231613937096825, 950842030981077], ![754191434898769, 388586934288278], ![469158045035606, 105616699803590], ![1234336462785768, 950842030981077], ![672912287194709, 230571553353754], ![504597306550354, 223581994926723], ![398970616796057, 852626669416348], ![408760111432613, 550960205719430], ![285791123956719, 309420661383698], ![398970616796057, 950842030981077], ![105616699803590, 554690633861837], ![967408039697935, 651518154550049], ![2026642220335100, 950842030981077]]

theorem branchResiduals012_eq : residualNumerators 12 = branchResiduals012 := rfl

theorem integerCheck012_0_0 :
    integerResidualCheck 12 0 0 (dualNumerators012 0 0) ∧
    integerMassCheck 12 0 0 (dualNumerators012 0 0) := by
  apply integerChecks_of_simple 12 0 0 (dualNumerators012 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1011030237961, 258120108700, 0, 1660206247774, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1607511062796, 565535261271, 1308901425339, 0, 227681483087, 1607511062798, 1485808378804, 481205215181, 818327875519, 1016864670366]) (branchResiduals012 0 0) 18767167
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck012_0_1 :
    integerResidualCheck 12 0 1 (dualNumerators012 0 1) ∧
    integerMassCheck 12 0 1 (dualNumerators012 0 1) := by
  apply integerChecks_of_simple 12 0 1 (dualNumerators012 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals012 0 1) 18767167
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck012_1_0 :
    integerResidualCheck 12 1 0 (dualNumerators012 1 0) ∧
    integerMassCheck 12 1 0 (dualNumerators012 1 0) := by
  apply integerChecks_of_simple 12 1 0 (dualNumerators012 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1197158056821, 305639293618, 0, 1965845541389, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 1903449321293, 669648709827, 1549866490727, 0, 269597002772, 1903449321295, 1759341515999, 569793739799, 968979732271, 1204066591796]) (branchResiduals012 1 0) 22176635
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck012_1_1 :
    integerResidualCheck 12 1 1 (dualNumerators012 1 1) ∧
    integerMassCheck 12 1 1 (dualNumerators012 1 1) := by
  apply integerChecks_of_simple 12 1 1 (dualNumerators012 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals012 1 1) 22176635
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck012_2_0 :
    integerResidualCheck 12 2 0 (dualNumerators012 2 0) ∧
    integerMassCheck 12 2 0 (dualNumerators012 2 0) := by
  apply integerChecks_of_simple 12 2 0 (dualNumerators012 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1197158056822, 305639293619, 0, 1965845541391, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 1903449321295, 669648709827, 1549866490728, 0, 269597002773, 1903449321296, 1759341516001, 569793739799, 968979732272, 1204066591797]) (branchResiduals012 2 0) 22681452
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck012_2_1 :
    integerResidualCheck 12 2 1 (dualNumerators012 2 1) ∧
    integerMassCheck 12 2 1 (dualNumerators012 2 1) := by
  apply integerChecks_of_simple 12 2 1 (dualNumerators012 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1011030237961, 258120108700, 0, 1660206247773, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1607511062795, 565535261271, 1308901425338, 0, 227681483087, 1607511062796, 1485808378803, 481205215180, 818327875518, 1016864670365]) (branchResiduals012 2 1) 22681452
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck012_3_0 :
    integerResidualCheck 12 3 0 (dualNumerators012 3 0) ∧
    integerMassCheck 12 3 0 (dualNumerators012 3 0) := by
  apply integerChecks_of_simple 12 3 0 (dualNumerators012 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals012 3 0) 16360330
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck012_3_1 :
    integerResidualCheck 12 3 1 (dualNumerators012 3 1) ∧
    integerMassCheck 12 3 1 (dualNumerators012 3 1) := by
  apply integerChecks_of_simple 12 3 1 (dualNumerators012 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 796619754801, 203380245200, 0, 1308124173107, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals012 3 1) 16360330
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck012_4_0 :
    integerResidualCheck 12 4 0 (dualNumerators012 4 0) ∧
    integerMassCheck 12 4 0 (dualNumerators012 4 0) := by
  apply integerChecks_of_simple 12 4 0 (dualNumerators012 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 672765518030, 171759757645, 0, 1104743927909, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1069679196818, 376321705057, 870976665588, 0, 151505113461, 1069679196819, 988695101419, 320206323920, 544536410901, 676647899379]) (branchResiduals012 4 0) 13760362
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck012_4_1 :
    integerResidualCheck 12 4 1 (dualNumerators012 4 1) ∧
    integerMassCheck 12 4 1 (dualNumerators012 4 1) := by
  apply integerChecks_of_simple 12 4 1 (dualNumerators012 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals012 4 1) 13760362
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck012_5_0 :
    integerResidualCheck 12 5 0 (dualNumerators012 5 0) ∧
    integerMassCheck 12 5 0 (dualNumerators012 5 0) := by
  apply integerChecks_of_simple 12 5 0 (dualNumerators012 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 796619754801, 203380245201, 0, 1308124173108, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000000, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1266604123796, 445601470905, 1031321016288, 0, 179396778078, 1266604123797, 1170711084557, 379155406172, 644784030255, 801216871620]) (branchResiduals012 5 0) 17641130
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck012_5_1 :
    integerResidualCheck 12 5 1 (dualNumerators012 5 1) ∧
    integerMassCheck 12 5 1 (dualNumerators012 5 1) := by
  apply integerChecks_of_simple 12 5 1 (dualNumerators012 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1069679196817, 376321705056, 870976665588, 0, 151505113461, 1069679196818, 988695101418, 320206323920, 544536410901, 676647899378]) (branchResiduals012 5 1) 17641130
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck012_6_0 :
    integerResidualCheck 12 6 0 (dualNumerators012 6 0) ∧
    integerMassCheck 12 6 0 (dualNumerators012 6 0) := by
  apply integerChecks_of_simple 12 6 0 (dualNumerators012 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 0, 70552396879, 187567711821, 1472638535954, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 1, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 659499318402, 1175693227483, 2719950702, 106626845062, 818327875519, 1016864670366]) (branchResiduals012 6 0) 8962451
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck012_6_1 :
    integerResidualCheck 12 6 1 (dualNumerators012 6 1) ∧
    integerMassCheck 12 6 1 (dualNumerators012 6 1) := by
  apply integerChecks_of_simple 12 6 1 (dualNumerators012 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949782, 1, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 1051270592788, 806396205434, 0, 0]) (branchResiduals012 6 1) 8962451
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck012_7_0 :
    integerResidualCheck 12 7 0 (dualNumerators012 7 0) ∧
    integerMassCheck 12 7 0 (dualNumerators012 7 0) := by
  apply integerChecks_of_simple 12 7 0 (dualNumerators012 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals012 7 0) 10424794
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck012_7_1 :
    integerResidualCheck 12 7 1 (dualNumerators012 7 1) ∧
    integerMassCheck 12 7 1 (dualNumerators012 7 1) := by
  apply integerChecks_of_simple 12 7 1 (dualNumerators012 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 598579028412, 152819646809, 0, 982922770697, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 951724660649, 334824354914, 774933245365, 0, 134798501387, 951724660649, 879670758001, 284896869900, 484489866137, 602033295899]) (branchResiduals012 7 1) 10424794
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck012_8_0 :
    integerResidualCheck 12 8 0 (dualNumerators012 8 0) ∧
    integerMassCheck 12 8 0 (dualNumerators012 8 0) := by
  apply integerChecks_of_simple 12 8 0 (dualNumerators012 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1197158056824, 305639293618, 0, 1965845541393, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 1903449321297, 669648709828, 1549866490730, 0, 269597002773, 1903449321298, 1759341516002, 569793739800, 968979732273, 1204066591798]) (branchResiduals012 8 0) 22681452
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck012_8_1 :
    integerResidualCheck 12 8 1 (dualNumerators012 8 1) ∧
    integerMassCheck 12 8 1 (dualNumerators012 8 1) := by
  apply integerChecks_of_simple 12 8 1 (dualNumerators012 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1357583723455, 477608822428, 1105400337063, 0, 192282767270, 1357583723456, 1254802730706, 406389967006, 691098574663, 858767916063]) (branchResiduals012 8 1) 22681452
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck012_9_0 :
    integerResidualCheck 12 9 0 (dualNumerators012 9 0) ∧
    integerMassCheck 12 9 0 (dualNumerators012 9 0) := by
  apply integerChecks_of_simple 12 9 0 (dualNumerators012 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 887477428322, 296619754801, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 703380245200, 296619754801, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals012 9 0) 16350530
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck012_9_1 :
    integerResidualCheck 12 9 1 (dualNumerators012 9 1) ∧
    integerMassCheck 12 9 1 (dualNumerators012 9 1) := by
  apply integerChecks_of_simple 12 9 1 (dualNumerators012 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals012 9 1) 16350530
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck012_10_0 :
    integerResidualCheck 12 10 0 (dualNumerators012 10 0) ∧
    integerMassCheck 12 10 0 (dualNumerators012 10 0) := by
  apply integerChecks_of_simple 12 10 0 (dualNumerators012 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals012 10 0) 10683139
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck012_10_1 :
    integerResidualCheck 12 10 1 (dualNumerators012 10 1) ∧
    integerMassCheck 12 10 1 (dualNumerators012 10 1) := by
  apply integerChecks_of_simple 12 10 1 (dualNumerators012 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 560661867464, 344525275673, 0, 844525275674, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 419928145920, 344525275674, 155474724327, 844525275674, 0, 0, 1184800741849, 1308901425339, 968259856239, 340641569100, 788396879662, 0, 137140480825, 968259856240, 894954094286, 289846647564, 492907358117, 612492978948]) (branchResiduals012 10 1) 10683139
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck012_11_0 :
    integerResidualCheck 12 11 0 (dualNumerators012 11 0) ∧
    integerMassCheck 12 11 0 (dualNumerators012 11 0) := by
  apply integerChecks_of_simple 12 11 0 (dualNumerators012 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268434, 0, 562584914689, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 1, 0, 736368196709, 813498294019, 601785379685, 211712914335, 489998333105, 0, 85234491332, 601785379686, 556224949284, 180143247425, 306347970271, 380671900746]) (branchResiduals012 11 0) 15120968
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck012_11_1 :
    integerResidualCheck 12 11 1 (dualNumerators012 11 1) ∧
    integerMassCheck 12 11 1 (dualNumerators012 11 1) := by
  apply integerChecks_of_simple 12 11 1 (dualNumerators012 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 548759091280, 193057841557, 446822154676, 0, 77724058423, 548759091281, 507213215908, 164269934257, 279354134309, 347129015395]) (branchResiduals012 11 1) 15120968
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck012_12_0 :
    integerResidualCheck 12 12 0 (dualNumerators012 12 0) ∧
    integerMassCheck 12 12 0 (dualNumerators012 12 0) := by
  apply integerChecks_of_simple 12 12 0 (dualNumerators012 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1266604123795, 445601470905, 1031321016287, 0, 179396778078, 1266604123796, 1170711084556, 379155406172, 644784030255, 801216871619]) (branchResiduals012 12 0) 16348076
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck012_12_1 :
    integerResidualCheck 12 12 1 (dualNumerators012 12 1) ∧
    integerMassCheck 12 12 1 (dualNumerators012 12 1) := by
  apply integerChecks_of_simple 12 12 1 (dualNumerators012 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals012 12 1) 16348076
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck012_13_0 :
    integerResidualCheck 12 13 0 (dualNumerators012 13 0) ∧
    integerMassCheck 12 13 0 (dualNumerators012 13 0) := by
  apply integerChecks_of_simple 12 13 0 (dualNumerators012 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals012 13 0) 13962901
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck012_13_1 :
    integerResidualCheck 12 13 1 (dualNumerators012 13 1) ∧
    integerMassCheck 12 13 1 (dualNumerators012 13 1) := by
  apply integerChecks_of_simple 12 13 1 (dualNumerators012 13 1)
    (![280984417303, 51728439727, 280984417303, 0, 1, 422262637837, 500000000000, 0, 393964356797, 280984417303, 422262637837, 0, 0, 52371963954, 0, 0, 414120121179, 52371963954, 946336320750, 799204942162, 435488332794, 654450712669, 435488332794, 515660508144, 422262637837, 0, 0, 52371963954, 500000000001, 0, 654450712669, 723000450937, 534839598409, 188160852528, 435488332794, 0, 75752556731, 534839598409, 494347550709, 160103161960, 272268205451, 338323949689]) (branchResiduals012 13 1) 13962901
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck012_14_0 :
    integerResidualCheck 12 14 0 (dualNumerators012 14 0) ∧
    integerMassCheck 12 14 0 (dualNumerators012 14 0) := by
  apply integerChecks_of_simple 12 14 0 (dualNumerators012 14 0)
    (![194975514542, 35894443005, 194975514542, 0, 1, 293008686654, 346950760497, 0, 273372466399, 194975514542, 0, 293008686654, 0, 0, 730242506439, 0, 0, 323699567405, 656664212341, 554569524952, 302186016501, 454124344937, 302186016501, 357817610917, 0, 293008686654, 0, 0, 59592178538, 323699567405, 454124344937, 501691112584, 371126010824, 130565101761, 302186016501, 0, 52564814335, 371126010824, 343028517337, 111095827600, 188927321881, 234763503278]) (branchResiduals012 14 0) 20161291
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck012_14_1 :
    integerResidualCheck 12 14 1 (dualNumerators012 14 1) ∧
    integerMassCheck 12 14 1 (dualNumerators012 14 1) := by
  apply integerChecks_of_simple 12 14 1 (dualNumerators012 14 1)
    (![561968834605, 103456879454, 561968834605, 0, 1, 844525275673, 1000000000000, 0, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 0, 1000000000000, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1069679196817, 376321705056, 870976665588, 0, 151505113461, 1069679196818, 988695101418, 320206323920, 544536410901, 676647899378]) (branchResiduals012 14 1) 20161291
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck012_15_0 :
    integerResidualCheck 12 15 0 (dualNumerators012 15 0) ∧
    integerMassCheck 12 15 0 (dualNumerators012 15 0) := by
  apply integerChecks_of_simple 12 15 0 (dualNumerators012 15 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546385, 0, 844525275675, 602334801077, 221089960013, 684097183123, 0, 1184097183122, 1071829546385, 0, 0, 0, 2028622458796, 1713222941252, 933538524389, 1402919220983, 933538524389, 1105400337064, 905187143136, 1, 684097183123, 500000000000, 0, 0, 1402919220983, 1549866490727, 1146513768302, 403352722425, 933538524389, 0, 162387657036, 1146513768303, 1059712622067, 343206598917, 583650214286, 725251211053]) (branchResiduals012 15 0) 12900283
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck012_15_1 :
    integerResidualCheck 12 15 1 (dualNumerators012 15 1) ∧
    integerMassCheck 12 15 1 (dualNumerators012 15 1) := by
  apply integerChecks_of_simple 12 15 1 (dualNumerators012 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals012 15 1) 12900283
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck012_16_0 :
    integerResidualCheck 12 16 0 (dualNumerators012 16 0) ∧
    integerMassCheck 12 16 0 (dualNumerators012 16 0) := by
  apply integerChecks_of_simple 12 16 0 (dualNumerators012 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals012 16 0) 10683060
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck012_16_1 :
    integerResidualCheck 12 16 1 (dualNumerators012 16 1) ∧
    integerMassCheck 12 16 1 (dualNumerators012 16 1) := by
  apply integerChecks_of_simple 12 16 1 (dualNumerators012 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 0, 0, 0, 0, 1184800741849, 1308901425339, 968259856239, 340641569100, 788396879662, 0, 137140480825, 968259856240, 894954094286, 289846647564, 492907358117, 612492978948]) (branchResiduals012 16 1) 10683060
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck012_17_0 :
    integerResidualCheck 12 17 0 (dualNumerators012 17 0) ∧
    integerMassCheck 12 17 0 (dualNumerators012 17 0) := by
  apply integerChecks_of_simple 12 17 0 (dualNumerators012 17 0)
    (![602334801078, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546386, 0, 844525275676, 602334801077, 0, 905187143137, 278910039987, 905187143136, 1071829546386, 0, 0, 1000000000001, 2028622458797, 1713222941254, 933538524390, 1402919220984, 933538524390, 1105400337065, 905187143136, 1, 1184097183123, 0, 0, 0, 1402919220984, 1549866490728, 1146513768303, 403352722426, 933538524390, 0, 162387657036, 1146513768304, 1059712622068, 343206598917, 583650214286, 725251211054]) (branchResiduals012 17 0) 15120968
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck012_17_1 :
    integerResidualCheck 12 17 1 (dualNumerators012 17 1) ∧
    integerMassCheck 12 17 1 (dualNumerators012 17 1) := by
  apply integerChecks_of_simple 12 17 1 (dualNumerators012 17 1)
    (![508686963928, 93647837150, 508686963928, 0, 1, 764453421592, 905187143136, 0, 713222941253, 508686963927, 764453421593, 0, 0, 1000000000000, 905187143136, 0, 844525275674, 0, 1713222941251, 1446860076751, 788396879661, 1184800741848, 788396879661, 933538524388, 764453421592, 1, 0, 1000000000000, 0, 0, 1184800741848, 1308901425338, 968259856239, 340641569100, 788396879661, 0, 137140480824, 968259856239, 894954094285, 289846647563, 492907358117, 612492978947]) (branchResiduals012 17 1) 15120968
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck012_18_0 :
    integerResidualCheck 12 18 0 (dualNumerators012 18 0) ∧
    integerMassCheck 12 18 0 (dualNumerators012 18 0) := by
  apply integerChecks_of_simple 12 18 0 (dualNumerators012 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 562515489548, 74022925577, 0, 476109064652, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 1025720546095, 242676153333, 763999473637, 0, 45472526152, 1025720546096, 863239815324, 123309744339, 477654049462, 593539022787]) (branchResiduals012 18 0) 13565580
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck012_18_1 :
    integerResidualCheck 12 18 1 (dualNumerators012 18 1) ∧
    integerMassCheck 12 18 1 (dualNumerators012 18 1) := by
  apply integerChecks_of_simple 12 18 1 (dualNumerators012 18 1)
    (![538874628613, 99205301184, 538874628613, 0, 1, 173280948973, 205181483568, 0, 64396810428, 45929282541, 82602613712, 90678335261, 0, 583235221374, 205181483568, 0, 0, 492556886114, 154686685730, 130636815909, 835183729590, 268562336295, 71184255953, 84289076957, 173280948973, 1, 90678335261, 492556886113, 0, 0, 268562336295, 763397412564, 0, 118180546476, 71184255953, 0, 99806458592, 1, 84824690714, 183737645581, 44504543900, 55301914693]) (branchResiduals012 18 1) 13565580
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck012_19_0 :
    integerResidualCheck 12 19 0 (dualNumerators012 19 0) ∧
    integerMassCheck 12 19 0 (dualNumerators012 19 0) := by
  apply integerChecks_of_simple 12 19 0 (dualNumerators012 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 216703300504, 217988955956, 0, 1402086139076, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 901168865389, 170024206859, 593870256538, 51346609551, 3480759251, 901168865389, 673714962064, 0, 403390917798, 501258706842]) (branchResiduals012 19 0) 8248658
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck012_19_1 :
    integerResidualCheck 12 19 1 (dualNumerators012 19 1) ∧
    integerMassCheck 12 19 1 (dualNumerators012 19 1) := by
  apply integerChecks_of_simple 12 19 1 (dualNumerators012 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 1, 0, 0, 0, 0, 987477735649, 0, 405068248518, 358931225119, 460183470977, 0, 240148617570, 405068248519, 529741159093, 457736576556, 287707656866, 357509209222]) (branchResiduals012 19 1) 8248658
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck012_20_0 :
    integerResidualCheck 12 20 0 (dualNumerators012 20 0) ∧
    integerMassCheck 12 20 0 (dualNumerators012 20 0) := by
  apply integerChecks_of_simple 12 20 0 (dualNumerators012 20 0)
    (![525362030296, 96717669897, 525362030297, 0, 2, 1982073878105, 2346968095805, 0, 736602820676, 525362030296, 1821502598273, 160571279835, 0, 1032780604873, 2346968095805, 0, 0, 872209325041, 1769383425548, 1494289025233, 814241006257, 3071949885822, 814241006257, 964140481890, 1982073878105, 2, 160571279833, 872209325040, 0, 0, 3071949885822, 1351808005780, 0, 1351808005780, 814241006257, 0, 1141636028738, 1, 970267099056, 2101682786767, 509065159462, 632570869278]) (branchResiduals012 20 0) 35312013
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck012_20_1 :
    integerResidualCheck 12 20 1 (dualNumerators012 20 1) ∧
    integerMassCheck 12 20 1 (dualNumerators012 20 1) := by
  apply integerChecks_of_simple 12 20 1 (dualNumerators012 20 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 1300649428514, 887240892199, 0, 1317842481106, 547079247729, 1300649428515, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals012 20 1) 35312013
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck012_21_0 :
    integerResidualCheck 12 21 0 (dualNumerators012 21 0) ∧
    integerMassCheck 12 21 0 (dualNumerators012 21 0) := by
  apply integerChecks_of_simple 12 21 0 (dualNumerators012 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 604293255477, 704608169863, 757887471419, 892563449519, 583650214286, 725251211053]) (branchResiduals012 21 0) 11182451
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck012_21_1 :
    integerResidualCheck 12 21 1 (dualNumerators012 21 1) ∧
    integerMassCheck 12 21 1 (dualNumerators012 21 1) := by
  apply integerChecks_of_simple 12 21 1 (dualNumerators012 21 1)
    (![113874129702, 20963906509, 113874129702, 0, 1, 11418112698, 13520155082, 0, 159661338854, 113874129702, 0, 11418112698, 207483478989, 1200472654287, 13520155082, 0, 0, 1189054541591, 1567617472129, 323892577801, 176489697786, 17696550257, 176489697786, 208980953998, 11418112698, 0, 218901591686, 1189054541590, 0, 0, 17696550257, 1842875789658, 878795318822, 964080470836, 0, 176489697786, 73266609994, 174187148961, 17696550257, 0, 110341723711, 137112035244]) (branchResiduals012 21 1) 11182451
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck012_22_0 :
    integerResidualCheck 12 22 0 (dualNumerators012 22 0) ∧
    integerMassCheck 12 22 0 (dualNumerators012 22 0) := by
  apply integerChecks_of_simple 12 22 0 (dualNumerators012 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 583695195717, 0, 612220343874, 0, 492945346072, 1, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554683, 1, 583695195717, 0, 0, 0, 801336080718, 763999473637, 104985155316, 659014318321, 0, 460183470977, 599623014547, 45593851542, 64927501002, 736408579717, 287707656866, 357509209222]) (branchResiduals012 22 0) 6465674
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck012_22_1 :
    integerResidualCheck 12 22 1 (dualNumerators012 22 1) ∧
    integerMassCheck 12 22 1 (dualNumerators012 22 1) := by
  apply integerChecks_of_simple 12 22 1 (dualNumerators012 22 1)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 0, 5063622582, 10371186464, 88904172359, 5995821236, 0, 0, 83840549778, 1170080822236, 143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 17855961539, 112085697126, 0, 78268383123, 32491749791, 77247265314, 7847938961, 0, 48933554844, 60805460262]) (branchResiduals012 22 1) 6465674
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck012_23_0 :
    integerResidualCheck 12 23 0 (dualNumerators012 23 0) ∧
    integerMassCheck 12 23 0 (dualNumerators012 23 0) := by
  apply integerChecks_of_simple 12 23 0 (dualNumerators012 23 0)
    (![525362030296, 96717669897, 525362030296, 0, 2, 1982073878105, 2346968095804, 0, 736602820676, 525362030295, 1821502598274, 160571279833, 0, 1032780604872, 2346968095804, 0, 0, 872209325040, 1769383425546, 1494289025232, 814241006256, 3071949885821, 814241006256, 964140481889, 1982073878106, 0, 160571279833, 872209325039, 0, 0, 3071949885821, 1351808005779, 1000000000000, 351808005780, 814241006256, 0, 1141636028738, 0, 970267099055, 2101682786767, 509065159462, 632570869277]) (branchResiduals012 23 0) 35297932
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck012_23_1 :
    integerResidualCheck 12 23 1 (dualNumerators012 23 1) ∧
    integerMassCheck 12 23 1 (dualNumerators012 23 1) := by
  apply integerChecks_of_simple 12 23 1 (dualNumerators012 23 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 547079247729, 1300649428515, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals012 23 1) 35297932
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck012_24_0 :
    integerResidualCheck 12 24 0 (dualNumerators012 24 0) ∧
    integerMassCheck 12 24 0 (dualNumerators012 24 0) := by
  apply integerChecks_of_simple 12 24 0 (dualNumerators012 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 276221246109, 150663467366, 0, 969054410724, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 384946583730, 686246488518, 705016048726, 601815130180, 477654049462, 593539022787]) (branchResiduals012 24 0) 9356857
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck012_24_1 :
    integerResidualCheck 12 24 1 (dualNumerators012 24 1) ∧
    integerMassCheck 12 24 1 (dualNumerators012 24 1) := by
  apply integerChecks_of_simple 12 24 1 (dualNumerators012 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 395480180778, 20824623507, 0, 133942179966, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 587483804282, 282115266095, 48434165160, 99625565721, 0, 0, 66021086067, 82038644814]) (branchResiduals012 24 1) 9356857
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck012_25_0 :
    integerResidualCheck 12 25 0 (dualNumerators012 25 0) ∧
    integerMassCheck 12 25 0 (dualNumerators012 25 0) := by
  apply integerChecks_of_simple 12 25 0 (dualNumerators012 25 0)
    (![31307490826, 5763620872, 31307490826, 0, 1, 17498922567, 20720424919, 0, 627590994654, 447612295109, 373636362947, 136807905692, 0, 879936634611, 604415620636, 0, 0, 743128728921, 1507527629264, 1273145186690, 48522430940, 27120993710, 693739297027, 821454747430, 510444268639, 1, 136807905692, 743128728920, 0, 0, 791120467347, 1151750315250, 639144727059, 512605588192, 48522430940, 0, 333537525435, 639144727060, 0, 27120993710, 433727241876, 538955010618]) (branchResiduals012 25 0) 8671199
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck012_25_1 :
    integerResidualCheck 12 25 1 (dualNumerators012 25 1) ∧
    integerMassCheck 12 25 1 (dualNumerators012 25 1) := by
  apply integerChecks_of_simple 12 25 1 (dualNumerators012 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 0, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 574640301588, 440788282170, 0, 0]) (branchResiduals012 25 1) 8671199
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck012_26_0 :
    integerResidualCheck 12 26 0 (dualNumerators012 26 0) ∧
    integerMassCheck 12 26 0 (dualNumerators012 26 0) := by
  apply integerChecks_of_simple 12 26 0 (dualNumerators012 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1045975868227, 802334790777, 0, 0]) (branchResiduals012 26 0) 15099566
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck012_26_1 :
    integerResidualCheck 12 26 1 (dualNumerators012 26 1) ∧
    integerMassCheck 12 26 1 (dualNumerators012 26 1) := by
  apply integerChecks_of_simple 12 26 1 (dualNumerators012 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 879744679617, 350168760452, 564110399358, 1160334187225, 0, 0, 768944423926, 955500162657]) (branchResiduals012 26 1) 15099566
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck012_27_0 :
    integerResidualCheck 12 27 0 (dualNumerators012 27 0) ∧
    integerMassCheck 12 27 0 (dualNumerators012 27 0) := by
  apply integerChecks_of_simple 12 27 0 (dualNumerators012 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312724, 1, 0, 0, 0, 0, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 436855949686, 304617712691, 340673826058, 423325647580]) (branchResiduals012 27 0) 7338775
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck012_27_1 :
    integerResidualCheck 12 27 1 (dualNumerators012 27 1) ∧
    integerMassCheck 12 27 1 (dualNumerators012 27 1) := by
  apply integerChecks_of_simple 12 27 1 (dualNumerators012 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 234337221023, 181967583262, 0, 1170399780726, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 953483284011, 578454657198, 377837583379, 0, 340277028102, 953483284012, 430830286610, 214386579479, 236224837801, 293536000677]) (branchResiduals012 27 1) 7338775
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck012_28_0 :
    integerResidualCheck 12 28 0 (dualNumerators012 28 0) ∧
    integerMassCheck 12 28 0 (dualNumerators012 28 0) := by
  apply integerChecks_of_simple 12 28 0 (dualNumerators012 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 1, 0, 0, 0, 0, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 374399059503, 471423145846, 287707656866, 357509209222]) (branchResiduals012 28 0) 10335557
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck012_28_1 :
    integerResidualCheck 12 28 1 (dualNumerators012 28 1) ∧
    integerMassCheck 12 28 1 (dualNumerators012 28 1) := by
  apply integerChecks_of_simple 12 28 1 (dualNumerators012 28 1)
    (![70965414109, 13064532837, 70965414109, 0, 1, 500061019298, 592120844340, 0, 99499623476, 70965414109, 0, 7115673227, 105323995459, 617878243177, 8425648624, 0, 0, 610762569951, 1239006666393, 201847170824, 109986917328, 775027817129, 109986917328, 130235198988, 7115673227, 0, 112439668685, 610762569950, 0, 0, 11028343493, 946600440957, 438442294144, 508158146813, 0, 109986917328, 360985704208, 438442294145, 11028343493, 0, 68764047964, 85447084301]) (branchResiduals012 28 1) 10335557
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck012_29_0 :
    integerResidualCheck 12 29 0 (dualNumerators012 29 0) ∧
    integerMassCheck 12 29 0 (dualNumerators012 29 0) := by
  apply integerChecks_of_simple 12 29 0 (dualNumerators012 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 45975868227, 1802334790777, 0, 0]) (branchResiduals012 29 0) 40352153
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck012_29_1 :
    integerResidualCheck 12 29 1 (dualNumerators012 29 1) ∧
    integerMassCheck 12 29 1 (dualNumerators012 29 1) := by
  apply integerChecks_of_simple 12 29 1 (dualNumerators012 29 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 1547079247729, 300649428515, 132139529898, 0, 823917842058, 1023810834186]) (branchResiduals012 29 1) 40352153
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck012_30_0 :
    integerResidualCheck 12 30 0 (dualNumerators012 30 0) ∧
    integerMassCheck 12 30 0 (dualNumerators012 30 0) := by
  apply integerChecks_of_simple 12 30 0 (dualNumerators012 30 0)
    (![50500080873, 9296922637, 50500080873, 0, 0, 5063622582, 5995821236, 0, 70805463414, 50500080873, 0, 5063622582, 10371186464, 88904172359, 5995821236, 0, 0, 83840549778, 170080822236, 1143637553286, 78268383123, 7847938961, 78268383123, 92677371984, 5063622582, 0, 15434809046, 83840549778, 0, 0, 7847938961, 129941658664, 17855961539, 112085697126, 0, 78268383123, 91883053566, 17855961539, 7847938961, 0, 108324858619, 1414156487]) (branchResiduals012 30 0) 7680628
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck012_30_1 :
    integerResidualCheck 12 30 1 (dualNumerators012 30 1) ∧
    integerMassCheck 12 30 1 (dualNumerators012 30 1) := by
  apply integerChecks_of_simple 12 30 1 (dualNumerators012 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 491724510490, 107456641334, 0, 691151837050, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 669214578381, 235435046259, 544901951702, 0, 94784895256, 669214578382, 621279733097, 307371055990, 281282522283, 482716951355]) (branchResiduals012 30 1) 7680628
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck012_31_0 :
    integerResidualCheck 12 31 0 (dualNumerators012 31 0) ∧
    integerMassCheck 12 31 0 (dualNumerators012 31 0) := by
  apply integerChecks_of_simple 12 31 0 (dualNumerators012 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 940234337176, 92181304950, 0, 592902192609, 1222480453651, 0, 0, 500720887661, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642124, 1, 92181304949, 500720887660, 0, 0, 1600106408231, 776050524992, 0, 776050524992, 634078107472, 938764468189, 655394283555, 1, 827665375816, 772441032416, 655394283556, 0]) (branchResiduals012 31 0) 32891612
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck012_31_1 :
    integerResidualCheck 12 31 1 (dualNumerators012 31 1) ∧
    integerMassCheck 12 31 1 (dualNumerators012 31 1) := by
  apply integerChecks_of_simple 12 31 1 (dualNumerators012 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 274671058114, 217988955956, 0, 1402086139076, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 556963843680, 992902647048, 18993131489, 744564115640, 327950144489, 1221916346239]) (branchResiduals012 31 1) 32891612
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck012_32_0 :
    integerResidualCheck 12 32 0 (dualNumerators012 32 0) ∧
    integerMassCheck 12 32 0 (dualNumerators012 32 0) := by
  apply integerChecks_of_simple 12 32 0 (dualNumerators012 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 1713354977902, 1030113130681, 2028778803022, 0, 505064750776, 2743468108580, 0, 1713354977903, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 315423825121, 1713354977902, 0, 0, 4252009289869, 2655471466972, 364902194330, 2290569272643, 0, 1599482877825, 1877710578357, 364902194331, 262156886566, 3989852403304, 0, 2242612772688]) (branchResiduals012 32 0) 67647473
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck012_32_1 :
    integerResidualCheck 12 32 1 (dualNumerators012 32 1) ∧
    integerMassCheck 12 32 1 (dualNumerators012 32 1) := by
  apply integerChecks_of_simple 12 32 1 (dualNumerators012 32 1)
    (![850294195655, 156536766246, 850294195655, 0, 1, 85258653367, 100954531288, 0, 1192185705866, 850294195654, 0, 85258653367, 174624663961, 1496922389437, 100954531288, 0, 0, 1411663736072, 2863732759262, 2418494697972, 1317842481106, 132139529898, 1317842481106, 1560453569675, 85258653367, 1, 259883317327, 1411663736071, 0, 0, 132139529898, 2187890320712, 300649428514, 1887240892199, 0, 1317842481106, 1547079247729, 300649428515, 132139529898, 0, 1823917842058, 23810834186]) (branchResiduals012 32 1) 67647473
    branchSparseDots012 branchIntegerCurvature012 branchDots012
    branchIntegerCurvature012_entry rfl
    (congrFun (congrFun branchResiduals012_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks012 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 12 j s (dualNumerators012 j s) ∧
    integerMassCheck 12 j s (dualNumerators012 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck012_0_0
    · exact integerCheck012_0_1
  · fin_cases s
    · exact integerCheck012_1_0
    · exact integerCheck012_1_1
  · fin_cases s
    · exact integerCheck012_2_0
    · exact integerCheck012_2_1
  · fin_cases s
    · exact integerCheck012_3_0
    · exact integerCheck012_3_1
  · fin_cases s
    · exact integerCheck012_4_0
    · exact integerCheck012_4_1
  · fin_cases s
    · exact integerCheck012_5_0
    · exact integerCheck012_5_1
  · fin_cases s
    · exact integerCheck012_6_0
    · exact integerCheck012_6_1
  · fin_cases s
    · exact integerCheck012_7_0
    · exact integerCheck012_7_1
  · fin_cases s
    · exact integerCheck012_8_0
    · exact integerCheck012_8_1
  · fin_cases s
    · exact integerCheck012_9_0
    · exact integerCheck012_9_1
  · fin_cases s
    · exact integerCheck012_10_0
    · exact integerCheck012_10_1
  · fin_cases s
    · exact integerCheck012_11_0
    · exact integerCheck012_11_1
  · fin_cases s
    · exact integerCheck012_12_0
    · exact integerCheck012_12_1
  · fin_cases s
    · exact integerCheck012_13_0
    · exact integerCheck012_13_1
  · fin_cases s
    · exact integerCheck012_14_0
    · exact integerCheck012_14_1
  · fin_cases s
    · exact integerCheck012_15_0
    · exact integerCheck012_15_1
  · fin_cases s
    · exact integerCheck012_16_0
    · exact integerCheck012_16_1
  · fin_cases s
    · exact integerCheck012_17_0
    · exact integerCheck012_17_1
  · fin_cases s
    · exact integerCheck012_18_0
    · exact integerCheck012_18_1
  · fin_cases s
    · exact integerCheck012_19_0
    · exact integerCheck012_19_1
  · fin_cases s
    · exact integerCheck012_20_0
    · exact integerCheck012_20_1
  · fin_cases s
    · exact integerCheck012_21_0
    · exact integerCheck012_21_1
  · fin_cases s
    · exact integerCheck012_22_0
    · exact integerCheck012_22_1
  · fin_cases s
    · exact integerCheck012_23_0
    · exact integerCheck012_23_1
  · fin_cases s
    · exact integerCheck012_24_0
    · exact integerCheck012_24_1
  · fin_cases s
    · exact integerCheck012_25_0
    · exact integerCheck012_25_1
  · fin_cases s
    · exact integerCheck012_26_0
    · exact integerCheck012_26_1
  · fin_cases s
    · exact integerCheck012_27_0
    · exact integerCheck012_27_1
  · fin_cases s
    · exact integerCheck012_28_0
    · exact integerCheck012_28_1
  · fin_cases s
    · exact integerCheck012_29_0
    · exact integerCheck012_29_1
  · fin_cases s
    · exact integerCheck012_30_0
    · exact integerCheck012_30_1
  · fin_cases s
    · exact integerCheck012_31_0
    · exact integerCheck012_31_1
  · fin_cases s
    · exact integerCheck012_32_0
    · exact integerCheck012_32_1

end ElevenSquare.Tasks.T06
