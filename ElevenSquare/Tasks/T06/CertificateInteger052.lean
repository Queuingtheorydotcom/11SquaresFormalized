import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual052
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
import ElevenSquare.Tasks.T06.SparseColumn21
import ElevenSquare.Tasks.T06.SparseColumn22
import ElevenSquare.Tasks.T06.SparseColumn24
import ElevenSquare.Tasks.T06.SparseColumn25
import ElevenSquare.Tasks.T06.SparseColumn26
import ElevenSquare.Tasks.T06.SparseColumn27
import ElevenSquare.Tasks.T06.SparseColumn28
import ElevenSquare.Tasks.T06.SparseColumn30
import ElevenSquare.Tasks.T06.SparseColumn31
import ElevenSquare.Tasks.T06.SparseColumn43
import ElevenSquare.Tasks.T06.SparseColumn49
import ElevenSquare.Tasks.T06.SparseColumn52
import ElevenSquare.Tasks.T06.SparseColumn54

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix052 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral28, roundedGradientLiteral29, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral52, roundedGradientLiteral53, roundedGradientLiteral34, roundedGradientLiteral35, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral46, roundedGradientLiteral47]

theorem branchIntegerMatrix052_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = branchIntegerMatrix052 := by
  change roundedGradients ∘ branchRows 52 = branchIntegerMatrix052
  rw [show branchRows 52 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 34, 35, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral28_eq, roundedGradientLiteral29_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral34_eq, roundedGradientLiteral35_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral46_eq, roundedGradientLiteral47_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral52_eq, roundedGradientLiteral53_eq, branchIntegerMatrix052]

theorem branchColumn052_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 0) i) = _
  rw [branchColumn052_0]
  exact sparseColumn00_sum n

theorem branchColumn052_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 1) i) = _
  rw [branchColumn052_1]
  exact sparseColumn01_sum n

theorem branchColumn052_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 2) i) = _
  rw [branchColumn052_2]
  exact sparseColumn02_sum n

theorem branchColumn052_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 3) i) = _
  rw [branchColumn052_3]
  exact sparseColumn03_sum n

theorem branchColumn052_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 4) i) = _
  rw [branchColumn052_4]
  exact sparseColumn04_sum n

theorem branchColumn052_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 5) i) = _
  rw [branchColumn052_5]
  exact sparseColumn05_sum n

theorem branchColumn052_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 6) i) = _
  rw [branchColumn052_6]
  exact sparseColumn06_sum n

theorem branchColumn052_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 7) i) = _
  rw [branchColumn052_7]
  exact sparseColumn07_sum n

theorem branchColumn052_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 8) i) = _
  rw [branchColumn052_8]
  exact sparseColumn08_sum n

theorem branchColumn052_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 9) i) = _
  rw [branchColumn052_9]
  exact sparseColumn09_sum n

theorem branchColumn052_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 10) i) = _
  rw [branchColumn052_10]
  exact sparseColumn10_sum n

theorem branchColumn052_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 11) i) = _
  rw [branchColumn052_11]
  exact sparseColumn11_sum n

theorem branchColumn052_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 12) = sparseColumn12 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 12) = sparseDot12 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 12) i) = _
  rw [branchColumn052_12]
  exact sparseColumn12_sum n

theorem branchColumn052_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 13) = sparseColumn13 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 13) = sparseDot13 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 13) i) = _
  rw [branchColumn052_13]
  exact sparseColumn13_sum n

theorem branchColumn052_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 14) = sparseColumn14 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 14) = sparseDot14 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 14) i) = _
  rw [branchColumn052_14]
  exact sparseColumn14_sum n

theorem branchColumn052_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 15) = sparseColumn15 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 15) = sparseDot15 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 15) i) = _
  rw [branchColumn052_15]
  exact sparseColumn15_sum n

theorem branchColumn052_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 16) = sparseColumn16 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 16) = sparseDot16 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 16) i) = _
  rw [branchColumn052_16]
  exact sparseColumn16_sum n

theorem branchColumn052_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 17) i) = _
  rw [branchColumn052_17]
  exact sparseColumn17_sum n

theorem branchColumn052_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 18) i) = _
  rw [branchColumn052_18]
  exact sparseColumn18_sum n

theorem branchColumn052_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 19) i) = _
  rw [branchColumn052_19]
  exact sparseColumn19_sum n

theorem branchColumn052_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 20) = sparseColumn52 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 20) = sparseDot52 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 20) i) = _
  rw [branchColumn052_20]
  exact sparseColumn52_sum n

theorem branchColumn052_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 21) i) = _
  rw [branchColumn052_21]
  exact sparseColumn21_sum n

theorem branchColumn052_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 22) i) = _
  rw [branchColumn052_22]
  exact sparseColumn22_sum n

theorem branchColumn052_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 23) = sparseColumn54 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 23) = sparseDot54 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 23) i) = _
  rw [branchColumn052_23]
  exact sparseColumn54_sum n

theorem branchColumn052_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 24) i) = _
  rw [branchColumn052_24]
  exact sparseColumn24_sum n

theorem branchColumn052_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 25) i) = _
  rw [branchColumn052_25]
  exact sparseColumn25_sum n

theorem branchColumn052_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 26) = sparseColumn26 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 26) = sparseDot26 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 26) i) = _
  rw [branchColumn052_26]
  exact sparseColumn26_sum n

theorem branchColumn052_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 27) i) = _
  rw [branchColumn052_27]
  exact sparseColumn27_sum n

theorem branchColumn052_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 28) i) = _
  rw [branchColumn052_28]
  exact sparseColumn28_sum n

theorem branchColumn052_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 29) = sparseColumn49 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 29) = sparseDot49 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 29) i) = _
  rw [branchColumn052_29]
  exact sparseColumn49_sum n

theorem branchColumn052_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 30) i) = _
  rw [branchColumn052_30]
  exact sparseColumn30_sum n

theorem branchColumn052_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 31) i) = _
  rw [branchColumn052_31]
  exact sparseColumn31_sum n

theorem branchColumn052_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 52 i) 32) = sparseColumn43 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 52 i)) = _
  rw [branchIntegerMatrix052_eq]
  simp only [branchIntegerMatrix052, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot052_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) 32) = sparseDot43 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 52 i) 32) i) = _
  rw [branchColumn052_32]
  exact sparseColumn43_sum n

def branchSparseDots052 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot12, sparseDot13, sparseDot14, sparseDot15, sparseDot16, sparseDot17, sparseDot18, sparseDot19, sparseDot52, sparseDot21, sparseDot22, sparseDot54, sparseDot24, sparseDot25, sparseDot26, sparseDot27, sparseDot28, sparseDot49, sparseDot30, sparseDot31, sparseDot43]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot052_0 :
    branchSparseDots052 0 = sparseDot00 := rfl

private theorem branchSparseDot052_1 :
    branchSparseDots052 1 = sparseDot01 := rfl

private theorem branchSparseDot052_2 :
    branchSparseDots052 2 = sparseDot02 := rfl

private theorem branchSparseDot052_3 :
    branchSparseDots052 3 = sparseDot03 := rfl

private theorem branchSparseDot052_4 :
    branchSparseDots052 4 = sparseDot04 := rfl

private theorem branchSparseDot052_5 :
    branchSparseDots052 5 = sparseDot05 := rfl

private theorem branchSparseDot052_6 :
    branchSparseDots052 6 = sparseDot06 := rfl

private theorem branchSparseDot052_7 :
    branchSparseDots052 7 = sparseDot07 := rfl

private theorem branchSparseDot052_8 :
    branchSparseDots052 8 = sparseDot08 := rfl

private theorem branchSparseDot052_9 :
    branchSparseDots052 9 = sparseDot09 := rfl

private theorem branchSparseDot052_10 :
    branchSparseDots052 10 = sparseDot10 := rfl

private theorem branchSparseDot052_11 :
    branchSparseDots052 11 = sparseDot11 := rfl

private theorem branchSparseDot052_12 :
    branchSparseDots052 12 = sparseDot12 := rfl

private theorem branchSparseDot052_13 :
    branchSparseDots052 13 = sparseDot13 := rfl

private theorem branchSparseDot052_14 :
    branchSparseDots052 14 = sparseDot14 := rfl

private theorem branchSparseDot052_15 :
    branchSparseDots052 15 = sparseDot15 := rfl

private theorem branchSparseDot052_16 :
    branchSparseDots052 16 = sparseDot16 := rfl

private theorem branchSparseDot052_17 :
    branchSparseDots052 17 = sparseDot17 := rfl

private theorem branchSparseDot052_18 :
    branchSparseDots052 18 = sparseDot18 := rfl

private theorem branchSparseDot052_19 :
    branchSparseDots052 19 = sparseDot19 := rfl

private theorem branchSparseDot052_20 :
    branchSparseDots052 20 = sparseDot52 := rfl

private theorem branchSparseDot052_21 :
    branchSparseDots052 21 = sparseDot21 := rfl

private theorem branchSparseDot052_22 :
    branchSparseDots052 22 = sparseDot22 := rfl

private theorem branchSparseDot052_23 :
    branchSparseDots052 23 = sparseDot54 := rfl

private theorem branchSparseDot052_24 :
    branchSparseDots052 24 = sparseDot24 := rfl

private theorem branchSparseDot052_25 :
    branchSparseDots052 25 = sparseDot25 := rfl

private theorem branchSparseDot052_26 :
    branchSparseDots052 26 = sparseDot26 := rfl

private theorem branchSparseDot052_27 :
    branchSparseDots052 27 = sparseDot27 := rfl

private theorem branchSparseDot052_28 :
    branchSparseDots052 28 = sparseDot28 := rfl

private theorem branchSparseDot052_29 :
    branchSparseDots052 29 = sparseDot49 := rfl

private theorem branchSparseDot052_30 :
    branchSparseDots052 30 = sparseDot30 := rfl

private theorem branchSparseDot052_31 :
    branchSparseDots052 31 = sparseDot31 := rfl

private theorem branchSparseDot052_32 :
    branchSparseDots052 32 = sparseDot43 := rfl

theorem branchDots052 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 52 i) k) = branchSparseDots052 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot052_0 n
      _ = _ := congrFun branchSparseDot052_0.symm n
  · calc
      _ = sparseDot01 n := branchDot052_1 n
      _ = _ := congrFun branchSparseDot052_1.symm n
  · calc
      _ = sparseDot02 n := branchDot052_2 n
      _ = _ := congrFun branchSparseDot052_2.symm n
  · calc
      _ = sparseDot03 n := branchDot052_3 n
      _ = _ := congrFun branchSparseDot052_3.symm n
  · calc
      _ = sparseDot04 n := branchDot052_4 n
      _ = _ := congrFun branchSparseDot052_4.symm n
  · calc
      _ = sparseDot05 n := branchDot052_5 n
      _ = _ := congrFun branchSparseDot052_5.symm n
  · calc
      _ = sparseDot06 n := branchDot052_6 n
      _ = _ := congrFun branchSparseDot052_6.symm n
  · calc
      _ = sparseDot07 n := branchDot052_7 n
      _ = _ := congrFun branchSparseDot052_7.symm n
  · calc
      _ = sparseDot08 n := branchDot052_8 n
      _ = _ := congrFun branchSparseDot052_8.symm n
  · calc
      _ = sparseDot09 n := branchDot052_9 n
      _ = _ := congrFun branchSparseDot052_9.symm n
  · calc
      _ = sparseDot10 n := branchDot052_10 n
      _ = _ := congrFun branchSparseDot052_10.symm n
  · calc
      _ = sparseDot11 n := branchDot052_11 n
      _ = _ := congrFun branchSparseDot052_11.symm n
  · calc
      _ = sparseDot12 n := branchDot052_12 n
      _ = _ := congrFun branchSparseDot052_12.symm n
  · calc
      _ = sparseDot13 n := branchDot052_13 n
      _ = _ := congrFun branchSparseDot052_13.symm n
  · calc
      _ = sparseDot14 n := branchDot052_14 n
      _ = _ := congrFun branchSparseDot052_14.symm n
  · calc
      _ = sparseDot15 n := branchDot052_15 n
      _ = _ := congrFun branchSparseDot052_15.symm n
  · calc
      _ = sparseDot16 n := branchDot052_16 n
      _ = _ := congrFun branchSparseDot052_16.symm n
  · calc
      _ = sparseDot17 n := branchDot052_17 n
      _ = _ := congrFun branchSparseDot052_17.symm n
  · calc
      _ = sparseDot18 n := branchDot052_18 n
      _ = _ := congrFun branchSparseDot052_18.symm n
  · calc
      _ = sparseDot19 n := branchDot052_19 n
      _ = _ := congrFun branchSparseDot052_19.symm n
  · calc
      _ = sparseDot52 n := branchDot052_20 n
      _ = _ := congrFun branchSparseDot052_20.symm n
  · calc
      _ = sparseDot21 n := branchDot052_21 n
      _ = _ := congrFun branchSparseDot052_21.symm n
  · calc
      _ = sparseDot22 n := branchDot052_22 n
      _ = _ := congrFun branchSparseDot052_22.symm n
  · calc
      _ = sparseDot54 n := branchDot052_23 n
      _ = _ := congrFun branchSparseDot052_23.symm n
  · calc
      _ = sparseDot24 n := branchDot052_24 n
      _ = _ := congrFun branchSparseDot052_24.symm n
  · calc
      _ = sparseDot25 n := branchDot052_25 n
      _ = _ := congrFun branchSparseDot052_25.symm n
  · calc
      _ = sparseDot26 n := branchDot052_26 n
      _ = _ := congrFun branchSparseDot052_26.symm n
  · calc
      _ = sparseDot27 n := branchDot052_27 n
      _ = _ := congrFun branchSparseDot052_27.symm n
  · calc
      _ = sparseDot28 n := branchDot052_28 n
      _ = _ := congrFun branchSparseDot052_28.symm n
  · calc
      _ = sparseDot49 n := branchDot052_29 n
      _ = _ := congrFun branchSparseDot052_29.symm n
  · calc
      _ = sparseDot30 n := branchDot052_30 n
      _ = _ := congrFun branchSparseDot052_30.symm n
  · calc
      _ = sparseDot31 n := branchDot052_31 n
      _ = _ := congrFun branchSparseDot052_31.symm n
  · calc
      _ = sparseDot43 n := branchDot052_32 n
      _ = _ := congrFun branchSparseDot052_32.symm n

def branchIntegerCurvature052 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101955390, 101955390, 44932602, 44932602, 106371291, 106371291, 48290998, 48290998, 289103692, 289103692]

theorem branchIntegerCurvature052_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 52 i)) = branchIntegerCurvature052 := by
  change curvatureNumerators ∘ branchRows 52 = branchIntegerCurvature052
  rw [show branchRows 52 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 52, 53, 34, 35, 50, 51, 38, 39, 46, 47] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature052_entry (i : Fin 42) :
    curvatureNumerators (branchRows 52 i) = branchIntegerCurvature052 i :=
  congrFun branchIntegerCurvature052_eq i

def branchResiduals052 : Fin 33 → Fin 2 → ℕ := ![![1298358832191850, 33000000000000], ![1545976822133216, 33000000000000], ![1582092005565650, 1337469174222803], ![33000000000000, 1023509794979087], ![858568754468382, 33000000000000], ![1056771355059073, 894492268249406], ![723347115984028, 622101700319854], ![33000000000000, 760492582531897], ![1577341241234757, 1129128913475471], ![1025167977617439, 33000000000000], ![33000000000000, 777060371366810], ![511873497841163, 466008616642146], ![989009794979087, 66000000000000], ![33000000000000, 419011200098761], ![315751515649834, 894492268249406], ![926123033860897, 33000000000000], ![66000000000000, 743155328720927], ![953768257573176, 810381613975139], ![622760410346438, 260661852603588], ![628072336791831, 507534631036879], ![1361614081564714, 954654488928133], ![754515935576293, 388499252561215], ![464911442822853, 96820869253143], ![1360614081564648, 954654488928133], ![669066522610473, 230503409392854], ![502901706596590, 223581994926723], ![396300992921948, 853076072054392], ![409602431178326, 547348246810893], ![285313444903937, 308506886524828], ![396300992921948, 954654488928133], ![96820869253143, 555014592156680], ![966659672576201, 651373120454565], ![2023418684621432, 954654488928133]]

theorem branchResiduals052_eq : residualNumerators 52 = branchResiduals052 := rfl

theorem integerCheck052_0_0 :
    integerResidualCheck 52 0 0 (dualNumerators052 0 0) ∧
    integerMassCheck 52 0 0 (dualNumerators052 0 0) := by
  apply integerChecks_of_simple 52 0 0 (dualNumerators052 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1011030237961, 258120108700, 0, 1660206247774, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 1820383169708, 352663154359, 0, 1308901425339, 1754571864380, 80620681505, 1741178091979, 225835502005, 818327875519, 1016864670366]) (branchResiduals052 0 0) 18767167
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck052_0_1 :
    integerResidualCheck 52 0 1 (dualNumerators052 0 1) ∧
    integerMassCheck 52 0 1 (dualNumerators052 0 1) := by
  apply integerChecks_of_simple 52 0 1 (dualNumerators052 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals052 0 1) 18767167
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck052_1_0 :
    integerResidualCheck 52 1 0 (dualNumerators052 1 0) ∧
    integerMassCheck 52 1 0 (dualNumerators052 1 0) := by
  apply integerChecks_of_simple 52 1 0 (dualNumerators052 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1197158056821, 305639293618, 0, 1965845541389, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 2155510583453, 417587447667, 0, 1549866490727, 2077583602197, 95462721871, 2061724074025, 267411181773, 968979732271, 1204066591796]) (branchResiduals052 1 0) 22176635
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck052_1_1 :
    integerResidualCheck 52 1 1 (dualNumerators052 1 1) ∧
    integerMassCheck 52 1 1 (dualNumerators052 1 1) := by
  apply integerChecks_of_simple 52 1 1 (dualNumerators052 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals052 1 1) 22176635
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck052_2_0 :
    integerResidualCheck 52 2 0 (dualNumerators052 2 0) ∧
    integerMassCheck 52 2 0 (dualNumerators052 2 0) := by
  apply integerChecks_of_simple 52 2 0 (dualNumerators052 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1197158056822, 305639293619, 0, 1965845541391, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 2155510583455, 417587447667, 0, 1549866490728, 2077583602198, 95462721871, 2061724074027, 267411181773, 968979732272, 1204066591797]) (branchResiduals052 2 0) 22681452
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck052_2_1 :
    integerResidualCheck 52 2 1 (dualNumerators052 2 1) ∧
    integerMassCheck 52 2 1 (dualNumerators052 2 1) := by
  apply integerChecks_of_simple 52 2 1 (dualNumerators052 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1011030237961, 258120108700, 0, 1660206247773, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 1820383169707, 352663154359, 0, 1308901425338, 1754571864379, 80620681504, 1741178091978, 225835502005, 818327875518, 1016864670365]) (branchResiduals052 2 1) 22681452
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck052_3_0 :
    integerResidualCheck 52 3 0 (dualNumerators052 3 0) ∧
    integerMassCheck 52 3 0 (dualNumerators052 3 0) := by
  apply integerChecks_of_simple 52 3 0 (dualNumerators052 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals052 3 0) 16360330
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck052_3_1 :
    integerResidualCheck 52 3 1 (dualNumerators052 3 1) ∧
    integerMassCheck 52 3 1 (dualNumerators052 3 1) := by
  apply integerChecks_of_simple 52 3 1 (dualNumerators052 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 796619754801, 203380245200, 0, 1308124173107, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1434332169154, 277873425546, 0, 1031321016287, 1382477552007, 63523349867, 1371924214149, 177942276579, 644784030255, 801216871619]) (branchResiduals052 3 1) 16360330
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck052_4_0 :
    integerResidualCheck 52 4 0 (dualNumerators052 4 0) ∧
    integerMassCheck 52 4 0 (dualNumerators052 4 0) := by
  apply integerChecks_of_simple 52 4 0 (dualNumerators052 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 672765518030, 171759757645, 0, 1104743927909, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 1211329770563, 234671131311, 0, 870976665588, 1167537235722, 53647074558, 1158624675158, 150276750182, 544536410901, 676647899379]) (branchResiduals052 4 0) 13760362
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck052_4_1 :
    integerResidualCheck 52 4 1 (dualNumerators052 4 1) ∧
    integerMassCheck 52 4 1 (dualNumerators052 4 1) := by
  apply integerChecks_of_simple 52 4 1 (dualNumerators052 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals052 4 1) 13760362
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck052_5_0 :
    integerResidualCheck 52 5 0 (dualNumerators052 5 0) ∧
    integerMassCheck 52 5 0 (dualNumerators052 5 0) := by
  apply integerChecks_of_simple 52 5 0 (dualNumerators052 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 796619754801, 203380245201, 0, 1308124173108, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000000, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 1434332169156, 277873425546, 0, 1031321016288, 1382477552008, 63523349867, 1371924214150, 177942276579, 644784030255, 801216871620]) (branchResiduals052 5 0) 17641130
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck052_5_1 :
    integerResidualCheck 52 5 1 (dualNumerators052 5 1) ∧
    integerMassCheck 52 5 1 (dualNumerators052 5 1) := by
  apply integerChecks_of_simple 52 5 1 (dualNumerators052 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1211329770562, 234671131311, 0, 870976665588, 1167537235721, 53647074558, 1158624675157, 150276750182, 544536410901, 676647899378]) (branchResiduals052 5 1) 17641130
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck052_6_0 :
    integerResidualCheck 52 6 0 (dualNumerators052 6 0) ∧
    integerMassCheck 52 6 0 (dualNumerators052 6 0) := by
  apply integerChecks_of_simple 52 6 0 (dualNumerators052 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 0, 70552396879, 187567711821, 1472638535954, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 1, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 943299579685, 1229746744383, 0, 0, 877488274356, 957704271528, 103906894360, 5439901403, 818327875519, 1016864670366]) (branchResiduals052 6 0) 8962451
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck052_6_1 :
    integerResidualCheck 52 6 1 (dualNumerators052 6 1) ∧
    integerMassCheck 52 6 1 (dualNumerators052 6 1) := by
  apply integerChecks_of_simple 52 6 1 (dualNumerators052 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949782, 1, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 877083590024, 431817835315, 0, 0, 760187607595, 1097479190627, 0, 0]) (branchResiduals052 6 1) 8962451
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck052_7_0 :
    integerResidualCheck 52 7 0 (dualNumerators052 7 0) ∧
    integerMassCheck 52 7 0 (dualNumerators052 7 0) := by
  apply integerChecks_of_simple 52 7 0 (dualNumerators052 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals052 7 0) 10424794
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck052_7_1 :
    integerResidualCheck 52 7 1 (dualNumerators052 7 1) ∧
    integerMassCheck 52 7 1 (dualNumerators052 7 1) := by
  apply integerChecks_of_simple 52 7 1 (dualNumerators052 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 598579028412, 152819646809, 0, 982922770697, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 1077755291729, 208793723834, 0, 774933245365, 1038791801100, 47731360936, 1030862037014, 133705590887, 484489866137, 602033295899]) (branchResiduals052 7 1) 10424794
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck052_8_0 :
    integerResidualCheck 52 8 0 (dualNumerators052 8 0) ∧
    integerMassCheck 52 8 0 (dualNumerators052 8 0) := by
  apply integerChecks_of_simple 52 8 0 (dualNumerators052 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1197158056824, 305639293618, 0, 1965845541393, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 2155510583457, 417587447668, 0, 1549866490730, 2077583602200, 95462721871, 2061724074028, 267411181773, 968979732273, 1204066591798]) (branchResiduals052 8 0) 22681452
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck052_8_1 :
    integerResidualCheck 52 8 1 (dualNumerators052 8 1) ∧
    integerMassCheck 52 8 1 (dualNumerators052 8 1) := by
  apply integerChecks_of_simple 52 8 1 (dualNumerators052 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 1537359598228, 297832947655, 0, 1105400337063, 1481780287453, 68086203273, 1470468908124, 190723789588, 691098574663, 858767916063]) (branchResiduals052 8 1) 22681452
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck052_9_0 :
    integerResidualCheck 52 9 0 (dualNumerators052 9 0) ∧
    integerMassCheck 52 9 0 (dualNumerators052 9 0) := by
  apply integerChecks_of_simple 52 9 0 (dualNumerators052 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 887477428322, 296619754801, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 703380245200, 296619754801, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1434332169154, 277873425546, 0, 1031321016287, 1382477552007, 63523349867, 1371924214149, 177942276579, 644784030255, 801216871619]) (branchResiduals052 9 0) 16350530
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck052_9_1 :
    integerResidualCheck 52 9 1 (dualNumerators052 9 1) ∧
    integerMassCheck 52 9 1 (dualNumerators052 9 1) := by
  apply integerChecks_of_simple 52 9 1 (dualNumerators052 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals052 9 1) 16350530
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck052_10_0 :
    integerResidualCheck 52 10 0 (dualNumerators052 10 0) ∧
    integerMassCheck 52 10 0 (dualNumerators052 10 0) := by
  apply integerChecks_of_simple 52 10 0 (dualNumerators052 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals052 10 0) 10683139
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck052_10_1 :
    integerResidualCheck 52 10 1 (dualNumerators052 10 1) ∧
    integerMassCheck 52 10 1 (dualNumerators052 10 1) := by
  apply integerChecks_of_simple 52 10 1 (dualNumerators052 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 560661867464, 344525275673, 0, 844525275674, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 419928145920, 344525275674, 155474724327, 844525275674, 0, 0, 1184800741849, 1308901425339, 1096480134411, 212421290928, 0, 788396879662, 1056839694908, 48560642157, 1048772159673, 136028582177, 492907358117, 612492978948]) (branchResiduals052 10 1) 10683139
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck052_11_0 :
    integerResidualCheck 52 11 0 (dualNumerators052 11 0) ∧
    integerMassCheck 52 11 0 (dualNumerators052 11 0) := by
  apply integerChecks_of_simple 52 11 0 (dualNumerators052 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268434, 0, 562584914689, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 1, 0, 736368196709, 813498294019, 681475855631, 132022438389, 0, 489998333105, 656838836154, 30181034864, 651824764029, 84543432681, 306347970271, 380671900746]) (branchResiduals052 11 0) 15120968
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck052_11_1 :
    integerResidualCheck 52 11 1 (dualNumerators052 11 1) ∧
    integerMassCheck 52 11 1 (dualNumerators052 11 1) := by
  apply integerChecks_of_simple 52 11 1 (dualNumerators052 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 621427644954, 120389287883, 0, 446822154676, 598961515206, 27521634498, 594389257794, 77093892371, 279354134309, 347129015395]) (branchResiduals052 11 1) 15120968
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck052_12_0 :
    integerResidualCheck 52 12 0 (dualNumerators052 12 0) ∧
    integerMassCheck 52 12 0 (dualNumerators052 12 0) := by
  apply integerChecks_of_simple 52 12 0 (dualNumerators052 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 1434332169154, 277873425546, 0, 1031321016287, 1382477552007, 63523349867, 1371924214149, 177942276579, 644784030255, 801216871619]) (branchResiduals052 12 0) 16348076
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck052_12_1 :
    integerResidualCheck 52 12 1 (dualNumerators052 12 1) ∧
    integerMassCheck 52 12 1 (dualNumerators052 12 1) := by
  apply integerChecks_of_simple 52 12 1 (dualNumerators052 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals052 12 1) 16348076
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck052_13_0 :
    integerResidualCheck 52 13 0 (dualNumerators052 13 0) ∧
    integerMassCheck 52 13 0 (dualNumerators052 13 0) := by
  apply integerChecks_of_simple 52 13 0 (dualNumerators052 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals052 13 0) 13962901
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck052_13_1 :
    integerResidualCheck 52 13 1 (dualNumerators052 13 1) ∧
    integerMassCheck 52 13 1 (dualNumerators052 13 1) := by
  apply integerChecks_of_simple 52 13 1 (dualNumerators052 13 1)
    (![280984417303, 51728439727, 280984417303, 0, 1, 422262637837, 500000000000, 0, 393964356797, 280984417303, 422262637837, 0, 0, 52371963954, 0, 0, 414120121179, 52371963954, 946336320750, 799204942162, 435488332794, 654450712669, 435488332794, 515660508144, 422262637837, 0, 0, 52371963954, 500000000001, 0, 654450712669, 723000450937, 605664885281, 117335565656, 0, 435488332794, 583768617861, 26823537279, 579312337579, 75138375091, 272268205451, 338323949689]) (branchResiduals052 13 1) 13962901
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck052_14_0 :
    integerResidualCheck 52 14 0 (dualNumerators052 14 0) ∧
    integerMassCheck 52 14 0 (dualNumerators052 14 0) := by
  apply integerChecks_of_simple 52 14 0 (dualNumerators052 14 0)
    (![194975514542, 35894443005, 194975514542, 0, 1, 293008686654, 346950760497, 0, 273372466399, 194975514542, 0, 293008686654, 0, 0, 730242506439, 0, 0, 323699567405, 656664212341, 554569524952, 302186016501, 454124344937, 302186016501, 357817610917, 0, 293008686654, 0, 0, 59592178538, 323699567405, 454124344937, 501691112584, 420271785109, 81419327475, 0, 302186016501, 405077931842, 18612893317, 401985712176, 52138632761, 188927321881, 234763503278]) (branchResiduals052 14 0) 20161291
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck052_14_1 :
    integerResidualCheck 52 14 1 (dualNumerators052 14 1) ∧
    integerMassCheck 52 14 1 (dualNumerators052 14 1) := by
  apply integerChecks_of_simple 52 14 1 (dualNumerators052 14 1)
    (![561968834605, 103456879454, 561968834605, 0, 1, 844525275673, 1000000000000, 0, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 0, 1000000000000, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 1211329770562, 234671131311, 0, 870976665588, 1167537235721, 53647074558, 1158624675157, 150276750182, 544536410901, 676647899378]) (branchResiduals052 14 1) 20161291
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck052_15_0 :
    integerResidualCheck 52 15 0 (dualNumerators052 15 0) ∧
    integerMassCheck 52 15 0 (dualNumerators052 15 0) := by
  apply integerChecks_of_simple 52 15 0 (dualNumerators052 15 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546385, 0, 844525275675, 602334801077, 221089960013, 684097183123, 0, 1184097183122, 1071829546385, 0, 0, 0, 2028622458796, 1713222941252, 933538524389, 1402919220983, 933538524389, 1105400337064, 905187143136, 1, 684097183123, 500000000000, 0, 0, 1402919220983, 1549866490727, 1298339038505, 251527452223, 0, 933538524389, 1251400905751, 57500519589, 1241848160005, 161071060979, 583650214286, 725251211053]) (branchResiduals052 15 0) 12900283
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck052_15_1 :
    integerResidualCheck 52 15 1 (dualNumerators052 15 1) ∧
    integerMassCheck 52 15 1 (dualNumerators052 15 1) := by
  apply integerChecks_of_simple 52 15 1 (dualNumerators052 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals052 15 1) 12900283
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck052_16_0 :
    integerResidualCheck 52 16 0 (dualNumerators052 16 0) ∧
    integerMassCheck 52 16 0 (dualNumerators052 16 0) := by
  apply integerChecks_of_simple 52 16 0 (dualNumerators052 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals052 16 0) 10683060
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck052_16_1 :
    integerResidualCheck 52 16 1 (dualNumerators052 16 1) ∧
    integerMassCheck 52 16 1 (dualNumerators052 16 1) := by
  apply integerChecks_of_simple 52 16 1 (dualNumerators052 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 0, 0, 0, 0, 1184800741849, 1308901425339, 1096480134411, 212421290928, 0, 788396879662, 1056839694908, 48560642157, 1048772159673, 136028582177, 492907358117, 612492978948]) (branchResiduals052 16 1) 10683060
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck052_17_0 :
    integerResidualCheck 52 17 0 (dualNumerators052 17 0) ∧
    integerMassCheck 52 17 0 (dualNumerators052 17 0) := by
  apply integerChecks_of_simple 52 17 0 (dualNumerators052 17 0)
    (![602334801078, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546386, 0, 844525275676, 602334801077, 0, 905187143137, 278910039987, 905187143136, 1071829546386, 0, 0, 1000000000001, 2028622458797, 1713222941254, 933538524390, 1402919220984, 933538524390, 1105400337065, 905187143136, 1, 1184097183123, 0, 0, 0, 1402919220984, 1549866490728, 1298339038506, 251527452223, 0, 933538524390, 1251400905752, 57500519589, 1241848160005, 161071060979, 583650214286, 725251211054]) (branchResiduals052 17 0) 15120968
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck052_17_1 :
    integerResidualCheck 52 17 1 (dualNumerators052 17 1) ∧
    integerMassCheck 52 17 1 (dualNumerators052 17 1) := by
  apply integerChecks_of_simple 52 17 1 (dualNumerators052 17 1)
    (![508686963928, 93647837150, 508686963928, 0, 1, 764453421592, 905187143136, 0, 713222941253, 508686963927, 764453421593, 0, 0, 1000000000000, 905187143136, 0, 844525275674, 0, 1713222941251, 1446860076751, 788396879661, 1184800741848, 788396879661, 933538524388, 764453421592, 1, 0, 1000000000000, 0, 0, 1184800741848, 1308901425338, 1096480134410, 212421290928, 0, 788396879661, 1056839694907, 48560642157, 1048772159672, 136028582177, 492907358117, 612492978947]) (branchResiduals052 17 1) 15120968
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck052_18_0 :
    integerResidualCheck 52 18 0 (dualNumerators052 18 0) ∧
    integerMassCheck 52 18 0 (dualNumerators052 18 0) := by
  apply integerChecks_of_simple 52 18 0 (dualNumerators052 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 562515489548, 74022925577, 0, 476109064652, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415124, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 975124848843, 293271850585, 0, 763999473637, 936711106099, 134481966149, 862769256399, 123780303264, 477654049462, 593539022787]) (branchResiduals052 18 0) 13565580
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck052_18_1 :
    integerResidualCheck 52 18 1 (dualNumerators052 18 1) ∧
    integerMassCheck 52 18 1 (dualNumerators052 18 1) := by
  apply integerChecks_of_simple 52 18 1 (dualNumerators052 18 1)
    (![546080038515, 100531796850, 546080038516, 0, 1, 184109219884, 218003208651, 0, 74499415779, 53134692444, 91228628230, 92880591654, 0, 597399944305, 218003208651, 0, 0, 504519352652, 178954014012, 151131188017, 846351152950, 285344710532, 82351679314, 97512391500, 184109219884, 1, 92880591654, 504519352652, 0, 0, 285344710532, 781937638598, 119604774277, 17115998234, 82351679314, 0, 115464148095, 0, 180745426040, 104599284492, 51486440059, 63977708037]) (branchResiduals052 18 1) 13565580
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck052_19_0 :
    integerResidualCheck 52 19 0 (dualNumerators052 19 0) ∧
    integerMassCheck 52 19 0 (dualNumerators052 19 0) := by
  apply integerChecks_of_simple 52 19 0 (dualNumerators052 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 216703300504, 217988955956, 0, 1402086139076, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 737249033801, 333944038447, 0, 645216866088, 704807657121, 199841967519, 577111910116, 96603051948, 403390917798, 501258706842]) (branchResiduals052 19 0) 8248658
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck052_19_1 :
    integerResidualCheck 52 19 1 (dualNumerators052 19 1) ∧
    integerMassCheck 52 19 1 (dualNumerators052 19 1) := by
  apply integerChecks_of_simple 52 19 1 (dualNumerators052 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 1, 0, 0, 0, 0, 987477735649, 0, 668354800182, 95644673455, 131755764247, 328427706730, 645216866088, 0, 761601233763, 225876501886, 287707656866, 357509209222]) (branchResiduals052 19 1) 8248658
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck052_20_0 :
    integerResidualCheck 52 20 0 (dualNumerators052 20 0) ∧
    integerMassCheck 52 20 0 (dualNumerators052 20 0) := by
  apply integerChecks_of_simple 52 20 0 (dualNumerators052 20 0)
    (![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 1920171252556, 185761786321, 0, 1194803767136, 2493629379177, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038876, 0, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 1368099033367, 195781320438, 941979561817, 0, 1320736486917, 0, 2067456287976, 1196458760692, 588927568327, 731808918591]) (branchResiduals052 20 0) 35312013
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck052_20_1 :
    integerResidualCheck 52 20 1 (dualNumerators052 20 1) ∧
    integerMassCheck 52 20 1 (dualNumerators052 20 1) := by
  apply integerChecks_of_simple 52 20 1 (dualNumerators052 20 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 0, 87654492241, 172716091384, 1501965016760, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 1, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 836254566552, 1355737922885, 0, 1320313360088, 769869471398, 1081323590019, 0, 135852760286, 825462640703, 1025730420714]) (branchResiduals052 20 1) 35312013
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck052_21_0 :
    integerResidualCheck 52 21 0 (dualNumerators052 21 0) ∧
    integerMassCheck 52 21 0 (dualNumerators052 21 0) := by
  apply integerChecks_of_simple 52 21 0 (dualNumerators052 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 625556137801, 307982386589, 759767979803, 549133445537, 851509250277, 798941670661, 583650214286, 725251211053]) (branchResiduals052 21 0) 11182451
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck052_21_1 :
    integerResidualCheck 52 21 1 (dualNumerators052 21 1) ∧
    integerMassCheck 52 21 1 (dualNumerators052 21 1) := by
  apply integerChecks_of_simple 52 21 1 (dualNumerators052 21 1)
    (![114087637157, 21003212630, 114087637157, 0, 1, 11738971135, 13900082653, 0, 159960694697, 114087637156, 0, 11738971135, 207227876819, 1201147979134, 13900082653, 0, 0, 1189409008001, 1568336550649, 324499857786, 176820605835, 18193837997, 176820605835, 209372781287, 11738971135, 0, 218966847953, 1189409008000, 0, 0, 18193837997, 1843425165269, 918700010035, 924725155234, 0, 176820605835, 103103392317, 144814328227, 0, 18193837997, 110548608107, 137369112437]) (branchResiduals052 21 1) 11182451
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck052_22_0 :
    integerResidualCheck 52 22 0 (dualNumerators052 22 0) ∧
    integerMassCheck 52 22 0 (dualNumerators052 22 0) := by
  apply integerChecks_of_simple 52 22 0 (dualNumerators052 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 583695195717, 0, 612220343874, 0, 492945346072, 1, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554683, 1, 583695195717, 0, 0, 0, 801336080718, 763999473637, 179826715678, 584172757959, 460183470977, 0, 216080085359, 429136780729, 256292246333, 545043834385, 287707656866, 357509209222]) (branchResiduals052 22 0) 6465674
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck052_22_1 :
    integerResidualCheck 52 22 1 (dualNumerators052 22 1) ∧
    integerMassCheck 52 22 1 (dualNumerators052 22 1) := by
  apply integerChecks_of_simple 52 22 1 (dualNumerators052 22 1)
    (![50594765625, 9314353833, 50594765625, 0, 0, 5205914576, 6164308785, 0, 70938219592, 50594765625, 0, 5205914576, 10257833851, 89203660570, 6164308785, 0, 0, 83997745994, 1170399714012, 143906865451, 78415131848, 8068472555, 78415131848, 92851136735, 5205914576, 0, 15463748427, 83997745994, 0, 0, 8068472555, 130185291813, 109057552771, 21127739043, 0, 78415131848, 45723551643, 64221217814, 0, 8068472555, 49025302449, 60919467008]) (branchResiduals052 22 1) 6465674
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck052_23_0 :
    integerResidualCheck 52 23 0 (dualNumerators052 23 0) ∧
    integerMassCheck 52 23 0 (dualNumerators052 23 0) := by
  apply integerChecks_of_simple 52 23 0 (dualNumerators052 23 0)
    (![607781100794, 111890788611, 607781100794, 0, 2, 2105933038874, 2493629379175, 0, 852161457016, 607781100793, 1920171252556, 185761786321, 0, 1194803767136, 2493629379175, 0, 0, 1009041980816, 2046965224151, 1728713870221, 941979561817, 3263915048668, 941979561817, 1115395345706, 2105933038876, 0, 185761786321, 1009041980816, 0, 0, 3263915048668, 1563880353804, 368099033367, 1195781320438, 941979561817, 0, 1320736486917, 0, 2067456287976, 1196458760692, 588927568327, 731808918591]) (branchResiduals052 23 0) 35297932
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck052_23_1 :
    integerResidualCheck 52 23 1 (dualNumerators052 23 1) ∧
    integerMassCheck 52 23 1 (dualNumerators052 23 1) := by
  apply integerChecks_of_simple 52 23 1 (dualNumerators052 23 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 0, 87654492241, 172716091384, 1501965016760, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 1, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 1836254566552, 355737922885, 0, 1320313360088, 769869471398, 1081323590019, 0, 135852760286, 825462640703, 1025730420714]) (branchResiduals052 23 1) 35297932
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck052_24_0 :
    integerResidualCheck 52 24 0 (dualNumerators052 24 0) ∧
    integerMassCheck 52 24 0 (dualNumerators052 24 0) := by
  apply integerChecks_of_simple 52 24 0 (dualNumerators052 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 276221246109, 150663467366, 0, 969054410724, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 550599432783, 717797266644, 0, 0, 512185690040, 559007382209, 569308312247, 737522866658, 477654049462, 593539022787]) (branchResiduals052 24 0) 9356857
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck052_24_1 :
    integerResidualCheck 52 24 1 (dualNumerators052 24 1) ∧
    integerMassCheck 52 24 1 (dualNumerators052 24 1) := by
  apply integerChecks_of_simple 52 24 1 (dualNumerators052 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 395480180778, 20824623507, 0, 133942179966, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 71330612949, 103986497321, 587483804282, 282115266095, 66021086067, 82038644814, 0, 0, 66021086067, 82038644814]) (branchResiduals052 24 1) 9356857
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck052_25_0 :
    integerResidualCheck 52 25 0 (dualNumerators052 25 0) ∧
    integerMassCheck 52 25 0 (dualNumerators052 25 0) := by
  apply integerChecks_of_simple 52 25 0 (dualNumerators052 25 0)
    (![30936264063, 5695279071, 30936264063, 0, 1, 16941043971, 20059842445, 0, 627070502755, 447241068346, 373191945837, 136694444207, 0, 879206860134, 603755038162, 0, 0, 742512415929, 1506277362888, 1272089305134, 47947079019, 26256356369, 693163945107, 820773474842, 509886390043, 1, 136694444206, 742512415929, 0, 0, 790255830005, 1150795112397, 483731503338, 667063609060, 47947079019, 0, 448879356988, 522996202554, 26256356369, 0, 433367530667, 538508028875]) (branchResiduals052 25 0) 8671199
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck052_25_1 :
    integerResidualCheck 52 25 1 (dualNumerators052 25 1) ∧
    integerMassCheck 52 25 1 (dualNumerators052 25 1) := by
  apply integerChecks_of_simple 52 25 1 (dualNumerators052 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 0, 0, 0, 251429110121, 0, 0, 0, 432354273819, 212862592270, 0, 0, 415529968297, 599898615461, 0, 0]) (branchResiduals052 25 1) 8671199
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck052_26_0 :
    integerResidualCheck 52 26 0 (dualNumerators052 26 0) ∧
    integerMassCheck 52 26 0 (dualNumerators052 26 0) := by
  apply integerChecks_of_simple 52 26 0 (dualNumerators052 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0]) (branchResiduals052 26 0) 15099566
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck052_26_1 :
    integerResidualCheck 52 26 1 (dualNumerators052 26 1) ∧
    integerMassCheck 52 26 1 (dualNumerators052 26 1) := by
  apply integerChecks_of_simple 52 26 1 (dualNumerators052 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 830784228945, 1211125748477, 879744679617, 350168760452, 768944423926, 955500162657, 0, 0, 768944423926, 955500162657]) (branchResiduals052 26 1) 15099566
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck052_27_0 :
    integerResidualCheck 52 27 0 (dualNumerators052 27 0) ∧
    integerMassCheck 52 27 0 (dualNumerators052 27 0) := by
  apply integerChecks_of_simple 52 27 0 (dualNumerators052 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312724, 1, 0, 0, 0, 0, 741473662376, 0, 0, 0, 365134112286, 179767839417, 0, 0, 286173900105, 455299762271, 340673826058, 423325647580]) (branchResiduals052 27 0) 7338775
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck052_27_1 :
    integerResidualCheck 52 27 1 (dualNumerators052 27 1) ∧
    integerMassCheck 52 27 1 (dualNumerators052 27 1) := by
  apply integerChecks_of_simple 52 27 1 (dualNumerators052 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 234337221023, 181967583262, 0, 1170399780726, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 918185996600, 613751944609, 0, 377837583379, 871790834897, 421969477217, 576174693322, 69042172766, 236224837801, 293536000677]) (branchResiduals052 27 1) 7338775
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck052_28_0 :
    integerResidualCheck 52 28 0 (dualNumerators052 28 0) ∧
    integerMassCheck 52 28 0 (dualNumerators052 28 0) := by
  apply integerChecks_of_simple 52 28 0 (dualNumerators052 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 1, 0, 0, 0, 0, 845822205349, 0, 0, 0, 308364986836, 151818484141, 0, 0, 450383711774, 395438493575, 287707656866, 357509209222]) (branchResiduals052 28 0) 10335557
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck052_28_1 :
    integerResidualCheck 52 28 1 (dualNumerators052 28 1) ∧
    integerMassCheck 52 28 1 (dualNumerators052 28 1) := by
  apply integerChecks_of_simple 52 28 1 (dualNumerators052 28 1)
    (![71098470185, 13089028086, 71098470186, 0, 1, 500260975618, 592357612055, 0, 99686179557, 71098470185, 0, 7315629546, 105164706304, 618299100026, 8662416338, 0, 0, 610983470481, 1239454790169, 202225622679, 110193136482, 775337722729, 110193136482, 130479382508, 7315629546, 0, 112480335850, 610983470480, 0, 0, 11338249092, 946942807286, 484898704770, 462044102516, 0, 110193136482, 456220281523, 343496853848, 0, 11338249092, 68892976605, 85607292678]) (branchResiduals052 28 1) 10335557
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck052_29_0 :
    integerResidualCheck 52 29 0 (dualNumerators052 29 0) ∧
    integerMassCheck 52 29 0 (dualNumerators052 29 0) := by
  apply integerChecks_of_simple 52 29 0 (dualNumerators052 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0]) (branchResiduals052 29 0) 40352153
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck052_29_1 :
    integerResidualCheck 52 29 1 (dualNumerators052 29 1) ∧
    integerMassCheck 52 29 1 (dualNumerators052 29 1) := by
  apply integerChecks_of_simple 52 29 1 (dualNumerators052 29 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 0, 87654492241, 172716091384, 1501965016760, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 1, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 1836254566552, 355737922885, 0, 1320313360088, 1769869471398, 81323590019, 0, 135852760286, 825462640703, 1025730420714]) (branchResiduals052 29 1) 40352153
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck052_30_0 :
    integerResidualCheck 52 30 0 (dualNumerators052 30 0) ∧
    integerMassCheck 52 30 0 (dualNumerators052 30 0) := by
  apply integerChecks_of_simple 52 30 0 (dualNumerators052 30 0)
    (![50594765625, 9314353833, 50594765625, 0, 0, 5205914576, 6164308785, 0, 70938219592, 50594765625, 0, 5205914576, 10257833851, 89203660570, 6164308785, 0, 0, 83997745994, 170399714012, 1143906865451, 78415131848, 8068472555, 78415131848, 92851136735, 5205914576, 0, 15463748427, 83997745994, 0, 0, 8068472555, 130185291813, 109057552771, 21127739043, 0, 78415131848, 105114855418, 4829914039, 0, 8068472555, 108416606224, 1528163233]) (branchResiduals052 30 0) 7680628
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck052_30_1 :
    integerResidualCheck 52 30 1 (dualNumerators052 30 1) ∧
    integerMassCheck 52 30 1 (dualNumerators052 30 1) := by
  apply integerChecks_of_simple 52 30 1 (dualNumerators052 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 491724510490, 107456641334, 0, 691151837050, 709488714054, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 757834259187, 146815365454, 0, 544901951702, 730436696602, 33562777035, 829173251111, 99477537975, 281282522283, 482716951355]) (branchResiduals052 30 1) 7680628
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck052_31_0 :
    integerResidualCheck 52 31 0 (dualNumerators052 31 0) ∧
    integerMassCheck 52 31 0 (dualNumerators052 31 0) := by
  apply integerChecks_of_simple 52 31 0 (dualNumerators052 31 0)
    (![1014824557516, 186826342402, 1014824557516, 0, 1, 1032415642124, 1222480453651, 0, 1422871445689, 1014824557515, 940234337176, 92181304950, 0, 592902192609, 1222480453651, 0, 0, 500720887661, 1015773638296, 1702371787578, 1572842575661, 1600106408231, 1572842575661, 1862398463333, 1032415642124, 1, 92181304949, 500720887660, 0, 0, 1600106408231, 776050524992, 678897187053, 97153337939, 711927549445, 860915026216, 655394283556, 0, 654789687546, 945316720686, 655394283556, 0]) (branchResiduals052 31 0) 32891612
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck052_31_1 :
    integerResidualCheck 52 31 1 (dualNumerators052 31 1) ∧
    integerMassCheck 52 31 1 (dualNumerators052 31 1) := by
  apply integerChecks_of_simple 52 31 1 (dualNumerators052 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 274671058114, 217988955956, 0, 1402086139076, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 796640337576, 1038552208309, 0, 0, 741061026801, 808805463926, 725570984152, 37986262977, 327950144489, 1221916346239]) (branchResiduals052 31 1) 32891612
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck052_32_0 :
    integerResidualCheck 52 32 0 (dualNumerators052 32 0) ∧
    integerMassCheck 52 32 0 (dualNumerators052 32 0) := by
  apply integerChecks_of_simple 52 32 0 (dualNumerators052 32 0)
    (![1032013329790, 189990746959, 1032013329790, 0, 3, 2743468108580, 3248532859356, 0, 1446971585042, 1032013329789, 1713354977902, 1030113130681, 2028778803022, 0, 505064750776, 2743468108580, 0, 1713354977903, 3475750388062, 2935359054651, 1599482877825, 4252009289869, 1599482877825, 1893943170084, 0, 2743468108582, 315423825121, 1713354977902, 0, 0, 4252009289869, 2655471466972, 2224515654627, 430955812345, 0, 1599482877825, 2144093971220, 98518801469, 3884085649292, 367923640577, 0, 2242612772688]) (branchResiduals052 32 0) 67647473
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck052_32_1 :
    integerResidualCheck 52 32 1 (dualNumerators052 32 1) ∧
    integerMassCheck 52 32 1 (dualNumerators052 32 1) := by
  apply integerChecks_of_simple 52 32 1 (dualNumerators052 32 1)
    (![851888448448, 156830263694, 851888448449, 0, 1, 87654492241, 103791437351, 0, 1194420985611, 851888448448, 0, 87654492241, 172716091384, 1501965016760, 103791437351, 0, 0, 1414310524521, 2869102093752, 2423029236662, 1320313360088, 135852760286, 1320313360088, 1563379330518, 87654492241, 1, 260370583625, 1414310524520, 0, 0, 135852760286, 2191992489437, 1836254566552, 355737922885, 0, 1320313360088, 1769869471398, 81323590019, 0, 135852760286, 1825462640703, 25730420714]) (branchResiduals052 32 1) 67647473
    branchSparseDots052 branchIntegerCurvature052 branchDots052
    branchIntegerCurvature052_entry rfl
    (congrFun (congrFun branchResiduals052_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks052 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 52 j s (dualNumerators052 j s) ∧
    integerMassCheck 52 j s (dualNumerators052 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck052_0_0
    · exact integerCheck052_0_1
  · fin_cases s
    · exact integerCheck052_1_0
    · exact integerCheck052_1_1
  · fin_cases s
    · exact integerCheck052_2_0
    · exact integerCheck052_2_1
  · fin_cases s
    · exact integerCheck052_3_0
    · exact integerCheck052_3_1
  · fin_cases s
    · exact integerCheck052_4_0
    · exact integerCheck052_4_1
  · fin_cases s
    · exact integerCheck052_5_0
    · exact integerCheck052_5_1
  · fin_cases s
    · exact integerCheck052_6_0
    · exact integerCheck052_6_1
  · fin_cases s
    · exact integerCheck052_7_0
    · exact integerCheck052_7_1
  · fin_cases s
    · exact integerCheck052_8_0
    · exact integerCheck052_8_1
  · fin_cases s
    · exact integerCheck052_9_0
    · exact integerCheck052_9_1
  · fin_cases s
    · exact integerCheck052_10_0
    · exact integerCheck052_10_1
  · fin_cases s
    · exact integerCheck052_11_0
    · exact integerCheck052_11_1
  · fin_cases s
    · exact integerCheck052_12_0
    · exact integerCheck052_12_1
  · fin_cases s
    · exact integerCheck052_13_0
    · exact integerCheck052_13_1
  · fin_cases s
    · exact integerCheck052_14_0
    · exact integerCheck052_14_1
  · fin_cases s
    · exact integerCheck052_15_0
    · exact integerCheck052_15_1
  · fin_cases s
    · exact integerCheck052_16_0
    · exact integerCheck052_16_1
  · fin_cases s
    · exact integerCheck052_17_0
    · exact integerCheck052_17_1
  · fin_cases s
    · exact integerCheck052_18_0
    · exact integerCheck052_18_1
  · fin_cases s
    · exact integerCheck052_19_0
    · exact integerCheck052_19_1
  · fin_cases s
    · exact integerCheck052_20_0
    · exact integerCheck052_20_1
  · fin_cases s
    · exact integerCheck052_21_0
    · exact integerCheck052_21_1
  · fin_cases s
    · exact integerCheck052_22_0
    · exact integerCheck052_22_1
  · fin_cases s
    · exact integerCheck052_23_0
    · exact integerCheck052_23_1
  · fin_cases s
    · exact integerCheck052_24_0
    · exact integerCheck052_24_1
  · fin_cases s
    · exact integerCheck052_25_0
    · exact integerCheck052_25_1
  · fin_cases s
    · exact integerCheck052_26_0
    · exact integerCheck052_26_1
  · fin_cases s
    · exact integerCheck052_27_0
    · exact integerCheck052_27_1
  · fin_cases s
    · exact integerCheck052_28_0
    · exact integerCheck052_28_1
  · fin_cases s
    · exact integerCheck052_29_0
    · exact integerCheck052_29_1
  · fin_cases s
    · exact integerCheck052_30_0
    · exact integerCheck052_30_1
  · fin_cases s
    · exact integerCheck052_31_0
    · exact integerCheck052_31_1
  · fin_cases s
    · exact integerCheck052_32_0
    · exact integerCheck052_32_1

end ElevenSquare.Tasks.T06
