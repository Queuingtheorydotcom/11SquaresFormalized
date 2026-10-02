import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual080
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
import ElevenSquare.Tasks.T06.SparseColumn27
import ElevenSquare.Tasks.T06.SparseColumn28
import ElevenSquare.Tasks.T06.SparseColumn30
import ElevenSquare.Tasks.T06.SparseColumn31
import ElevenSquare.Tasks.T06.SparseColumn32
import ElevenSquare.Tasks.T06.SparseColumn47
import ElevenSquare.Tasks.T06.SparseColumn48
import ElevenSquare.Tasks.T06.SparseColumn55
import ElevenSquare.Tasks.T06.SparseColumn56

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix080 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral28, roundedGradientLiteral29, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix080_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = branchIntegerMatrix080 := by
  change roundedGradients ∘ branchRows 80 = branchIntegerMatrix080
  rw [show branchRows 80 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral28_eq, roundedGradientLiteral29_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix080]

theorem branchColumn080_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 0) i) = _
  rw [branchColumn080_0]
  exact sparseColumn00_sum n

theorem branchColumn080_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 1) i) = _
  rw [branchColumn080_1]
  exact sparseColumn01_sum n

theorem branchColumn080_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 2) i) = _
  rw [branchColumn080_2]
  exact sparseColumn02_sum n

theorem branchColumn080_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 3) i) = _
  rw [branchColumn080_3]
  exact sparseColumn03_sum n

theorem branchColumn080_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 4) i) = _
  rw [branchColumn080_4]
  exact sparseColumn04_sum n

theorem branchColumn080_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 5) i) = _
  rw [branchColumn080_5]
  exact sparseColumn05_sum n

theorem branchColumn080_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 6) i) = _
  rw [branchColumn080_6]
  exact sparseColumn06_sum n

theorem branchColumn080_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 7) i) = _
  rw [branchColumn080_7]
  exact sparseColumn07_sum n

theorem branchColumn080_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 8) i) = _
  rw [branchColumn080_8]
  exact sparseColumn08_sum n

theorem branchColumn080_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 9) i) = _
  rw [branchColumn080_9]
  exact sparseColumn09_sum n

theorem branchColumn080_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 10) i) = _
  rw [branchColumn080_10]
  exact sparseColumn10_sum n

theorem branchColumn080_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 11) i) = _
  rw [branchColumn080_11]
  exact sparseColumn11_sum n

theorem branchColumn080_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 12) = sparseColumn12 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 12) = sparseDot12 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 12) i) = _
  rw [branchColumn080_12]
  exact sparseColumn12_sum n

theorem branchColumn080_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 13) = sparseColumn13 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 13) = sparseDot13 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 13) i) = _
  rw [branchColumn080_13]
  exact sparseColumn13_sum n

theorem branchColumn080_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 14) = sparseColumn14 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 14) = sparseDot14 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 14) i) = _
  rw [branchColumn080_14]
  exact sparseColumn14_sum n

theorem branchColumn080_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 15) = sparseColumn15 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 15) = sparseDot15 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 15) i) = _
  rw [branchColumn080_15]
  exact sparseColumn15_sum n

theorem branchColumn080_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 16) = sparseColumn16 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 16) = sparseDot16 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 16) i) = _
  rw [branchColumn080_16]
  exact sparseColumn16_sum n

theorem branchColumn080_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 17) i) = _
  rw [branchColumn080_17]
  exact sparseColumn17_sum n

theorem branchColumn080_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 18) i) = _
  rw [branchColumn080_18]
  exact sparseColumn18_sum n

theorem branchColumn080_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 19) i) = _
  rw [branchColumn080_19]
  exact sparseColumn19_sum n

theorem branchColumn080_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 20) = sparseColumn55 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 20) = sparseDot55 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 20) i) = _
  rw [branchColumn080_20]
  exact sparseColumn55_sum n

theorem branchColumn080_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 21) i) = _
  rw [branchColumn080_21]
  exact sparseColumn21_sum n

theorem branchColumn080_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 22) i) = _
  rw [branchColumn080_22]
  exact sparseColumn22_sum n

theorem branchColumn080_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 23) = sparseColumn47 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 23) = sparseDot47 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 23) i) = _
  rw [branchColumn080_23]
  exact sparseColumn47_sum n

theorem branchColumn080_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 24) i) = _
  rw [branchColumn080_24]
  exact sparseColumn24_sum n

theorem branchColumn080_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 25) i) = _
  rw [branchColumn080_25]
  exact sparseColumn25_sum n

theorem branchColumn080_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 26) = sparseColumn56 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 26) = sparseDot56 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 26) i) = _
  rw [branchColumn080_26]
  exact sparseColumn56_sum n

theorem branchColumn080_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 27) i) = _
  rw [branchColumn080_27]
  exact sparseColumn27_sum n

theorem branchColumn080_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 28) i) = _
  rw [branchColumn080_28]
  exact sparseColumn28_sum n

theorem branchColumn080_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 29) = sparseColumn48 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 29) = sparseDot48 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 29) i) = _
  rw [branchColumn080_29]
  exact sparseColumn48_sum n

theorem branchColumn080_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 30) i) = _
  rw [branchColumn080_30]
  exact sparseColumn30_sum n

theorem branchColumn080_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 31) i) = _
  rw [branchColumn080_31]
  exact sparseColumn31_sum n

theorem branchColumn080_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 80 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 80 i)) = _
  rw [branchIntegerMatrix080_eq]
  simp only [branchIntegerMatrix080, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot080_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 80 i) 32) i) = _
  rw [branchColumn080_32]
  exact sparseColumn32_sum n

def branchSparseDots080 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot12, sparseDot13, sparseDot14, sparseDot15, sparseDot16, sparseDot17, sparseDot18, sparseDot19, sparseDot55, sparseDot21, sparseDot22, sparseDot47, sparseDot24, sparseDot25, sparseDot56, sparseDot27, sparseDot28, sparseDot48, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot080_0 :
    branchSparseDots080 0 = sparseDot00 := rfl

private theorem branchSparseDot080_1 :
    branchSparseDots080 1 = sparseDot01 := rfl

private theorem branchSparseDot080_2 :
    branchSparseDots080 2 = sparseDot02 := rfl

private theorem branchSparseDot080_3 :
    branchSparseDots080 3 = sparseDot03 := rfl

private theorem branchSparseDot080_4 :
    branchSparseDots080 4 = sparseDot04 := rfl

private theorem branchSparseDot080_5 :
    branchSparseDots080 5 = sparseDot05 := rfl

private theorem branchSparseDot080_6 :
    branchSparseDots080 6 = sparseDot06 := rfl

private theorem branchSparseDot080_7 :
    branchSparseDots080 7 = sparseDot07 := rfl

private theorem branchSparseDot080_8 :
    branchSparseDots080 8 = sparseDot08 := rfl

private theorem branchSparseDot080_9 :
    branchSparseDots080 9 = sparseDot09 := rfl

private theorem branchSparseDot080_10 :
    branchSparseDots080 10 = sparseDot10 := rfl

private theorem branchSparseDot080_11 :
    branchSparseDots080 11 = sparseDot11 := rfl

private theorem branchSparseDot080_12 :
    branchSparseDots080 12 = sparseDot12 := rfl

private theorem branchSparseDot080_13 :
    branchSparseDots080 13 = sparseDot13 := rfl

private theorem branchSparseDot080_14 :
    branchSparseDots080 14 = sparseDot14 := rfl

private theorem branchSparseDot080_15 :
    branchSparseDots080 15 = sparseDot15 := rfl

private theorem branchSparseDot080_16 :
    branchSparseDots080 16 = sparseDot16 := rfl

private theorem branchSparseDot080_17 :
    branchSparseDots080 17 = sparseDot17 := rfl

private theorem branchSparseDot080_18 :
    branchSparseDots080 18 = sparseDot18 := rfl

private theorem branchSparseDot080_19 :
    branchSparseDots080 19 = sparseDot19 := rfl

private theorem branchSparseDot080_20 :
    branchSparseDots080 20 = sparseDot55 := rfl

private theorem branchSparseDot080_21 :
    branchSparseDots080 21 = sparseDot21 := rfl

private theorem branchSparseDot080_22 :
    branchSparseDots080 22 = sparseDot22 := rfl

private theorem branchSparseDot080_23 :
    branchSparseDots080 23 = sparseDot47 := rfl

private theorem branchSparseDot080_24 :
    branchSparseDots080 24 = sparseDot24 := rfl

private theorem branchSparseDot080_25 :
    branchSparseDots080 25 = sparseDot25 := rfl

private theorem branchSparseDot080_26 :
    branchSparseDots080 26 = sparseDot56 := rfl

private theorem branchSparseDot080_27 :
    branchSparseDots080 27 = sparseDot27 := rfl

private theorem branchSparseDot080_28 :
    branchSparseDots080 28 = sparseDot28 := rfl

private theorem branchSparseDot080_29 :
    branchSparseDots080 29 = sparseDot48 := rfl

private theorem branchSparseDot080_30 :
    branchSparseDots080 30 = sparseDot30 := rfl

private theorem branchSparseDot080_31 :
    branchSparseDots080 31 = sparseDot31 := rfl

private theorem branchSparseDot080_32 :
    branchSparseDots080 32 = sparseDot32 := rfl

theorem branchDots080 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 80 i) k) = branchSparseDots080 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot080_0 n
      _ = _ := congrFun branchSparseDot080_0.symm n
  · calc
      _ = sparseDot01 n := branchDot080_1 n
      _ = _ := congrFun branchSparseDot080_1.symm n
  · calc
      _ = sparseDot02 n := branchDot080_2 n
      _ = _ := congrFun branchSparseDot080_2.symm n
  · calc
      _ = sparseDot03 n := branchDot080_3 n
      _ = _ := congrFun branchSparseDot080_3.symm n
  · calc
      _ = sparseDot04 n := branchDot080_4 n
      _ = _ := congrFun branchSparseDot080_4.symm n
  · calc
      _ = sparseDot05 n := branchDot080_5 n
      _ = _ := congrFun branchSparseDot080_5.symm n
  · calc
      _ = sparseDot06 n := branchDot080_6 n
      _ = _ := congrFun branchSparseDot080_6.symm n
  · calc
      _ = sparseDot07 n := branchDot080_7 n
      _ = _ := congrFun branchSparseDot080_7.symm n
  · calc
      _ = sparseDot08 n := branchDot080_8 n
      _ = _ := congrFun branchSparseDot080_8.symm n
  · calc
      _ = sparseDot09 n := branchDot080_9 n
      _ = _ := congrFun branchSparseDot080_9.symm n
  · calc
      _ = sparseDot10 n := branchDot080_10 n
      _ = _ := congrFun branchSparseDot080_10.symm n
  · calc
      _ = sparseDot11 n := branchDot080_11 n
      _ = _ := congrFun branchSparseDot080_11.symm n
  · calc
      _ = sparseDot12 n := branchDot080_12 n
      _ = _ := congrFun branchSparseDot080_12.symm n
  · calc
      _ = sparseDot13 n := branchDot080_13 n
      _ = _ := congrFun branchSparseDot080_13.symm n
  · calc
      _ = sparseDot14 n := branchDot080_14 n
      _ = _ := congrFun branchSparseDot080_14.symm n
  · calc
      _ = sparseDot15 n := branchDot080_15 n
      _ = _ := congrFun branchSparseDot080_15.symm n
  · calc
      _ = sparseDot16 n := branchDot080_16 n
      _ = _ := congrFun branchSparseDot080_16.symm n
  · calc
      _ = sparseDot17 n := branchDot080_17 n
      _ = _ := congrFun branchSparseDot080_17.symm n
  · calc
      _ = sparseDot18 n := branchDot080_18 n
      _ = _ := congrFun branchSparseDot080_18.symm n
  · calc
      _ = sparseDot19 n := branchDot080_19 n
      _ = _ := congrFun branchSparseDot080_19.symm n
  · calc
      _ = sparseDot55 n := branchDot080_20 n
      _ = _ := congrFun branchSparseDot080_20.symm n
  · calc
      _ = sparseDot21 n := branchDot080_21 n
      _ = _ := congrFun branchSparseDot080_21.symm n
  · calc
      _ = sparseDot22 n := branchDot080_22 n
      _ = _ := congrFun branchSparseDot080_22.symm n
  · calc
      _ = sparseDot47 n := branchDot080_23 n
      _ = _ := congrFun branchSparseDot080_23.symm n
  · calc
      _ = sparseDot24 n := branchDot080_24 n
      _ = _ := congrFun branchSparseDot080_24.symm n
  · calc
      _ = sparseDot25 n := branchDot080_25 n
      _ = _ := congrFun branchSparseDot080_25.symm n
  · calc
      _ = sparseDot56 n := branchDot080_26 n
      _ = _ := congrFun branchSparseDot080_26.symm n
  · calc
      _ = sparseDot27 n := branchDot080_27 n
      _ = _ := congrFun branchSparseDot080_27.symm n
  · calc
      _ = sparseDot28 n := branchDot080_28 n
      _ = _ := congrFun branchSparseDot080_28.symm n
  · calc
      _ = sparseDot48 n := branchDot080_29 n
      _ = _ := congrFun branchSparseDot080_29.symm n
  · calc
      _ = sparseDot30 n := branchDot080_30 n
      _ = _ := congrFun branchSparseDot080_30.symm n
  · calc
      _ = sparseDot31 n := branchDot080_31 n
      _ = _ := congrFun branchSparseDot080_31.symm n
  · calc
      _ = sparseDot32 n := branchDot080_32 n
      _ = _ := congrFun branchSparseDot080_32.symm n

def branchIntegerCurvature080 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101981296, 101981296, 79086693, 79086693, 106371291, 106371291, 48290998, 48290998, 204734428, 204734428]

theorem branchIntegerCurvature080_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 80 i)) = branchIntegerCurvature080 := by
  change curvatureNumerators ∘ branchRows 80 = branchIntegerCurvature080
  rw [show branchRows 80 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature080_entry (i : Fin 42) :
    curvatureNumerators (branchRows 80 i) = branchIntegerCurvature080 i :=
  congrFun branchIntegerCurvature080_eq i

def branchResiduals080 : Fin 33 → Fin 2 → ℕ := ![![1302257427328372, 33000000000000], ![1546551569028370, 33000000000000], ![1585127095212755, 1338260583187973], ![33000000000000, 1024910356255075], ![861007722689791, 33000000000000], ![1055998955028457, 894801629003218], ![723886069516686, 624777238175104], ![33000000000000, 763525801716916], ![1580659678879458, 1128452734381895], ![1026568538893427, 33000000000000], ![33000000000000, 778027430759126], ![509516446068323, 464022179603405], ![990410356255075, 66000000000000], ![33000000000000, 419537407182879], ![318419503876888, 894801629003218], ![926604218601625, 33000000000000], ![66000000000000, 744122388113243], ![955655668501015, 812886379303975], ![623355374180069, 270865009653394], ![632221493436520, 512304098835474], ![1475782214030092, 854833127134258], ![752007348580913, 375215540078376], ![470667348659713, 90706651221511], ![1478622365049130, 854833127134258], ![670001998447466, 230874054719092], ![506741633438651, 220935526651417], ![396300992921948, 854833127134258], ![408930962063290, 547859315217757], ![285784861133797, 299207140313493], ![396300992921948, 894213626664326], ![217028033353406, 553078169200686], ![1682112528662530, 651514209790585], ![1332039050357428, 2885910746952835]]

theorem branchResiduals080_eq : residualNumerators 80 = branchResiduals080 := rfl

theorem integerCheck080_0_0 :
    integerResidualCheck 80 0 0 (dualNumerators080 0 0) ∧
    integerMassCheck 80 0 0 (dualNumerators080 0 0) := by
  apply integerChecks_of_simple 80 0 0 (dualNumerators080 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1011030237961, 258120108700, 0, 1660206247774, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 217988955954, 1955057368113, 74854042823, 1234047382517, 1835192545884, 0, 1821798773483, 145214820501, 1430871029972, 404321515913]) (branchResiduals080 0 0) 18767167
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck080_0_1 :
    integerResidualCheck 80 0 1 (dualNumerators080 0 1) ∧
    integerMassCheck 80 0 1 (dualNumerators080 0 1) := by
  apply integerChecks_of_simple 80 0 1 (dualNumerators080 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals080 0 1) 18767167
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck080_1_0 :
    integerResidualCheck 80 1 0 (dualNumerators080 1 0) ∧
    integerMassCheck 80 1 0 (dualNumerators080 1 0) := by
  apply integerChecks_of_simple 80 1 0 (dualNumerators080 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1197158056821, 305639293618, 0, 1965845541389, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 258120108696, 2314977922424, 88634461252, 1461232029476, 2173046324067, 0, 2157186795895, 171948459903, 1694290356000, 478755968067]) (branchResiduals080 1 0) 22176635
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck080_1_1 :
    integerResidualCheck 80 1 1 (dualNumerators080 1 1) ∧
    integerMassCheck 80 1 1 (dualNumerators080 1 1) := by
  apply integerChecks_of_simple 80 1 1 (dualNumerators080 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals080 1 1) 22176635
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck080_2_0 :
    integerResidualCheck 80 2 0 (dualNumerators080 2 0) ∧
    integerMassCheck 80 2 0 (dualNumerators080 2 0) := by
  apply integerChecks_of_simple 80 2 0 (dualNumerators080 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1197158056822, 305639293619, 0, 1965845541391, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 258120108697, 2314977922426, 88634461252, 1461232029477, 2173046324068, 0, 2157186795897, 171948459903, 1694290356001, 478755968068]) (branchResiduals080 2 0) 22681452
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck080_2_1 :
    integerResidualCheck 80 2 1 (dualNumerators080 2 1) ∧
    integerMassCheck 80 2 1 (dualNumerators080 2 1) := by
  apply integerChecks_of_simple 80 2 1 (dualNumerators080 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1011030237961, 258120108700, 0, 1660206247773, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 217988955954, 1955057368112, 74854042823, 1234047382516, 1835192545883, 0, 1821798773482, 145214820501, 1430871029971, 404321515912]) (branchResiduals080 2 1) 22681452
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck080_3_0 :
    integerResidualCheck 80 3 0 (dualNumerators080 3 0) ∧
    integerMassCheck 80 3 0 (dualNumerators080 3 0) := by
  apply integerChecks_of_simple 80 3 0 (dualNumerators080 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals080 3 0) 16360330
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck080_3_1 :
    integerResidualCheck 80 3 1 (dualNumerators080 3 1) ∧
    integerMassCheck 80 3 1 (dualNumerators080 3 1) := by
  apply integerChecks_of_simple 80 3 1 (dualNumerators080 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 796619754801, 203380245200, 0, 1308124173107, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 171759757642, 1540445837058, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 1127424369963, 318576531911]) (branchResiduals080 3 1) 16360330
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck080_4_0 :
    integerResidualCheck 80 4 0 (dualNumerators080 4 0) ∧
    integerMassCheck 80 4 0 (dualNumerators080 4 0) := by
  apply integerChecks_of_simple 80 4 0 (dualNumerators080 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 672765518030, 171759757645, 0, 1104743927909, 1000000000001, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 1, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 145055456673, 1300945445202, 49809804896, 821166860693, 1221184310279, 0, 1212271749715, 96629675624, 952138376845, 269045933435]) (branchResiduals080 4 0) 13760362
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck080_4_1 :
    integerResidualCheck 80 4 1 (dualNumerators080 4 1) ∧
    integerMassCheck 80 4 1 (dualNumerators080 4 1) := by
  apply integerChecks_of_simple 80 4 1 (dualNumerators080 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals080 4 1) 13760362
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck080_5_0 :
    integerResidualCheck 80 5 0 (dualNumerators080 5 0) ∧
    integerMassCheck 80 5 0 (dualNumerators080 5 0) := by
  apply integerChecks_of_simple 80 5 0 (dualNumerators080 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 796619754801, 203380245201, 0, 1308124173108, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 1, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 171759757642, 1540445837059, 58979649669, 972341366620, 1446000901875, 0, 1435447564017, 114418926712, 1127424369964, 318576531911]) (branchResiduals080 5 0) 17641130
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck080_5_1 :
    integerResidualCheck 80 5 1 (dualNumerators080 5 1) ∧
    integerMassCheck 80 5 1 (dualNumerators080 5 1) := by
  apply integerChecks_of_simple 80 5 1 (dualNumerators080 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275673, 1, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 145055456672, 1300945445201, 49809804896, 821166860692, 1221184310279, 0, 1212271749715, 96629675624, 952138376844, 269045933435]) (branchResiduals080 5 1) 17641130
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck080_6_0 :
    integerResidualCheck 80 6 0 (dualNumerators080 6 0) ∧
    integerMassCheck 80 6 0 (dualNumerators080 6 0) := by
  apply integerChecks_of_simple 80 6 0 (dualNumerators080 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 0, 70552396879, 187567711821, 1472638535954, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 1, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 877488274356, 957704271528, 103906894360, 5439901403, 1430871029972, 404321515913]) (branchResiduals080 6 0) 8962451
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck080_6_1 :
    integerResidualCheck 80 6 1 (dualNumerators080 6 1) ∧
    integerMassCheck 80 6 1 (dualNumerators080 6 1) := by
  apply integerChecks_of_simple 80 6 1 (dualNumerators080 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949782, 1, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 760187607595, 1097479190627, 0, 0]) (branchResiduals080 6 1) 8962451
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck080_7_0 :
    integerResidualCheck 80 7 0 (dualNumerators080 7 0) ∧
    integerMassCheck 80 7 0 (dualNumerators080 7 0) := by
  apply integerChecks_of_simple 80 7 0 (dualNumerators080 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals080 7 0) 10424794
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck080_7_1 :
    integerResidualCheck 80 7 1 (dualNumerators080 7 1) ∧
    integerMassCheck 80 7 1 (dualNumerators080 7 1) := by
  apply integerChecks_of_simple 80 7 1 (dualNumerators080 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 598579028412, 152819646809, 0, 982922770697, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 129060054349, 1157488961214, 44317230626, 730616014740, 1086523162035, 0, 1078593397950, 85974229952, 847145178002, 239377984034]) (branchResiduals080 7 1) 10424794
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck080_8_0 :
    integerResidualCheck 80 8 0 (dualNumerators080 8 0) ∧
    integerMassCheck 80 8 0 (dualNumerators080 8 0) := by
  apply integerChecks_of_simple 80 8 0 (dualNumerators080 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1197158056824, 305639293618, 0, 1965845541393, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 258120108697, 2314977922428, 88634461252, 1461232029479, 2173046324070, 0, 2157186795899, 171948459903, 1694290356003, 478755968068]) (branchResiduals080 8 0) 22681452
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck080_8_1 :
    integerResidualCheck 80 8 1 (dualNumerators080 8 1) ∧
    integerMassCheck 80 8 1 (dualNumerators080 8 1) := by
  apply integerChecks_of_simple 80 8 1 (dualNumerators080 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 184097183121, 1651095362762, 63216131150, 1042184205913, 1549866490725, 0, 1538555111396, 122637586316, 1208406751039, 341459739686]) (branchResiduals080 8 1) 22681452
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck080_9_0 :
    integerResidualCheck 80 9 0 (dualNumerators080 9 0) ∧
    integerMassCheck 80 9 0 (dualNumerators080 9 0) := by
  apply integerChecks_of_simple 80 9 0 (dualNumerators080 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 887477428322, 296619754801, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 703380245200, 296619754801, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 171759757642, 1540445837058, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 1127424369963, 318576531911]) (branchResiduals080 9 0) 16350530
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck080_9_1 :
    integerResidualCheck 80 9 1 (dualNumerators080 9 1) ∧
    integerMassCheck 80 9 1 (dualNumerators080 9 1) := by
  apply integerChecks_of_simple 80 9 1 (dualNumerators080 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals080 9 1) 16350530
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck080_10_0 :
    integerResidualCheck 80 10 0 (dualNumerators080 10 0) ∧
    integerMassCheck 80 10 0 (dualNumerators080 10 0) := by
  apply integerChecks_of_simple 80 10 0 (dualNumerators080 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals080 10 0) 10683139
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck080_10_1 :
    integerResidualCheck 80 10 1 (dualNumerators080 10 1) ∧
    integerMassCheck 80 10 1 (dualNumerators080 10 1) := by
  apply integerChecks_of_simple 80 10 1 (dualNumerators080 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 560661867464, 344525275673, 0, 844525275674, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 419928145920, 344525275674, 155474724327, 844525275674, 0, 0, 1184800741849, 1308901425339, 131302334422, 1177599090918, 45087194994, 743309684668, 1105400337064, 0, 1097332801829, 87467940020, 861863417206, 243536919859]) (branchResiduals080 10 1) 10683139
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck080_11_0 :
    integerResidualCheck 80 11 0 (dualNumerators080 11 0) ∧
    integerMassCheck 80 11 0 (dualNumerators080 11 0) := by
  apply integerChecks_of_simple 80 11 0 (dualNumerators080 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268434, 0, 562584914689, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 1, 0, 736368196709, 813498294019, 81606011717, 731892282302, 28022244838, 461976088268, 687019871017, 0, 682005798892, 54362397817, 535658687508, 151361183509]) (branchResiduals080 11 0) 15120968
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck080_11_1 :
    integerResidualCheck 80 11 1 (dualNumerators080 11 1) ∧
    integerMassCheck 80 11 1 (dualNumerators080 11 1) := by
  apply integerChecks_of_simple 80 11 1 (dualNumerators080 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 74415302107, 667401630730, 25553066146, 421269088530, 626483149703, 0, 621910892291, 49572257873, 488459149252, 138024000452]) (branchResiduals080 11 1) 15120968
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck080_12_0 :
    integerResidualCheck 80 12 0 (dualNumerators080 12 0) ∧
    integerMassCheck 80 12 0 (dualNumerators080 12 0) := by
  apply integerChecks_of_simple 80 12 0 (dualNumerators080 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 171759757642, 1540445837058, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 1127424369963, 318576531911]) (branchResiduals080 12 0) 16348076
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck080_12_1 :
    integerResidualCheck 80 12 1 (dualNumerators080 12 1) ∧
    integerMassCheck 80 12 1 (dualNumerators080 12 1) := by
  apply integerChecks_of_simple 80 12 1 (dualNumerators080 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals080 12 1) 16348076
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck080_13_0 :
    integerResidualCheck 80 13 0 (dualNumerators080 13 0) ∧
    integerMassCheck 80 13 0 (dualNumerators080 13 0) := by
  apply integerChecks_of_simple 80 13 0 (dualNumerators080 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals080 13 0) 13962901
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck080_13_1 :
    integerResidualCheck 80 13 1 (dualNumerators080 13 1) ∧
    integerMassCheck 80 13 1 (dualNumerators080 13 1) := by
  apply integerChecks_of_simple 80 13 1 (dualNumerators080 13 1)
    (![280984417303, 51728439727, 280984417303, 0, 1, 422262637837, 500000000000, 0, 393964356797, 280984417303, 422262637837, 0, 0, 52371963954, 0, 0, 414120121179, 52371963954, 946336320750, 799204942162, 435488332794, 654450712669, 435488332794, 515660508144, 422262637837, 0, 0, 52371963954, 500000000001, 0, 654450712669, 723000450937, 72527728336, 650472722601, 24904902448, 410583430346, 610592155140, 0, 606135874858, 48314837812, 476069188422, 134522966718]) (branchResiduals080 13 1) 13962901
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck080_14_0 :
    integerResidualCheck 80 14 0 (dualNumerators080 14 0) ∧
    integerMassCheck 80 14 0 (dualNumerators080 14 0) := by
  apply integerChecks_of_simple 80 14 0 (dualNumerators080 14 0)
    (![194975514542, 35894443005, 194975514542, 0, 1, 293008686654, 346950760497, 0, 273372466399, 194975514542, 0, 293008686654, 0, 0, 730242506439, 0, 0, 323699567405, 656664212341, 554569524952, 302186016501, 454124344937, 302186016501, 357817610917, 0, 293008686654, 0, 0, 59592178538, 323699567405, 454124344937, 501691112584, 50327101007, 451364011578, 17281549689, 284904466812, 423690825158, 0, 420598605493, 33525739445, 330345133945, 93345691214]) (branchResiduals080 14 0) 20161291
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck080_14_1 :
    integerResidualCheck 80 14 1 (dualNumerators080 14 1) ∧
    integerMassCheck 80 14 1 (dualNumerators080 14 1) := by
  apply integerChecks_of_simple 80 14 1 (dualNumerators080 14 1)
    (![561968834605, 103456879454, 561968834605, 0, 1, 844525275673, 1000000000000, 0, 787928713594, 561968834605, 672765518030, 171759757644, 0, 1104743927908, 0, 1000000000000, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 145055456672, 1300945445201, 49809804896, 821166860692, 1221184310279, 0, 1212271749715, 96629675624, 952138376844, 269045933435]) (branchResiduals080 14 1) 20161291
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck080_15_0 :
    integerResidualCheck 80 15 0 (dualNumerators080 15 0) ∧
    integerMassCheck 80 15 0 (dualNumerators080 15 0) := by
  apply integerChecks_of_simple 80 15 0 (dualNumerators080 15 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546385, 0, 844525275675, 602334801077, 221089960013, 684097183123, 0, 1184097183122, 1071829546385, 0, 0, 0, 2028622458796, 1713222941252, 933538524389, 1402919220983, 933538524389, 1105400337064, 905187143136, 1, 684097183123, 500000000000, 0, 0, 1402919220983, 1549866490727, 155474724326, 1394391766402, 53387620587, 880150903803, 1308901425339, 0, 1299348679593, 103570541391, 1020530044549, 288371380791]) (branchResiduals080 15 0) 12900283
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck080_15_1 :
    integerResidualCheck 80 15 1 (dualNumerators080 15 1) ∧
    integerMassCheck 80 15 1 (dualNumerators080 15 1) := by
  apply integerChecks_of_simple 80 15 1 (dualNumerators080 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals080 15 1) 12900283
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck080_16_0 :
    integerResidualCheck 80 16 0 (dualNumerators080 16 0) ∧
    integerMassCheck 80 16 0 (dualNumerators080 16 0) := by
  apply integerChecks_of_simple 80 16 0 (dualNumerators080 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals080 16 0) 10683060
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck080_16_1 :
    integerResidualCheck 80 16 1 (dualNumerators080 16 1) ∧
    integerMassCheck 80 16 1 (dualNumerators080 16 1) := by
  apply integerChecks_of_simple 80 16 1 (dualNumerators080 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 0, 0, 0, 0, 1184800741849, 1308901425339, 131302334422, 1177599090918, 45087194994, 743309684668, 1105400337064, 0, 1097332801829, 87467940020, 861863417206, 243536919859]) (branchResiduals080 16 1) 10683060
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck080_17_0 :
    integerResidualCheck 80 17 0 (dualNumerators080 17 0) ∧
    integerMassCheck 80 17 0 (dualNumerators080 17 0) := by
  apply integerChecks_of_simple 80 17 0 (dualNumerators080 17 0)
    (![602334801078, 110888140175, 602334801078, 0, 1, 905187143136, 1071829546386, 0, 844525275676, 602334801077, 0, 905187143137, 278910039987, 905187143136, 1071829546386, 0, 0, 1000000000001, 2028622458797, 1713222941254, 933538524390, 1402919220984, 933538524390, 1105400337065, 905187143136, 1, 1184097183123, 0, 0, 0, 1402919220984, 1549866490728, 155474724326, 1394391766403, 53387620587, 880150903803, 1308901425340, 0, 1299348679594, 103570541391, 1020530044550, 288371380791]) (branchResiduals080 17 0) 15120968
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck080_17_1 :
    integerResidualCheck 80 17 1 (dualNumerators080 17 1) ∧
    integerMassCheck 80 17 1 (dualNumerators080 17 1) := by
  apply integerChecks_of_simple 80 17 1 (dualNumerators080 17 1)
    (![508686963928, 93647837150, 508686963928, 0, 1, 764453421592, 905187143136, 0, 713222941253, 508686963927, 764453421593, 0, 0, 1000000000000, 905187143136, 0, 844525275674, 0, 1713222941251, 1446860076751, 788396879661, 1184800741848, 788396879661, 933538524388, 764453421592, 1, 0, 1000000000000, 0, 0, 1184800741848, 1308901425338, 131302334422, 1177599090917, 45087194994, 743309684668, 1105400337063, 0, 1097332801828, 87467940020, 861863417205, 243536919859]) (branchResiduals080 17 1) 15120968
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck080_18_0 :
    integerResidualCheck 80 18 0 (dualNumerators080 18 0) ∧
    integerMassCheck 80 18 0 (dualNumerators080 18 0) := by
  apply integerChecks_of_simple 80 18 0 (dualNumerators080 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 562515489548, 74022925577, 0, 476109064652, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 1, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 170971222814, 1097425476614, 0, 763999473637, 1027460955744, 43732116505, 953519106044, 33030453619, 835192545885, 236000526363]) (branchResiduals080 18 0) 13565580
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck080_18_1 :
    integerResidualCheck 80 18 1 (dualNumerators080 18 1) ∧
    integerMassCheck 80 18 1 (dualNumerators080 18 1) := by
  apply integerChecks_of_simple 80 18 1 (dualNumerators080 18 1)
    (![552774353318, 101764201348, 552774353318, 0, 1, 194169418432, 229915461414, 0, 83885421775, 59829007246, 99242781131, 94926637302, 0, 610559933212, 229915461414, 0, 0, 515633295912, 201500008915, 170171850577, 856726447141, 300936675152, 92726973504, 109797748126, 194169418432, 1, 94926637302, 515633295911, 0, 0, 300936675152, 799162766836, 15443069854, 138502830895, 92726973504, 0, 130011204269, 0, 195186313540, 105750361613, 101367709986, 28643494283]) (branchResiduals080 18 1) 13565580
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck080_19_0 :
    integerResidualCheck 80 19 0 (dualNumerators080 19 0) ∧
    integerMassCheck 80 19 0 (dualNumerators080 19 0) := by
  apply integerChecks_of_simple 80 19 0 (dualNumerators080 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 216703300504, 217988955956, 0, 1402086139076, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 1, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 230658067063, 840535005185, 0, 645216866088, 781448198910, 123201425731, 653752451905, 19962510160, 705341215054, 199308409586]) (branchResiduals080 19 0) 8248658
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck080_19_1 :
    integerResidualCheck 80 19 1 (dualNumerators080 19 1) ∧
    integerMassCheck 80 19 1 (dualNumerators080 19 1) := by
  apply integerChecks_of_simple 80 19 1 (dualNumerators080 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 1, 0, 0, 0, 0, 987477735649, 0, 76640541789, 687358931849, 186417556881, 273765914097, 645216866088, 0, 761601233763, 225876501886, 503065535987, 142151330101]) (branchResiduals080 19 1) 8248658
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck080_20_0 :
    integerResidualCheck 80 20 0 (dualNumerators080 20 0) ∧
    integerMassCheck 80 20 0 (dualNumerators080 20 0) := by
  apply integerChecks_of_simple 80 20 0 (dualNumerators080 20 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2011841128636, 209165476430, 0, 1345334280754, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605064, 2, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 176645531640, 1584264425996, 1060657349048, 0, 1487132967409, 0, 2232638358246, 1209625354629, 1159494400494, 327638566915]) (branchResiduals080 20 0) 35312013
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck080_20_1 :
    integerResidualCheck 80 20 1 (dualNumerators080 20 1) ∧
    integerMassCheck 80 20 1 (dualNumerators080 20 1) := by
  apply integerChecks_of_simple 80 20 1 (dualNumerators080 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals080 20 1) 35312013
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck080_21_0 :
    integerResidualCheck 80 21 0 (dualNumerators080 21 0) ∧
    integerMassCheck 80 21 0 (dualNumerators080 21 0) := by
  apply integerChecks_of_simple 80 21 0 (dualNumerators080 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770837, 1, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 759767979803, 549133445537, 851509250277, 798941670661, 1020530044549, 288371380791]) (branchResiduals080 21 0) 11182451
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck080_21_1 :
    integerResidualCheck 80 21 1 (dualNumerators080 21 1) ∧
    integerMassCheck 80 21 1 (dualNumerators080 21 1) := by
  apply integerChecks_of_simple 80 21 1 (dualNumerators080 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 860003851037, 963321782180, 3460174706, 161253783489, 102979506989, 127963650709, 0, 0, 180062781238, 50880376460]) (branchResiduals080 21 1) 11182451
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck080_22_0 :
    integerResidualCheck 80 22 0 (dualNumerators080 22 0) ∧
    integerMassCheck 80 22 0 (dualNumerators080 22 0) := by
  apply integerChecks_of_simple 80 22 0 (dualNumerators080 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 583695195717, 0, 612220343874, 0, 492945346072, 1, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554683, 1, 583695195717, 0, 0, 0, 801336080718, 763999473637, 510506833659, 253492639979, 460183470977, 0, 270741877993, 374474988096, 310954038967, 490382041752, 503065535987, 142151330101]) (branchResiduals080 22 0) 6465674
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck080_22_1 :
    integerResidualCheck 80 22 1 (dualNumerators080 22 1) ∧
    integerMassCheck 80 22 1 (dualNumerators080 22 1) := by
  apply integerChecks_of_simple 80 22 1 (dualNumerators080 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 9522456419, 111749239332, 1534493418, 71511669319, 45668611868, 56748400418, 0, 0, 79852948501, 22564063785]) (branchResiduals080 22 1) 6465674
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck080_23_0 :
    integerResidualCheck 80 23 0 (dualNumerators080 23 0) ∧
    integerMassCheck 80 23 0 (dualNumerators080 23 0) := by
  apply integerChecks_of_simple 80 23 0 (dualNumerators080 23 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2011841128638, 209165476428, 0, 1345334280754, 2629887664754, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 1176645531640, 584264425996, 1060657349048, 0, 1487132967409, 0, 2232638358246, 1209625354629, 1159494400494, 327638566915]) (branchResiduals080 23 0) 35297932
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck080_23_1 :
    integerResidualCheck 80 23 1 (dualNumerators080 23 1) ∧
    integerMassCheck 80 23 1 (dualNumerators080 23 1) := by
  apply integerChecks_of_simple 80 23 1 (dualNumerators080 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 160334187224, 1881575790198, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals080 23 1) 35297932
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck080_24_0 :
    integerResidualCheck 80 24 0 (dualNumerators080 24 0) ∧
    integerMassCheck 80 24 0 (dualNumerators080 24 0) := by
  apply integerChecks_of_simple 80 24 0 (dualNumerators080 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 276221246109, 150663467366, 0, 969054410724, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713474, 1, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 512185690040, 559007382209, 569308312247, 737522866658, 835192545885, 236000526363]) (branchResiduals080 24 0) 9356857
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck080_24_1 :
    integerResidualCheck 80 24 1 (dualNumerators080 24 1) ∧
    integerMassCheck 80 24 1 (dualNumerators080 24 1) := by
  apply integerChecks_of_simple 80 24 1 (dualNumerators080 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 395480180778, 20824623507, 0, 133942179966, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 1, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 690777049383, 178822020994, 66021086067, 82038644814, 0, 0, 115439864933, 32619865948]) (branchResiduals080 24 1) 9356857
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck080_25_0 :
    integerResidualCheck 80 25 0 (dualNumerators080 25 0) ∧
    integerMassCheck 80 25 0 (dualNumerators080 25 0) := by
  apply integerChecks_of_simple 80 25 0 (dualNumerators080 25 0)
    (![34423495944, 6337268637, 34423495944, 0, 1, 22181646803, 26265225496, 0, 631959902239, 450728300227, 377366713580, 137760279295, 0, 886062219380, 609960421212, 0, 0, 748301940086, 1518022121617, 1282008050738, 53351822857, 34378591088, 698568688945, 827173216796, 515126992874, 1, 137760279295, 748301940085, 0, 0, 798378064725, 1159768101884, 638738616250, 521029485635, 53351822857, 0, 457056897559, 522396578403, 34378591088, 0, 763664612251, 215788863711]) (branchResiduals080 25 0) 8671199
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck080_25_1 :
    integerResidualCheck 80 25 1 (dualNumerators080 25 1) ∧
    integerMassCheck 80 25 1 (dualNumerators080 25 1) := by
  apply integerChecks_of_simple 80 25 1 (dualNumerators080 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 1, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 415529968297, 599898615461, 0, 0]) (branchResiduals080 25 1) 8671199
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck080_26_0 :
    integerResidualCheck 80 26 0 (dualNumerators080 26 0) ∧
    integerMassCheck 80 26 0 (dualNumerators080 26 0) := by
  apply integerChecks_of_simple 80 26 0 (dualNumerators080 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0]) (branchResiduals080 26 0) 15099566
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck080_26_1 :
    integerResidualCheck 80 26 1 (dualNumerators080 26 1) ∧
    integerMassCheck 80 26 1 (dualNumerators080 26 1) := by
  apply integerChecks_of_simple 80 26 1 (dualNumerators080 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 1025837005087, 204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals080 26 1) 15099566
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck080_27_0 :
    integerResidualCheck 80 27 0 (dualNumerators080 27 0) ∧
    integerMassCheck 80 27 0 (dualNumerators080 27 0) := by
  apply integerChecks_of_simple 80 27 0 (dualNumerators080 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000001, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312724, 1, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 286173900105, 455299762271, 595678484088, 168320989550]) (branchResiduals080 27 0) 7338775
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck080_27_1 :
    integerResidualCheck 80 27 1 (dualNumerators080 27 1) ∧
    integerMassCheck 80 27 1 (dualNumerators080 27 1) := by
  apply integerChecks_of_simple 80 27 1 (dualNumerators080 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 234337221023, 181967583262, 0, 1170399780726, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 1, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 530765167249, 1001172773960, 0, 377837583379, 916671368281, 377088943834, 621055226706, 24161639382, 413046270426, 116714568052]) (branchResiduals080 27 1) 7338775
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck080_28_0 :
    integerResidualCheck 80 28 0 (dualNumerators080 28 0) ∧
    integerMassCheck 80 28 0 (dualNumerators080 28 0) := by
  apply integerChecks_of_simple 80 28 0 (dualNumerators080 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 1, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 450383711774, 395438493575, 503065535987, 142151330101]) (branchResiduals080 28 0) 10335557
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck080_28_1 :
    integerResidualCheck 80 28 1 (dualNumerators080 28 1) ∧
    integerMassCheck 80 28 1 (dualNumerators080 28 1) := by
  apply integerChecks_of_simple 80 28 1 (dualNumerators080 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 426731607120, 507685338329, 2156352207, 100492021777, 456143077212, 332995651238, 0, 0, 112213633330, 31708229033]) (branchResiduals080 28 1) 10335557
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck080_29_0 :
    integerResidualCheck 80 29 0 (dualNumerators080 29 0) ∧
    integerMassCheck 80 29 0 (dualNumerators080 29 0) := by
  apply integerChecks_of_simple 80 29 0 (dualNumerators080 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210956, 1, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0]) (branchResiduals080 29 0) 40352153
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck080_29_1 :
    integerResidualCheck 80 29 1 (dualNumerators080 29 1) ∧
    integerMassCheck 80 29 1 (dualNumerators080 29 1) := by
  apply integerChecks_of_simple 80 29 1 (dualNumerators080 29 1)
    (![814189538844, 149890000629, 814189538844, 0, 1, 31000670773, 36707806937, 0, 1141563866996, 814189538843, 0, 31000670773, 217847644751, 1382723230032, 36707806937, 0, 0, 1351722559261, 2742134741776, 2315802098733, 1261885083355, 48046900821, 1261885083355, 1494194572624, 31000670773, 1, 248848315523, 1351722559260, 0, 0, 48046900821, 2094989499358, 210158692266, 1884830807092, 72165251132, 1189719832223, 1769271584479, 0, 0, 48046900821, 1379473483620, 389798100860]) (branchResiduals080 29 1) 40352153
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck080_30_0 :
    integerResidualCheck 80 30 0 (dualNumerators080 30 0) ∧
    integerMassCheck 80 30 0 (dualNumerators080 30 0) := by
  apply integerChecks_of_simple 80 30 0 (dualNumerators080 30 0)
    (![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 77683757550, 37915592377, 0, 243869815754, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 1, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 32020676104, 287180873334, 10995405936, 181270795848, 269573776534, 0, 163293901896, 15869656905, 269573776534, 0]) (branchResiduals080 30 0) 7680628
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck080_30_1 :
    integerResidualCheck 80 30 1 (dualNumerators080 30 1) ∧
    integerMassCheck 80 30 1 (dualNumerators080 30 1) := by
  apply integerChecks_of_simple 80 30 1 (dualNumerators080 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714054, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 90749849645, 813899774996, 31162097647, 513739854055, 763999473637, 0, 862736028146, 65914760940, 536287180313, 227712293325]) (branchResiduals080 30 1) 7680628
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck080_31_0 :
    integerResidualCheck 80 31 0 (dualNumerators080 31 0) ∧
    integerMassCheck 80 31 0 (dualNumerators080 31 0) := by
  apply integerChecks_of_simple 80 31 0 (dualNumerators080 31 0)
    (![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1719079079316, 0, 231835083176, 1259308150412, 2035556695381, 0, 0, 1259308150414, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079315, 2, 231835083174, 1259308150413, 0, 0, 2664343059941, 1951759503826, 195790587527, 1755968916300, 939253060812, 1341759948741, 1648310233018, 0, 1640459045760, 1023884014182, 1648310233018, 0]) (branchResiduals080 31 0) 32891612
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck080_31_1 :
    integerResidualCheck 80 31 1 (dualNumerators080 31 1) ∧
    integerMassCheck 80 31 1 (dualNumerators080 31 1) := by
  apply integerChecks_of_simple 80 31 1 (dualNumerators080 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 274671058114, 217988955956, 0, 1402086139076, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 1, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 741061026801, 808805463926, 725570984152, 37986262977, 845258320866, 704608169862]) (branchResiduals080 31 1) 32891612
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck080_32_0 :
    integerResidualCheck 80 32 0 (dualNumerators080 32 0) ∧
    integerMassCheck 80 32 0 (dualNumerators080 32 0) := by
  apply integerChecks_of_simple 80 32 0 (dualNumerators080 32 0)
    (![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 979882959195, 1099655708204, 1160276651773, 0, 382837210862, 2079538667397, 0, 979882959196, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 180393692578, 979882959195, 0, 0, 3223007296772, 1518687763292, 152347032953, 1366340730340, 52313619645, 862444872157, 1282570201956, 0, 3029568551736, 193438745037, 0, 1282570201956]) (branchResiduals080 32 0) 67647473
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck080_32_1 :
    integerResidualCheck 80 32 1 (dualNumerators080 32 1) ∧
    integerMassCheck 80 32 1 (dualNumerators080 32 1) := by
  apply integerChecks_of_simple 80 32 1 (dualNumerators080 32 1)
    (![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1307998858623, 638403098873, 0, 4106153599144, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957494, 2, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 539147553060, 4835402745519, 185134947997, 3052143736978, 4538943572529, 0, 2749458111138, 267205060270, 4538943572529, 0]) (branchResiduals080 32 1) 67647473
    branchSparseDots080 branchIntegerCurvature080 branchDots080
    branchIntegerCurvature080_entry rfl
    (congrFun (congrFun branchResiduals080_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks080 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 80 j s (dualNumerators080 j s) ∧
    integerMassCheck 80 j s (dualNumerators080 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck080_0_0
    · exact integerCheck080_0_1
  · fin_cases s
    · exact integerCheck080_1_0
    · exact integerCheck080_1_1
  · fin_cases s
    · exact integerCheck080_2_0
    · exact integerCheck080_2_1
  · fin_cases s
    · exact integerCheck080_3_0
    · exact integerCheck080_3_1
  · fin_cases s
    · exact integerCheck080_4_0
    · exact integerCheck080_4_1
  · fin_cases s
    · exact integerCheck080_5_0
    · exact integerCheck080_5_1
  · fin_cases s
    · exact integerCheck080_6_0
    · exact integerCheck080_6_1
  · fin_cases s
    · exact integerCheck080_7_0
    · exact integerCheck080_7_1
  · fin_cases s
    · exact integerCheck080_8_0
    · exact integerCheck080_8_1
  · fin_cases s
    · exact integerCheck080_9_0
    · exact integerCheck080_9_1
  · fin_cases s
    · exact integerCheck080_10_0
    · exact integerCheck080_10_1
  · fin_cases s
    · exact integerCheck080_11_0
    · exact integerCheck080_11_1
  · fin_cases s
    · exact integerCheck080_12_0
    · exact integerCheck080_12_1
  · fin_cases s
    · exact integerCheck080_13_0
    · exact integerCheck080_13_1
  · fin_cases s
    · exact integerCheck080_14_0
    · exact integerCheck080_14_1
  · fin_cases s
    · exact integerCheck080_15_0
    · exact integerCheck080_15_1
  · fin_cases s
    · exact integerCheck080_16_0
    · exact integerCheck080_16_1
  · fin_cases s
    · exact integerCheck080_17_0
    · exact integerCheck080_17_1
  · fin_cases s
    · exact integerCheck080_18_0
    · exact integerCheck080_18_1
  · fin_cases s
    · exact integerCheck080_19_0
    · exact integerCheck080_19_1
  · fin_cases s
    · exact integerCheck080_20_0
    · exact integerCheck080_20_1
  · fin_cases s
    · exact integerCheck080_21_0
    · exact integerCheck080_21_1
  · fin_cases s
    · exact integerCheck080_22_0
    · exact integerCheck080_22_1
  · fin_cases s
    · exact integerCheck080_23_0
    · exact integerCheck080_23_1
  · fin_cases s
    · exact integerCheck080_24_0
    · exact integerCheck080_24_1
  · fin_cases s
    · exact integerCheck080_25_0
    · exact integerCheck080_25_1
  · fin_cases s
    · exact integerCheck080_26_0
    · exact integerCheck080_26_1
  · fin_cases s
    · exact integerCheck080_27_0
    · exact integerCheck080_27_1
  · fin_cases s
    · exact integerCheck080_28_0
    · exact integerCheck080_28_1
  · fin_cases s
    · exact integerCheck080_29_0
    · exact integerCheck080_29_1
  · fin_cases s
    · exact integerCheck080_30_0
    · exact integerCheck080_30_1
  · fin_cases s
    · exact integerCheck080_31_0
    · exact integerCheck080_31_1
  · fin_cases s
    · exact integerCheck080_32_0
    · exact integerCheck080_32_1

end ElevenSquare.Tasks.T06
