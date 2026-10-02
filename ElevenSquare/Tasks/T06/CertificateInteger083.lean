import ElevenSquare.Tasks.T06.DataIntegral
import ElevenSquare.Tasks.T06.CertificateSimple
import ElevenSquare.Tasks.T06.DataDual083
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
import ElevenSquare.Tasks.T06.SparseColumn48
import ElevenSquare.Tasks.T06.SparseColumn55
import ElevenSquare.Tasks.T06.SparseColumn56

namespace ElevenSquare.Tasks.T06
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def branchIntegerMatrix083 : Fin 42 → Fin 33 → ℤ :=
  ![roundedGradientLiteral00, roundedGradientLiteral01, roundedGradientLiteral02, roundedGradientLiteral03, roundedGradientLiteral04, roundedGradientLiteral05, roundedGradientLiteral06, roundedGradientLiteral07, roundedGradientLiteral08, roundedGradientLiteral09, roundedGradientLiteral10, roundedGradientLiteral11, roundedGradientLiteral12, roundedGradientLiteral13, roundedGradientLiteral14, roundedGradientLiteral15, roundedGradientLiteral16, roundedGradientLiteral17, roundedGradientLiteral18, roundedGradientLiteral19, roundedGradientLiteral20, roundedGradientLiteral21, roundedGradientLiteral22, roundedGradientLiteral23, roundedGradientLiteral24, roundedGradientLiteral25, roundedGradientLiteral26, roundedGradientLiteral27, roundedGradientLiteral45, roundedGradientLiteral43, roundedGradientLiteral30, roundedGradientLiteral31, roundedGradientLiteral32, roundedGradientLiteral33, roundedGradientLiteral54, roundedGradientLiteral55, roundedGradientLiteral50, roundedGradientLiteral51, roundedGradientLiteral38, roundedGradientLiteral39, roundedGradientLiteral40, roundedGradientLiteral41]

theorem branchIntegerMatrix083_eq :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = branchIntegerMatrix083 := by
  change roundedGradients ∘ branchRows 83 = branchIntegerMatrix083
  rw [show branchRows 83 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty,
    roundedGradientLiteral00_eq, roundedGradientLiteral01_eq, roundedGradientLiteral02_eq, roundedGradientLiteral03_eq, roundedGradientLiteral04_eq, roundedGradientLiteral05_eq, roundedGradientLiteral06_eq, roundedGradientLiteral07_eq, roundedGradientLiteral08_eq, roundedGradientLiteral09_eq, roundedGradientLiteral10_eq, roundedGradientLiteral11_eq, roundedGradientLiteral12_eq, roundedGradientLiteral13_eq, roundedGradientLiteral14_eq, roundedGradientLiteral15_eq, roundedGradientLiteral16_eq, roundedGradientLiteral17_eq, roundedGradientLiteral18_eq, roundedGradientLiteral19_eq, roundedGradientLiteral20_eq, roundedGradientLiteral21_eq, roundedGradientLiteral22_eq, roundedGradientLiteral23_eq, roundedGradientLiteral24_eq, roundedGradientLiteral25_eq, roundedGradientLiteral26_eq, roundedGradientLiteral27_eq, roundedGradientLiteral30_eq, roundedGradientLiteral31_eq, roundedGradientLiteral32_eq, roundedGradientLiteral33_eq, roundedGradientLiteral38_eq, roundedGradientLiteral39_eq, roundedGradientLiteral40_eq, roundedGradientLiteral41_eq, roundedGradientLiteral43_eq, roundedGradientLiteral45_eq, roundedGradientLiteral50_eq, roundedGradientLiteral51_eq, roundedGradientLiteral54_eq, roundedGradientLiteral55_eq, branchIntegerMatrix083]

theorem branchColumn083_0 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 0) = sparseColumn00 := by
  change (fun row : Fin 33 → ℤ => row 0) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_0 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 0) = sparseDot00 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 0) i) = _
  rw [branchColumn083_0]
  exact sparseColumn00_sum n

theorem branchColumn083_1 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 1) = sparseColumn01 := by
  change (fun row : Fin 33 → ℤ => row 1) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_1 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 1) = sparseDot01 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 1) i) = _
  rw [branchColumn083_1]
  exact sparseColumn01_sum n

theorem branchColumn083_2 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 2) = sparseColumn02 := by
  change (fun row : Fin 33 → ℤ => row 2) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_2 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 2) = sparseDot02 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 2) i) = _
  rw [branchColumn083_2]
  exact sparseColumn02_sum n

theorem branchColumn083_3 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 3) = sparseColumn03 := by
  change (fun row : Fin 33 → ℤ => row 3) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_3 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 3) = sparseDot03 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 3) i) = _
  rw [branchColumn083_3]
  exact sparseColumn03_sum n

theorem branchColumn083_4 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 4) = sparseColumn04 := by
  change (fun row : Fin 33 → ℤ => row 4) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_4 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 4) = sparseDot04 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 4) i) = _
  rw [branchColumn083_4]
  exact sparseColumn04_sum n

theorem branchColumn083_5 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 5) = sparseColumn05 := by
  change (fun row : Fin 33 → ℤ => row 5) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_5 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 5) = sparseDot05 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 5) i) = _
  rw [branchColumn083_5]
  exact sparseColumn05_sum n

theorem branchColumn083_6 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 6) = sparseColumn06 := by
  change (fun row : Fin 33 → ℤ => row 6) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_6 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 6) = sparseDot06 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 6) i) = _
  rw [branchColumn083_6]
  exact sparseColumn06_sum n

theorem branchColumn083_7 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 7) = sparseColumn07 := by
  change (fun row : Fin 33 → ℤ => row 7) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_7 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 7) = sparseDot07 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 7) i) = _
  rw [branchColumn083_7]
  exact sparseColumn07_sum n

theorem branchColumn083_8 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 8) = sparseColumn08 := by
  change (fun row : Fin 33 → ℤ => row 8) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_8 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 8) = sparseDot08 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 8) i) = _
  rw [branchColumn083_8]
  exact sparseColumn08_sum n

theorem branchColumn083_9 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 9) = sparseColumn09 := by
  change (fun row : Fin 33 → ℤ => row 9) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_9 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 9) = sparseDot09 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 9) i) = _
  rw [branchColumn083_9]
  exact sparseColumn09_sum n

theorem branchColumn083_10 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 10) = sparseColumn10 := by
  change (fun row : Fin 33 → ℤ => row 10) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_10 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 10) = sparseDot10 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 10) i) = _
  rw [branchColumn083_10]
  exact sparseColumn10_sum n

theorem branchColumn083_11 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 11) = sparseColumn11 := by
  change (fun row : Fin 33 → ℤ => row 11) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_11 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 11) = sparseDot11 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 11) i) = _
  rw [branchColumn083_11]
  exact sparseColumn11_sum n

theorem branchColumn083_12 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 12) = sparseColumn35 := by
  change (fun row : Fin 33 → ℤ => row 12) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_12 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 12) = sparseDot35 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 12) i) = _
  rw [branchColumn083_12]
  exact sparseColumn35_sum n

theorem branchColumn083_13 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 13) = sparseColumn36 := by
  change (fun row : Fin 33 → ℤ => row 13) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_13 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 13) = sparseDot36 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 13) i) = _
  rw [branchColumn083_13]
  exact sparseColumn36_sum n

theorem branchColumn083_14 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 14) = sparseColumn41 := by
  change (fun row : Fin 33 → ℤ => row 14) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_14 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 14) = sparseDot41 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 14) i) = _
  rw [branchColumn083_14]
  exact sparseColumn41_sum n

theorem branchColumn083_15 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 15) = sparseColumn38 := by
  change (fun row : Fin 33 → ℤ => row 15) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_15 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 15) = sparseDot38 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 15) i) = _
  rw [branchColumn083_15]
  exact sparseColumn38_sum n

theorem branchColumn083_16 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 16) = sparseColumn39 := by
  change (fun row : Fin 33 → ℤ => row 16) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_16 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 16) = sparseDot39 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 16) i) = _
  rw [branchColumn083_16]
  exact sparseColumn39_sum n

theorem branchColumn083_17 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 17) = sparseColumn17 := by
  change (fun row : Fin 33 → ℤ => row 17) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_17 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 17) = sparseDot17 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 17) i) = _
  rw [branchColumn083_17]
  exact sparseColumn17_sum n

theorem branchColumn083_18 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 18) = sparseColumn18 := by
  change (fun row : Fin 33 → ℤ => row 18) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_18 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 18) = sparseDot18 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 18) i) = _
  rw [branchColumn083_18]
  exact sparseColumn18_sum n

theorem branchColumn083_19 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 19) = sparseColumn19 := by
  change (fun row : Fin 33 → ℤ => row 19) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_19 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 19) = sparseDot19 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 19) i) = _
  rw [branchColumn083_19]
  exact sparseColumn19_sum n

theorem branchColumn083_20 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 20) = sparseColumn55 := by
  change (fun row : Fin 33 → ℤ => row 20) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_20 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 20) = sparseDot55 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 20) i) = _
  rw [branchColumn083_20]
  exact sparseColumn55_sum n

theorem branchColumn083_21 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 21) = sparseColumn21 := by
  change (fun row : Fin 33 → ℤ => row 21) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_21 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 21) = sparseDot21 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 21) i) = _
  rw [branchColumn083_21]
  exact sparseColumn21_sum n

theorem branchColumn083_22 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 22) = sparseColumn22 := by
  change (fun row : Fin 33 → ℤ => row 22) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_22 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 22) = sparseDot22 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 22) i) = _
  rw [branchColumn083_22]
  exact sparseColumn22_sum n

theorem branchColumn083_23 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 23) = sparseColumn47 := by
  change (fun row : Fin 33 → ℤ => row 23) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_23 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 23) = sparseDot47 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 23) i) = _
  rw [branchColumn083_23]
  exact sparseColumn47_sum n

theorem branchColumn083_24 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 24) = sparseColumn24 := by
  change (fun row : Fin 33 → ℤ => row 24) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_24 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 24) = sparseDot24 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 24) i) = _
  rw [branchColumn083_24]
  exact sparseColumn24_sum n

theorem branchColumn083_25 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 25) = sparseColumn25 := by
  change (fun row : Fin 33 → ℤ => row 25) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_25 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 25) = sparseDot25 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 25) i) = _
  rw [branchColumn083_25]
  exact sparseColumn25_sum n

theorem branchColumn083_26 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 26) = sparseColumn56 := by
  change (fun row : Fin 33 → ℤ => row 26) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_26 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 26) = sparseDot56 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 26) i) = _
  rw [branchColumn083_26]
  exact sparseColumn56_sum n

theorem branchColumn083_27 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 27) = sparseColumn27 := by
  change (fun row : Fin 33 → ℤ => row 27) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_27 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 27) = sparseDot27 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 27) i) = _
  rw [branchColumn083_27]
  exact sparseColumn27_sum n

theorem branchColumn083_28 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 28) = sparseColumn28 := by
  change (fun row : Fin 33 → ℤ => row 28) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_28 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 28) = sparseDot28 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 28) i) = _
  rw [branchColumn083_28]
  exact sparseColumn28_sum n

theorem branchColumn083_29 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 29) = sparseColumn48 := by
  change (fun row : Fin 33 → ℤ => row 29) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_29 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 29) = sparseDot48 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 29) i) = _
  rw [branchColumn083_29]
  exact sparseColumn48_sum n

theorem branchColumn083_30 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 30) = sparseColumn30 := by
  change (fun row : Fin 33 → ℤ => row 30) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_30 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 30) = sparseDot30 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 30) i) = _
  rw [branchColumn083_30]
  exact sparseColumn30_sum n

theorem branchColumn083_31 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 31) = sparseColumn31 := by
  change (fun row : Fin 33 → ℤ => row 31) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_31 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 31) = sparseDot31 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 31) i) = _
  rw [branchColumn083_31]
  exact sparseColumn31_sum n

theorem branchColumn083_32 :
    (fun i : Fin 42 => roundedGradients (branchRows 83 i) 32) = sparseColumn32 := by
  change (fun row : Fin 33 → ℤ => row 32) ∘ (fun i : Fin 42 => roundedGradients (branchRows 83 i)) = _
  rw [branchIntegerMatrix083_eq]
  simp only [branchIntegerMatrix083, certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchDot083_32 (n : Fin 42 → ℕ) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) 32) = sparseDot32 n := by
  change (∑ i : Fin 42, (n i : ℤ) * (fun i : Fin 42 => roundedGradients (branchRows 83 i) 32) i) = _
  rw [branchColumn083_32]
  exact sparseColumn32_sum n

def branchSparseDots083 : Fin 33 → (Fin 42 → ℕ) → ℤ :=
  ![sparseDot00, sparseDot01, sparseDot02, sparseDot03, sparseDot04, sparseDot05, sparseDot06, sparseDot07, sparseDot08, sparseDot09, sparseDot10, sparseDot11, sparseDot35, sparseDot36, sparseDot41, sparseDot38, sparseDot39, sparseDot17, sparseDot18, sparseDot19, sparseDot55, sparseDot21, sparseDot22, sparseDot47, sparseDot24, sparseDot25, sparseDot56, sparseDot27, sparseDot28, sparseDot48, sparseDot30, sparseDot31, sparseDot32]

-- Keep vector indexing opaque when transporting the large matrix sum.
private theorem branchSparseDot083_0 :
    branchSparseDots083 0 = sparseDot00 := rfl

private theorem branchSparseDot083_1 :
    branchSparseDots083 1 = sparseDot01 := rfl

private theorem branchSparseDot083_2 :
    branchSparseDots083 2 = sparseDot02 := rfl

private theorem branchSparseDot083_3 :
    branchSparseDots083 3 = sparseDot03 := rfl

private theorem branchSparseDot083_4 :
    branchSparseDots083 4 = sparseDot04 := rfl

private theorem branchSparseDot083_5 :
    branchSparseDots083 5 = sparseDot05 := rfl

private theorem branchSparseDot083_6 :
    branchSparseDots083 6 = sparseDot06 := rfl

private theorem branchSparseDot083_7 :
    branchSparseDots083 7 = sparseDot07 := rfl

private theorem branchSparseDot083_8 :
    branchSparseDots083 8 = sparseDot08 := rfl

private theorem branchSparseDot083_9 :
    branchSparseDots083 9 = sparseDot09 := rfl

private theorem branchSparseDot083_10 :
    branchSparseDots083 10 = sparseDot10 := rfl

private theorem branchSparseDot083_11 :
    branchSparseDots083 11 = sparseDot11 := rfl

private theorem branchSparseDot083_12 :
    branchSparseDots083 12 = sparseDot35 := rfl

private theorem branchSparseDot083_13 :
    branchSparseDots083 13 = sparseDot36 := rfl

private theorem branchSparseDot083_14 :
    branchSparseDots083 14 = sparseDot41 := rfl

private theorem branchSparseDot083_15 :
    branchSparseDots083 15 = sparseDot38 := rfl

private theorem branchSparseDot083_16 :
    branchSparseDots083 16 = sparseDot39 := rfl

private theorem branchSparseDot083_17 :
    branchSparseDots083 17 = sparseDot17 := rfl

private theorem branchSparseDot083_18 :
    branchSparseDots083 18 = sparseDot18 := rfl

private theorem branchSparseDot083_19 :
    branchSparseDots083 19 = sparseDot19 := rfl

private theorem branchSparseDot083_20 :
    branchSparseDots083 20 = sparseDot55 := rfl

private theorem branchSparseDot083_21 :
    branchSparseDots083 21 = sparseDot21 := rfl

private theorem branchSparseDot083_22 :
    branchSparseDots083 22 = sparseDot22 := rfl

private theorem branchSparseDot083_23 :
    branchSparseDots083 23 = sparseDot47 := rfl

private theorem branchSparseDot083_24 :
    branchSparseDots083 24 = sparseDot24 := rfl

private theorem branchSparseDot083_25 :
    branchSparseDots083 25 = sparseDot25 := rfl

private theorem branchSparseDot083_26 :
    branchSparseDots083 26 = sparseDot56 := rfl

private theorem branchSparseDot083_27 :
    branchSparseDots083 27 = sparseDot27 := rfl

private theorem branchSparseDot083_28 :
    branchSparseDots083 28 = sparseDot28 := rfl

private theorem branchSparseDot083_29 :
    branchSparseDots083 29 = sparseDot48 := rfl

private theorem branchSparseDot083_30 :
    branchSparseDots083 30 = sparseDot30 := rfl

private theorem branchSparseDot083_31 :
    branchSparseDots083 31 = sparseDot31 := rfl

private theorem branchSparseDot083_32 :
    branchSparseDots083 32 = sparseDot32 := rfl

theorem branchDots083 (n : Fin 42 → ℕ) (k : Fin 33) :
    (∑ i : Fin 42, (n i : ℤ) * roundedGradients (branchRows 83 i) k) = branchSparseDots083 k n := by
  fin_cases k
  · calc
      _ = sparseDot00 n := branchDot083_0 n
      _ = _ := congrFun branchSparseDot083_0.symm n
  · calc
      _ = sparseDot01 n := branchDot083_1 n
      _ = _ := congrFun branchSparseDot083_1.symm n
  · calc
      _ = sparseDot02 n := branchDot083_2 n
      _ = _ := congrFun branchSparseDot083_2.symm n
  · calc
      _ = sparseDot03 n := branchDot083_3 n
      _ = _ := congrFun branchSparseDot083_3.symm n
  · calc
      _ = sparseDot04 n := branchDot083_4 n
      _ = _ := congrFun branchSparseDot083_4.symm n
  · calc
      _ = sparseDot05 n := branchDot083_5 n
      _ = _ := congrFun branchSparseDot083_5.symm n
  · calc
      _ = sparseDot06 n := branchDot083_6 n
      _ = _ := congrFun branchSparseDot083_6.symm n
  · calc
      _ = sparseDot07 n := branchDot083_7 n
      _ = _ := congrFun branchSparseDot083_7.symm n
  · calc
      _ = sparseDot08 n := branchDot083_8 n
      _ = _ := congrFun branchSparseDot083_8.symm n
  · calc
      _ = sparseDot09 n := branchDot083_9 n
      _ = _ := congrFun branchSparseDot083_9.symm n
  · calc
      _ = sparseDot10 n := branchDot083_10 n
      _ = _ := congrFun branchSparseDot083_10.symm n
  · calc
      _ = sparseDot11 n := branchDot083_11 n
      _ = _ := congrFun branchSparseDot083_11.symm n
  · calc
      _ = sparseDot35 n := branchDot083_12 n
      _ = _ := congrFun branchSparseDot083_12.symm n
  · calc
      _ = sparseDot36 n := branchDot083_13 n
      _ = _ := congrFun branchSparseDot083_13.symm n
  · calc
      _ = sparseDot41 n := branchDot083_14 n
      _ = _ := congrFun branchSparseDot083_14.symm n
  · calc
      _ = sparseDot38 n := branchDot083_15 n
      _ = _ := congrFun branchSparseDot083_15.symm n
  · calc
      _ = sparseDot39 n := branchDot083_16 n
      _ = _ := congrFun branchSparseDot083_16.symm n
  · calc
      _ = sparseDot17 n := branchDot083_17 n
      _ = _ := congrFun branchSparseDot083_17.symm n
  · calc
      _ = sparseDot18 n := branchDot083_18 n
      _ = _ := congrFun branchSparseDot083_18.symm n
  · calc
      _ = sparseDot19 n := branchDot083_19 n
      _ = _ := congrFun branchSparseDot083_19.symm n
  · calc
      _ = sparseDot55 n := branchDot083_20 n
      _ = _ := congrFun branchSparseDot083_20.symm n
  · calc
      _ = sparseDot21 n := branchDot083_21 n
      _ = _ := congrFun branchSparseDot083_21.symm n
  · calc
      _ = sparseDot22 n := branchDot083_22 n
      _ = _ := congrFun branchSparseDot083_22.symm n
  · calc
      _ = sparseDot47 n := branchDot083_23 n
      _ = _ := congrFun branchSparseDot083_23.symm n
  · calc
      _ = sparseDot24 n := branchDot083_24 n
      _ = _ := congrFun branchSparseDot083_24.symm n
  · calc
      _ = sparseDot25 n := branchDot083_25 n
      _ = _ := congrFun branchSparseDot083_25.symm n
  · calc
      _ = sparseDot56 n := branchDot083_26 n
      _ = _ := congrFun branchSparseDot083_26.symm n
  · calc
      _ = sparseDot27 n := branchDot083_27 n
      _ = _ := congrFun branchSparseDot083_27.symm n
  · calc
      _ = sparseDot28 n := branchDot083_28 n
      _ = _ := congrFun branchSparseDot083_28.symm n
  · calc
      _ = sparseDot48 n := branchDot083_29 n
      _ = _ := congrFun branchSparseDot083_29.symm n
  · calc
      _ = sparseDot30 n := branchDot083_30 n
      _ = _ := congrFun branchSparseDot083_30.symm n
  · calc
      _ = sparseDot31 n := branchDot083_31 n
      _ = _ := congrFun branchSparseDot083_31.symm n
  · calc
      _ = sparseDot32 n := branchDot083_32 n
      _ = _ := congrFun branchSparseDot083_32.symm n

def branchIntegerCurvature083 : Fin 42 → ℕ := ![5144483, 5144483, 5144483, 5144483, 3112095, 3112095, 3112095, 3112095, 5144483, 5144483, 2286437, 2286437, 2286437, 2286437, 4064777, 4064777, 2286437, 2286437, 9519013, 34962020, 106147352, 100287661, 30814247, 240392540, 39659306, 39659306, 26751322, 26751322, 42331420, 42331420, 33780595, 79795748, 101981296, 101981296, 79086693, 79086693, 106371291, 106371291, 48290998, 48290998, 204734428, 204734428]

theorem branchIntegerCurvature083_eq :
    (fun i : Fin 42 => curvatureNumerators (branchRows 83 i)) = branchIntegerCurvature083 := by
  change curvatureNumerators ∘ branchRows 83 = branchIntegerCurvature083
  rw [show branchRows 83 = (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 45, 43, 30, 31, 32, 33, 54, 55, 50, 51, 38, 39, 40, 41] : Fin 42 → Fin 56) from rfl]
  simp only [certificate_comp_vecCons, certificate_comp_vecEmpty]
  rfl

theorem branchIntegerCurvature083_entry (i : Fin 42) :
    curvatureNumerators (branchRows 83 i) = branchIntegerCurvature083 i :=
  congrFun branchIntegerCurvature083_eq i

def branchResiduals083 : Fin 33 → Fin 2 → ℕ := ![![1302257427328372, 33000000000000], ![1546551569028370, 33000000000000], ![1585127095212755, 1336760583187940], ![33000000000000, 1024331311443958], ![860572074281336, 33000000000000], ![1053998955028424, 893860909105151], ![720386069516620, 624777238175104], ![33000000000000, 763525801716916], ![1579159678879425, 1128452734381895], ![1025812043689577, 33000000000000], ![33000000000000, 777632019678618], ![507556183864690, 464022179603405], ![990410356255075, 66000000000000], ![33000000000000, 862998091124416], ![1054498955028457, 487658442023773], ![471967803271104, 33000000000000], ![66000000000000, 744121016473193], ![660414838469010, 462842739758769], ![620812030828169, 268295018393809], ![629632743419687, 510531548456317], ![1477700438628792, 854833127134258], ![751321880462813, 375215540078376], ![470939678676221, 90706651221511], ![1477700438628792, 854833127134258], ![668306644415849, 230374054719026], ![505936894074485, 218713669397988], ![396136216194598, 854833127134258], ![408541179298282, 545859315217724], ![283938357332490, 299207140313493], ![396136216194598, 891428242462843], ![215729782293340, 553298276274045], ![1680150457817014, 648577798406985], ![1332039050357428, 2887686809275685]]

theorem branchResiduals083_eq : residualNumerators 83 = branchResiduals083 := rfl

theorem integerCheck083_0_0 :
    integerResidualCheck 83 0 0 (dualNumerators083 0 0) ∧
    integerMassCheck 83 0 0 (dualNumerators083 0 0) := by
  apply integerChecks_of_simple 83 0 0 (dualNumerators083 0 0)
    (![0, 0, 500000000001, 344525275674, 1, 1269150346660, 1502797350439, 0, 1184097183123, 844525275673, 1269150346661, 0, 258120108700, 1402086139074, 1502797350439, 0, 0, 1402086139076, 2844303430895, 2402086139076, 1308901425339, 1967013593984, 1308901425339, 1549866490727, 1269150346660, 1, 258120108699, 1402086139075, 0, 0, 1967013593984, 2173046324067, 217988955954, 1955057368113, 74854042823, 1234047382517, 1835192545884, 0, 1821798773483, 145214820501, 1430871029972, 404321515913]) (branchResiduals083 0 0) 18767167
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 0) 0) rfl
  constructor <;> decide

theorem integerCheck083_0_1 :
    integerResidualCheck 83 0 1 (dualNumerators083 0 1) ∧
    integerMassCheck 83 0 1 (dualNumerators083 0 1) := by
  apply integerChecks_of_simple 83 0 1 (dualNumerators083 0 1)
    (![500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals083 0 1) 18767167
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 0) 1) rfl
  constructor <;> decide

theorem integerCheck083_1_0 :
    integerResidualCheck 83 1 0 (dualNumerators083 1 0) ∧
    integerMassCheck 83 1 0 (dualNumerators083 1 0) := by
  apply integerChecks_of_simple 83 1 0 (dualNumerators083 1 0)
    (![500000000000, 684097183123, 0, 0, 2, 1502797350437, 1779458109456, 0, 1402086139078, 999999999999, 1502797350439, 0, 305639293618, 1660206247771, 1779458109456, 0, 0, 1660206247774, 3367931680465, 2844303430895, 1549866490727, 2329135255797, 1549866490727, 1835192545884, 1502797350437, 2, 305639293617, 1660206247772, 0, 0, 2329135255797, 2573098031120, 258120108696, 2314977922424, 88634461252, 1461232029476, 2173046324067, 0, 2157186795895, 171948459903, 1694290356000, 478755968067]) (branchResiduals083 1 0) 22176635
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 1) 0) rfl
  constructor <;> decide

theorem integerCheck083_1_1 :
    integerResidualCheck 83 1 1 (dualNumerators083 1 1) ∧
    integerMassCheck 83 1 1 (dualNumerators083 1 1) := by
  apply integerChecks_of_simple 83 1 1 (dualNumerators083 1 1)
    (![0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals083 1 1) 22176635
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 1) 1) rfl
  constructor <;> decide

theorem integerCheck083_2_0 :
    integerResidualCheck 83 2 0 (dualNumerators083 2 0) ∧
    integerMassCheck 83 2 0 (dualNumerators083 2 0) := by
  apply integerChecks_of_simple 83 2 0 (dualNumerators083 2 0)
    (![0, 1184097183123, 1000000000001, 0, 2, 1502797350439, 1779458109458, 0, 1402086139079, 1000000000000, 1502797350440, 0, 305639293619, 1660206247773, 1779458109458, 0, 0, 1660206247775, 3367931680468, 2844303430897, 1549866490728, 2329135255799, 1549866490728, 1835192545886, 1502797350439, 2, 305639293618, 1660206247774, 0, 0, 2329135255799, 2573098031122, 258120108697, 2314977922426, 88634461252, 1461232029477, 2173046324068, 0, 2157186795897, 171948459903, 1694290356001, 478755968068]) (branchResiduals083 2 0) 22681452
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 2) 0) rfl
  constructor <;> decide

theorem integerCheck083_2_1 :
    integerResidualCheck 83 2 1 (dualNumerators083 2 1) ∧
    integerMassCheck 83 2 1 (dualNumerators083 2 1) := by
  apply integerChecks_of_simple 83 2 1 (dualNumerators083 2 1)
    (![1000000000000, 0, 0, 844525275674, 1, 1269150346659, 1502797350438, 0, 1184097183123, 844525275672, 1269150346660, 0, 258120108700, 1402086139073, 1502797350438, 0, 0, 1402086139075, 2844303430893, 2402086139075, 1308901425338, 1967013593982, 1308901425338, 1549866490726, 1269150346659, 1, 258120108699, 1402086139074, 0, 0, 1967013593982, 2173046324065, 217988955954, 1955057368112, 74854042823, 1234047382516, 1835192545883, 0, 1821798773482, 145214820501, 1430871029971, 404321515912]) (branchResiduals083 2 1) 22681452
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 2) 1) rfl
  constructor <;> decide

theorem integerCheck083_3_0 :
    integerResidualCheck 83 3 0 (dualNumerators083 3 0) ∧
    integerMassCheck 83 3 0 (dualNumerators083 3 0) := by
  apply integerChecks_of_simple 83 3 0 (dualNumerators083 3 0)
    (![0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals083 3 0) 16360330
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 3) 0) rfl
  constructor <;> decide

theorem integerCheck083_3_1 :
    integerResidualCheck 83 3 1 (dualNumerators083 3 1) ∧
    integerMassCheck 83 3 1 (dualNumerators083 3 1) := by
  apply integerChecks_of_simple 83 3 1 (dualNumerators083 3 1)
    (![665425714058, 122502999536, 665425714059, 0, 0, 0, 684097183123, 500000000000, 932984170267, 665425714058, 1000000000001, 0, 203380245200, 1104743927908, 1184097183122, 0, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000001, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 171759757642, 1540445837058, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 1127424369963, 318576531911]) (branchResiduals083 3 1) 16360330
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 3) 1) rfl
  constructor <;> decide

theorem integerCheck083_4_0 :
    integerResidualCheck 83 4 0 (dualNumerators083 4 0) ∧
    integerMassCheck 83 4 0 (dualNumerators083 4 0) := by
  apply integerChecks_of_simple 83 4 0 (dualNumerators083 4 0)
    (![561968834605, 103456879454, 561968834606, 0, 500000000001, 344525275674, 0, 0, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 145055456673, 1300945445202, 49809804896, 821166860693, 1221184310279, 0, 1212271749715, 96629675624, 952138376845, 269045933435]) (branchResiduals083 4 0) 13760362
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 4) 0) rfl
  constructor <;> decide

theorem integerCheck083_4_1 :
    integerResidualCheck 83 4 1 (dualNumerators083 4 1) ∧
    integerMassCheck 83 4 1 (dualNumerators083 4 1) := by
  apply integerChecks_of_simple 83 4 1 (dualNumerators083 4 1)
    (![0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals083 4 1) 13760362
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 4) 1) rfl
  constructor <;> decide

theorem integerCheck083_5_0 :
    integerResidualCheck 83 5 0 (dualNumerators083 5 0) ∧
    integerMassCheck 83 5 0 (dualNumerators083 5 0) := by
  apply integerChecks_of_simple 83 5 0 (dualNumerators083 5 0)
    (![665425714059, 122502999536, 665425714059, 0, 1000000000001, 0, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 203380245200, 1104743927909, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 1000000000001, 0, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 171759757642, 1540445837059, 58979649669, 972341366620, 1446000901875, 0, 1435447564017, 114418926712, 1127424369964, 318576531911]) (branchResiduals083 5 0) 17641130
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 5) 0) rfl
  constructor <;> decide

theorem integerCheck083_5_1 :
    integerResidualCheck 83 5 1 (dualNumerators083 5 1) ∧
    integerMassCheck 83 5 1 (dualNumerators083 5 1) := by
  apply integerChecks_of_simple 83 5 1 (dualNumerators083 5 1)
    (![561968834605, 103456879454, 561968834605, 0, 0, 844525275674, 0, 1000000000000, 787928713594, 561968834605, 844525275674, 0, 171759757644, 932984170265, 1000000000000, 0, 0, 932984170266, 1892672641500, 1598409884323, 870976665588, 1308901425338, 870976665588, 1031321016287, 844525275674, 0, 171759757644, 932984170265, 0, 0, 1308901425338, 1446000901873, 145055456672, 1300945445201, 49809804896, 821166860692, 1221184310279, 0, 1212271749715, 96629675624, 952138376844, 269045933435]) (branchResiduals083 5 1) 17641130
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 5) 1) rfl
  constructor <;> decide

theorem integerCheck083_6_0 :
    integerResidualCheck 83 6 0 (dualNumerators083 6 0) ∧
    integerMassCheck 83 6 0 (dualNumerators083 6 0) := by
  apply integerChecks_of_simple 83 6 0 (dualNumerators083 6 0)
    (![0, 0, 0, 0, 1, 70552396879, 83540894407, 0, 684097183123, 500000000000, 70552396879, 0, 258120108699, 1402086139075, 83540894407, 0, 0, 1402086139076, 2844303430895, 2402086139076, 0, 109346795763, 0, 1549866490727, 70552396879, 0, 258120108699, 1402086139075, 0, 0, 109346795763, 2173046324067, 1175693227482, 997353096586, 0, 0, 877488274356, 957704271528, 103906894360, 5439901403, 1430871029972, 404321515913]) (branchResiduals083 6 0) 8962451
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 6) 0) rfl
  constructor <;> decide

theorem integerCheck083_6_1 :
    integerResidualCheck 83 6 1 (dualNumerators083 6 1) ∧
    integerMassCheck 83 6 1 (dualNumerators083 6 1) := by
  apply integerChecks_of_simple 83 6 1 (dualNumerators083 6 1)
    (![844525275674, 155474724327, 844525275674, 0, 1, 1198597949782, 1419256456032, 0, 500000000001, 344525275674, 1198597949783, 0, 0, 0, 1419256456032, 0, 0, 0, 0, 0, 1308901425339, 1857666798222, 1308901425339, 0, 1198597949783, 0, 0, 0, 0, 0, 1857666798222, 0, 0, 0, 1032558314351, 276343110989, 0, 0, 760187607595, 1097479190627, 0, 0]) (branchResiduals083 6 1) 8962451
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 6) 1) rfl
  constructor <;> decide

theorem integerCheck083_7_0 :
    integerResidualCheck 83 7 0 (dualNumerators083 7 0) ∧
    integerMassCheck 83 7 0 (dualNumerators083 7 0) := by
  apply integerChecks_of_simple 83 7 0 (dualNumerators083 7 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals083 7 0) 10424794
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 7) 0) rfl
  constructor <;> decide

theorem integerCheck083_7_1 :
    integerResidualCheck 83 7 1 (dualNumerators083 7 1) ∧
    integerMassCheck 83 7 1 (dualNumerators083 7 1) := by
  apply integerChecks_of_simple 83 7 1 (dualNumerators083 7 1)
    (![500000000001, 92048591562, 500000000001, 0, 1, 751398675220, 889729054730, 0, 201043069540, 0, 751398675221, 0, 152819646809, 830103123888, 889729054730, 0, 0, 830103123889, 1683965840236, 1422151715450, 774933245365, 1164567627901, 774933245365, 917596272944, 751398675221, 0, 152819646809, 830103123888, 0, 0, 1164567627901, 1286549015562, 129060054349, 1157488961214, 44317230626, 730616014740, 1086523162035, 0, 1078593397950, 85974229952, 847145178002, 239377984034]) (branchResiduals083 7 1) 10424794
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 7) 1) rfl
  constructor <;> decide

theorem integerCheck083_8_0 :
    integerResidualCheck 83 8 0 (dualNumerators083 8 0) ∧
    integerMassCheck 83 8 0 (dualNumerators083 8 0) := by
  apply integerChecks_of_simple 83 8 0 (dualNumerators083 8 0)
    (![1000000000001, 184097183123, 1000000000002, 0, 2, 1502797350440, 1779458109459, 0, 2402086139080, 0, 1502797350441, 0, 305639293618, 1660206247775, 1779458109459, 0, 0, 1660206247777, 3367931680471, 2844303430900, 1549866490730, 2329135255801, 1549866490730, 1835192545887, 1502797350441, 0, 305639293618, 1660206247775, 0, 0, 2329135255801, 2573098031124, 258120108697, 2314977922428, 88634461252, 1461232029479, 2173046324070, 0, 2157186795899, 171948459903, 1694290356003, 478755968068]) (branchResiduals083 8 0) 22681452
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 8) 0) rfl
  constructor <;> decide

theorem integerCheck083_8_1 :
    integerResidualCheck 83 8 1 (dualNumerators083 8 1) ∧
    integerMassCheck 83 8 1 (dualNumerators083 8 1) := by
  apply integerChecks_of_simple 83 8 1 (dualNumerators083 8 1)
    (![713222941251, 131302334423, 713222941251, 0, 1, 1071829546383, 1269150346659, 0, 0, 1713222941250, 853840590428, 217988955957, 0, 1402086139075, 1269150346659, 0, 0, 1184097183120, 2402086139074, 2028622458793, 1105400337063, 1661192697711, 1105400337063, 1308901425337, 1071829546383, 1, 217988955956, 1184097183119, 0, 0, 1661192697711, 1835192545882, 184097183121, 1651095362762, 63216131150, 1042184205913, 1549866490725, 0, 1538555111396, 122637586316, 1208406751039, 341459739686]) (branchResiduals083 8 1) 22681452
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 8) 1) rfl
  constructor <;> decide

theorem integerCheck083_9_0 :
    integerResidualCheck 83 9 0 (dualNumerators083 9 0) ∧
    integerMassCheck 83 9 0 (dualNumerators083 9 0) := by
  apply integerChecks_of_simple 83 9 0 (dualNumerators083 9 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 0, 1308124173107, 1184097183122, 0, 296619754801, 808124173109, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 1000000000000, 1, 500000000000, 808124173108, 0, 0, 1549866490727, 1712205594700, 171759757642, 1540445837058, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 1127424369963, 318576531911]) (branchResiduals083 9 0) 16350530
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 9) 0) rfl
  constructor <;> decide

theorem integerCheck083_9_1 :
    integerResidualCheck 83 9 1 (dualNumerators083 9 1) ∧
    integerMassCheck 83 9 1 (dualNumerators083 9 1) := by
  apply integerChecks_of_simple 83 9 1 (dualNumerators083 9 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals083 9 1) 16350530
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 9) 1) rfl
  constructor <;> decide

theorem integerCheck083_10_0 :
    integerResidualCheck 83 10 0 (dualNumerators083 10 0) ∧
    integerMassCheck 83 10 0 (dualNumerators083 10 0) := by
  apply integerChecks_of_simple 83 10 0 (dualNumerators083 10 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals083 10 0) 10683139
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 10) 0) rfl
  constructor <;> decide

theorem integerCheck083_10_1 :
    integerResidualCheck 83 10 1 (dualNumerators083 10 1) ∧
    integerMassCheck 83 10 1 (dualNumerators083 10 1) := by
  apply integerChecks_of_simple 83 10 1 (dualNumerators083 10 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275673, 500000000002, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421593, 1, 500000000000, 500000000001, 0, 0, 1184800741849, 1308901425339, 131302334422, 1177599090918, 45087194994, 743309684668, 1105400337064, 0, 1097332801829, 87467940020, 861863417206, 243536919859]) (branchResiduals083 10 1) 10683139
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 10) 1) rfl
  constructor <;> decide

theorem integerCheck083_11_0 :
    integerResidualCheck 83 11 0 (dualNumerators083 11 0) ∧
    integerMassCheck 83 11 0 (dualNumerators083 11 0) := by
  apply integerChecks_of_simple 83 11 0 (dualNumerators083 11 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180167, 562584914688, 0, 443276808118, 316155188874, 0, 475117180167, 621512268435, 0, 562584914688, 0, 0, 524882819834, 1064789076551, 899241288409, 489998333105, 736368196709, 489998333105, 580205645964, 475117180167, 0, 96629448601, 524882819834, 0, 0, 736368196709, 813498294019, 81606011717, 731892282302, 28022244838, 461976088268, 687019871017, 0, 682005798892, 54362397817, 535658687508, 151361183509]) (branchResiduals083 11 0) 15120968
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 11) 0) rfl
  constructor <;> decide

theorem integerCheck083_11_1 :
    integerResidualCheck 83 11 1 (dualNumerators083 11 1) ∧
    integerMassCheck 83 11 1 (dualNumerators083 11 1) := by
  apply integerChecks_of_simple 83 11 1 (dualNumerators083 11 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494509, 288297190338, 433252253779, 0, 0, 566747746222, 79760519503, 433252253779, 478632796615, 1, 970965240729, 820004687597, 446822154676, 671483150164, 446822154676, 529080854708, 0, 433252253779, 566747746222, 0, 0, 0, 671483150164, 741816932837, 74415302107, 667401630730, 25553066146, 421269088530, 626483149703, 0, 621910892291, 49572257873, 488459149252, 138024000452]) (branchResiduals083 11 1) 15120968
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 11) 1) rfl
  constructor <;> decide

theorem integerCheck083_12_0 :
    integerResidualCheck 83 12 0 (dualNumerators083 12 0) ∧
    integerMassCheck 83 12 0 (dualNumerators083 12 0) := by
  apply integerChecks_of_simple 83 12 0 (dualNumerators083 12 0)
    (![665425714058, 122502999536, 665425714059, 0, 1, 1000000000000, 1184097183122, 0, 932984170267, 665425714058, 0, 0, 203380245200, 1104743927908, 684097183123, 500000000000, 0, 1104743927909, 2241108343373, 1892672641502, 1031321016287, 1549866490727, 1031321016287, 1221184310279, 0, 0, 203380245200, 1104743927908, 0, 0, 1549866490727, 1712205594700, 171759757642, 1540445837058, 58979649669, 972341366619, 1446000901874, 0, 1435447564016, 114418926712, 1127424369963, 318576531911]) (branchResiduals083 12 0) 16348076
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 12) 0) rfl
  constructor <;> decide

theorem integerCheck083_12_1 :
    integerResidualCheck 83 12 1 (dualNumerators083 12 1) ∧
    integerMassCheck 83 12 1 (dualNumerators083 12 1) := by
  apply integerChecks_of_simple 83 12 1 (dualNumerators083 12 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals083 12 1) 16348076
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 12) 1) rfl
  constructor <;> decide

theorem integerCheck083_13_0 :
    integerResidualCheck 83 13 0 (dualNumerators083 13 0) ∧
    integerMassCheck 83 13 0 (dualNumerators083 13 0) := by
  apply integerChecks_of_simple 83 13 0 (dualNumerators083 13 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals083 13 0) 13962901
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 13) 0) rfl
  constructor <;> decide

theorem integerCheck083_13_1 :
    integerResidualCheck 83 13 1 (dualNumerators083 13 1) ∧
    integerMassCheck 83 13 1 (dualNumerators083 13 1) := by
  apply integerChecks_of_simple 83 13 1 (dualNumerators083 13 1)
    (![561968834605, 103456879454, 561968834606, 0, 1, 844525275674, 1000000000000, 0, 787928713594, 561968834605, 844525275674, 0, 671759757645, 432984170265, 0, 0, 0, 932984170266, 1892672641502, 1598409884324, 870976665588, 1308901425339, 870976665588, 1031321016287, 344525275674, 500000000001, 171759757644, 932984170265, 0, 0, 1308901425339, 1446000901874, 145055456673, 1300945445202, 49809804896, 821166860693, 1221184310279, 0, 1212271749715, 96629675624, 952138376845, 269045933435]) (branchResiduals083 13 1) 13962901
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 13) 1) rfl
  constructor <;> decide

theorem integerCheck083_14_0 :
    integerResidualCheck 83 14 0 (dualNumerators083 14 0) ∧
    integerMassCheck 83 14 0 (dualNumerators083 14 0) := by
  apply integerChecks_of_simple 83 14 0 (dualNumerators083 14 0)
    (![665425714059, 122502999536, 665425714059, 0, 1, 1000000000001, 1184097183123, 0, 932984170268, 665425714058, 1000000000001, 0, 1203380245201, 104743927908, 1184097183123, 0, 0, 1104743927910, 2241108343375, 1892672641503, 1031321016288, 1549866490728, 1031321016288, 1221184310280, 0, 1000000000001, 203380245200, 1104743927909, 0, 0, 1549866490728, 1712205594701, 171759757642, 1540445837059, 58979649669, 972341366620, 1446000901875, 0, 1435447564017, 114418926712, 1127424369964, 318576531911]) (branchResiduals083 14 0) 20161291
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 14) 0) rfl
  constructor <;> decide

theorem integerCheck083_14_1 :
    integerResidualCheck 83 14 1 (dualNumerators083 14 1) ∧
    integerMassCheck 83 14 1 (dualNumerators083 14 1) := by
  apply integerChecks_of_simple 83 14 1 (dualNumerators083 14 1)
    (![304668546437, 56088621185, 304668546437, 0, 1, 457855084347, 542144915653, 0, 427171545972, 304668546437, 0, 0, 0, 598931303614, 0, 542144915653, 364736405027, 598931303615, 1026102849586, 866569791916, 472195570901, 709614252839, 472195570901, 559125445386, 0, 0, 0, 598931303614, 457855084347, 0, 709614252839, 783942036981, 78641078323, 705300958658, 27004132474, 445191438428, 662058864893, 0, 657226965498, 52387287341, 516196980004, 145861884889]) (branchResiduals083 14 1) 20161291
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 14) 1) rfl
  constructor <;> decide

theorem integerCheck083_15_0 :
    integerResidualCheck 83 15 0 (dualNumerators083 15 0) ∧
    integerMassCheck 83 15 0 (dualNumerators083 15 0) := by
  apply integerChecks_of_simple 83 15 0 (dualNumerators083 15 0)
    (![316155188874, 58203279702, 316155188874, 0, 1, 475117180166, 562584914688, 0, 443276808117, 316155188873, 0, 0, 596629448601, 24882819833, 562584914688, 0, 0, 0, 1064789076551, 899241288408, 489998333105, 736368196709, 489998333105, 580205645964, 0, 0, 596629448601, 24882819833, 0, 475117180167, 736368196709, 813498294019, 81606011717, 731892282302, 28022244838, 461976088267, 687019871016, 0, 682005798892, 54362397817, 535658687508, 151361183509]) (branchResiduals083 15 0) 12900283
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 15) 0) rfl
  constructor <;> decide

theorem integerCheck083_15_1 :
    integerResidualCheck 83 15 1 (dualNumerators083 15 1) ∧
    integerMassCheck 83 15 1 (dualNumerators083 15 1) := by
  apply integerChecks_of_simple 83 15 1 (dualNumerators083 15 1)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals083 15 1) 12900283
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 15) 1) rfl
  constructor <;> decide

theorem integerCheck083_16_0 :
    integerResidualCheck 83 16 0 (dualNumerators083 16 0) ∧
    integerMassCheck 83 16 0 (dualNumerators083 16 0) := by
  apply integerChecks_of_simple 83 16 0 (dualNumerators083 16 0)
    (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 500000000000, 500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (branchResiduals083 16 0) 10683060
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 16) 0) rfl
  constructor <;> decide

theorem integerCheck083_16_1 :
    integerResidualCheck 83 16 1 (dualNumerators083 16 1) ∧
    integerMassCheck 83 16 1 (dualNumerators083 16 1) := by
  apply integerChecks_of_simple 83 16 1 (dualNumerators083 16 1)
    (![508686963928, 93647837151, 508686963928, 0, 1, 764453421593, 905187143136, 0, 713222941253, 508686963927, 764453421594, 0, 0, 0, 905187143136, 0, 344525275674, 500000000001, 1713222941252, 1446860076752, 788396879662, 1184800741849, 788396879662, 933538524389, 764453421594, 0, 0, 0, 0, 0, 1184800741849, 1308901425339, 131302334422, 1177599090918, 45087194994, 743309684668, 1105400337064, 0, 1097332801829, 87467940020, 861863417206, 243536919859]) (branchResiduals083 16 1) 10683060
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 16) 1) rfl
  constructor <;> decide

theorem integerCheck083_17_0 :
    integerResidualCheck 83 17 0 (dualNumerators083 17 0) ∧
    integerMassCheck 83 17 0 (dualNumerators083 17 0) := by
  apply integerChecks_of_simple 83 17 0 (dualNumerators083 17 0)
    (![414661618272, 76338035873, 414661618273, 0, 1, 623152381268, 737872979315, 0, 581391307387, 414661618272, 0, 311576190635, 815160693466, 0, 737872979315, 0, 0, 1000000000001, 1396552000852, 1179423463512, 642670147151, 965802994344, 642670147151, 760983910917, 0, 311576190635, 815160693466, 0, 311576190634, 0, 965802994344, 1066964993557, 107032501981, 959932491577, 36753309138, 605916838014, 901078905318, 0, 894502567701, 71300426643, 702557180842, 198521724476]) (branchResiduals083 17 0) 15120968
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 17) 0) rfl
  constructor <;> decide

theorem integerCheck083_17_1 :
    integerResidualCheck 83 17 1 (dualNumerators083 17 1) ∧
    integerMassCheck 83 17 1 (dualNumerators083 17 1) := by
  apply integerChecks_of_simple 83 17 1 (dualNumerators083 17 1)
    (![288297190338, 53074700644, 288297190339, 0, 1, 433252253779, 513012773281, 0, 404217494508, 288297190338, 0, 0, 0, 566747746221, 513012773281, 0, 911885050394, 0, 970965240729, 820004687596, 446822154676, 671483150164, 446822154676, 529080854708, 0, 0, 0, 566747746221, 0, 433252253779, 671483150164, 741816932836, 74415302107, 667401630730, 25553066146, 421269088530, 626483149703, 0, 621910892291, 49572257873, 488459149252, 138024000452]) (branchResiduals083 17 1) 15120968
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 17) 1) rfl
  constructor <;> decide

theorem integerCheck083_18_0 :
    integerResidualCheck 83 18 0 (dualNumerators083 18 0) ∧
    integerMassCheck 83 18 0 (dualNumerators083 18 0) := by
  apply integerChecks_of_simple 83 18 0 (dualNumerators083 18 0)
    (![0, 0, 0, 0, 1, 636538415124, 753723344298, 0, 691151837051, 492945346072, 636538415125, 0, 74022925577, 402086139076, 753723344298, 0, 0, 402086139076, 1660206247774, 1402086139076, 0, 986549559662, 763999473637, 904649624640, 636538415125, 0, 74022925577, 402086139076, 0, 0, 986549559662, 623179833340, 170971222814, 1097425476614, 0, 763999473637, 1027460955744, 43732116505, 953519106044, 33030453619, 835192545885, 236000526363]) (branchResiduals083 18 0) 13565580
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 18) 0) rfl
  constructor <;> decide

theorem integerCheck083_18_1 :
    integerResidualCheck 83 18 1 (dualNumerators083 18 1) ∧
    integerMassCheck 83 18 1 (dualNumerators083 18 1) := by
  apply integerChecks_of_simple 83 18 1 (dualNumerators083 18 1)
    (![552774353318, 101764201348, 552774353318, 0, 1, 194169418432, 229915461414, 0, 83885421775, 59829007246, 194169418432, 0, 94926637302, 515633295911, 229915461414, 0, 0, 515633295912, 201500008915, 170171850577, 856726447141, 300936675152, 92726973504, 109797748126, 194169418432, 0, 94926637302, 515633295911, 0, 0, 300936675152, 799162766836, 15443069854, 138502830895, 92726973504, 0, 130011204269, 0, 195186313540, 105750361613, 101367709986, 28643494283]) (branchResiduals083 18 1) 13565580
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 18) 1) rfl
  constructor <;> decide

theorem integerCheck083_19_0 :
    integerResidualCheck 83 19 0 (dualNumerators083 19 0) ∧
    integerMassCheck 83 19 0 (dualNumerators083 19 0) := by
  apply integerChecks_of_simple 83 19 0 (dualNumerators083 19 0)
    (![0, 0, 0, 0, 1, 434692256459, 514717876398, 0, 583695195718, 416304804283, 434692256459, 0, 217988955956, 1184097183121, 514717876398, 0, 0, 1184097183122, 1402086139076, 1184097183122, 0, 673714962064, 645216866088, 763999473637, 434692256459, 0, 217988955956, 1184097183121, 0, 0, 673714962064, 1835192545884, 230658067063, 840535005185, 0, 645216866088, 781448198910, 123201425731, 653752451905, 19962510160, 705341215054, 199308409586]) (branchResiduals083 19 0) 8248658
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 19) 0) rfl
  constructor <;> decide

theorem integerCheck083_19_1 :
    integerResidualCheck 83 19 1 (dualNumerators083 19 1) ∧
    integerMassCheck 83 19 1 (dualNumerators083 19 1) := by
  apply integerChecks_of_simple 83 19 1 (dualNumerators083 19 1)
    (![713222941252, 131302334423, 713222941252, 0, 1, 637137289926, 754432470263, 0, 416304804284, 296918136968, 637137289926, 0, 0, 0, 754432470263, 0, 0, 0, 1000000000000, 844525275674, 1105400337064, 987477735649, 460183470977, 544901951702, 637137289926, 0, 0, 0, 0, 0, 987477735649, 0, 76640541789, 687358931849, 186417556881, 273765914097, 645216866088, 0, 761601233763, 225876501886, 503065535987, 142151330101]) (branchResiduals083 19 1) 8248658
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 19) 1) rfl
  constructor <;> decide

theorem integerCheck083_20_0 :
    integerResidualCheck 83 20 0 (dualNumerators083 20 0) ∧
    integerMassCheck 83 20 0 (dualNumerators083 20 0) := by
  apply integerChecks_of_simple 83 20 0 (dualNumerators083 20 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 176645531640, 1584264425996, 1060657349048, 0, 1487132967409, 0, 2232638358246, 1209625354629, 1159494400494, 327638566915]) (branchResiduals083 20 0) 35312013
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 20) 0) rfl
  constructor <;> decide

theorem integerCheck083_20_1 :
    integerResidualCheck 83 20 1 (dualNumerators083 20 1) ∧
    integerMassCheck 83 20 1 (dualNumerators083 20 1) := by
  apply integerChecks_of_simple 83 20 1 (dualNumerators083 20 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals083 20 1) 35312013
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 20) 1) rfl
  constructor <;> decide

theorem integerCheck083_21_0 :
    integerResidualCheck 83 21 0 (dualNumerators083 21 0) ∧
    integerMassCheck 83 21 0 (dualNumerators083 21 0) := by
  apply integerChecks_of_simple 83 21 0 (dualNumerators083 21 0)
    (![602334801077, 110888140175, 602334801078, 0, 1, 1064898770837, 1260943634859, 0, 844525275675, 602334801077, 1064898770838, 0, 0, 0, 1260943634859, 0, 0, 0, 844525275674, 1713222941252, 933538524389, 1650450920938, 933538524389, 1105400337064, 1064898770838, 0, 0, 0, 0, 0, 1650450920938, 0, 0, 0, 736444277975, 197094246414, 759767979803, 549133445537, 851509250277, 798941670661, 1020530044549, 288371380791]) (branchResiduals083 21 0) 11182451
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 21) 0) rfl
  constructor <;> decide

theorem integerCheck083_21_1 :
    integerResidualCheck 83 21 1 (dualNumerators083 21 1) ∧
    integerMassCheck 83 21 1 (dualNumerators083 21 1) := by
  apply integerChecks_of_simple 83 21 1 (dualNumerators083 21 1)
    (![106276223907, 19565153455, 106276223907, 0, 0, 0, 0, 0, 149008420454, 106276223907, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1176440450920, 1542028244498, 302281828281, 164713958195, 0, 164713958195, 195037333919, 0, 0, 216579373126, 1176440450920, 0, 0, 0, 1823325633217, 860003851037, 963321782180, 3460174706, 161253783489, 102979506989, 127963650709, 0, 0, 180062781238, 50880376460]) (branchResiduals083 21 1) 11182451
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 21) 1) rfl
  constructor <;> decide

theorem integerCheck083_22_0 :
    integerResidualCheck 83 22 0 (dualNumerators083 22 0) ∧
    integerMassCheck 83 22 0 (dualNumerators083 22 0) := by
  apply integerChecks_of_simple 83 22 0 (dualNumerators083 22 0)
    (![296918136969, 54661792634, 296918136969, 0, 517035554684, 0, 95184789192, 517035554683, 416304804284, 296918136968, 517035554684, 0, 90749849646, 492945346072, 612220343875, 0, 0, 492945346072, 0, 844525275674, 460183470977, 801336080718, 460183470977, 544901951702, 517035554684, 0, 90749849646, 492945346072, 0, 0, 801336080718, 763999473637, 510506833659, 253492639979, 460183470977, 0, 270741877993, 374474988096, 310954038967, 490382041752, 503065535987, 142151330101]) (branchResiduals083 22 0) 6465674
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 22) 0) rfl
  constructor <;> decide

theorem integerCheck083_22_1 :
    integerResidualCheck 83 22 1 (dualNumerators083 22 1) ∧
    integerMassCheck 83 22 1 (dualNumerators083 22 1) := by
  apply integerChecks_of_simple 83 22 1 (dualNumerators083 22 1)
    (![47130616201, 8676613682, 47130616201, 0, 0, 0, 0, 0, 66081183701, 47130616201, 0, 0, 14404968244, 78246543477, 0, 0, 0, 78246543478, 1158732695421, 134053773359, 73046162737, 0, 73046162737, 86493755534, 0, 0, 14404968244, 78246543477, 0, 0, 0, 121271695751, 9522456419, 111749239332, 1534493418, 71511669319, 45668611868, 56748400418, 0, 0, 79852948501, 22564063785]) (branchResiduals083 22 1) 6465674
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 22) 1) rfl
  constructor <;> decide

theorem integerCheck083_23_0 :
    integerResidualCheck 83 23 0 (dualNumerators083 23 0) ∧
    integerMassCheck 83 23 0 (dualNumerators083 23 0) := by
  apply integerChecks_of_simple 83 23 0 (dualNumerators083 23 0)
    (![684354010744, 125987645637, 684354010745, 0, 2, 2221006605064, 2629887664752, 0, 959523272688, 684354010744, 2221006605066, 0, 209165476428, 1136168804326, 2629887664752, 0, 0, 1136168804327, 2304857553440, 1946510460708, 1060657349048, 3442263712874, 1060657349048, 1255921379264, 2221006605066, 0, 209165476428, 1136168804326, 0, 0, 3442263712874, 1760909957636, 1176645531640, 584264425996, 1060657349048, 0, 1487132967409, 0, 2232638358246, 1209625354629, 1159494400494, 327638566915]) (branchResiduals083 23 0) 35297932
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 23) 0) rfl
  constructor <;> decide

theorem integerCheck083_23_1 :
    integerResidualCheck 83 23 1 (dualNumerators083 23 1) ∧
    integerMassCheck 83 23 1 (dualNumerators083 23 1) := by
  apply integerChecks_of_simple 83 23 1 (dualNumerators083 23 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 160334187224, 1881575790198, 25837005087, 1204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals083 23 1) 35297932
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 23) 1) rfl
  constructor <;> decide

theorem integerCheck083_24_0 :
    integerResidualCheck 83 24 0 (dualNumerators083 24 0) ∧
    integerMassCheck 83 24 0 (dualNumerators083 24 0) := by
  apply integerChecks_of_simple 83 24 0 (dualNumerators083 24 0)
    (![0, 0, 0, 0, 1, 843189517757, 998418332815, 0, 691151837051, 492945346072, 426884713475, 0, 150663467366, 818390943359, 505472986743, 0, 0, 818390943360, 1660206247774, 1402086139076, 0, 1306831178905, 763999473637, 904649624640, 426884713475, 0, 150663467366, 818390943359, 0, 0, 661614312817, 1268396699427, 686246488518, 582150210910, 0, 0, 512185690040, 559007382209, 569308312247, 737522866658, 835192545885, 236000526363]) (branchResiduals083 24 0) 9356857
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 24) 0) rfl
  constructor <;> decide

theorem integerCheck083_24_1 :
    integerResidualCheck 83 24 1 (dualNumerators083 24 1) ∧
    integerMassCheck 83 24 1 (dualNumerators083 24 1) := by
  apply integerChecks_of_simple 83 24 1 (dualNumerators083 24 1)
    (![561079986940, 103293245102, 561079986941, 0, 0, 0, 0, 0, 95530635553, 68134640869, 416304804284, 0, 20824623506, 113117556460, 492945346072, 0, 0, 113117556460, 229472815518, 193795592785, 869599070377, 0, 105599596740, 125040185038, 416304804284, 0, 20824623506, 113117556460, 0, 0, 645216866088, 175317110270, 99625565721, 75691544549, 690777049383, 178822020994, 66021086067, 82038644814, 0, 0, 115439864933, 32619865948]) (branchResiduals083 24 1) 9356857
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 24) 1) rfl
  constructor <;> decide

theorem integerCheck083_25_0 :
    integerResidualCheck 83 25 0 (dualNumerators083 25 0) ∧
    integerMassCheck 83 25 0 (dualNumerators083 25 0) := by
  apply integerChecks_of_simple 83 25 0 (dualNumerators083 25 0)
    (![34423495944, 6337268637, 34423495944, 0, 1, 22181646803, 26265225496, 0, 631959902239, 450728300227, 515126992874, 0, 137760279295, 748301940085, 609960421212, 0, 0, 748301940086, 1518022121617, 1282008050738, 53351822857, 34378591088, 698568688945, 827173216796, 515126992874, 0, 137760279295, 748301940085, 0, 0, 798378064725, 1159768101884, 638738616250, 521029485635, 53351822857, 0, 457056897559, 522396578403, 34378591088, 0, 763664612251, 215788863711]) (branchResiduals083 25 0) 8671199
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 25) 0) rfl
  constructor <;> decide

theorem integerCheck083_25_1 :
    integerResidualCheck 83 25 1 (dualNumerators083 25 1) ∧
    integerMassCheck 83 25 1 (dualNumerators083 25 1) := by
  apply integerChecks_of_simple 83 25 1 (dualNumerators083 25 1)
    (![416304804284, 76640541789, 416304804284, 0, 1, 655171648547, 775786903506, 0, 0, 0, 162226302475, 0, 0, 0, 192091707789, 0, 0, 0, 0, 0, 645216866088, 1015428583757, 0, 0, 162226302475, 0, 0, 0, 0, 0, 251429110121, 0, 0, 0, 508994815607, 136222050481, 0, 0, 415529968297, 599898615461, 0, 0]) (branchResiduals083 25 1) 8671199
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 25) 1) rfl
  constructor <;> decide

theorem integerCheck083_26_0 :
    integerResidualCheck 83 26 0 (dualNumerators083 26 0) ∧
    integerMassCheck 83 26 0 (dualNumerators083 26 0) := by
  apply integerChecks_of_simple 83 26 0 (dualNumerators083 26 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 756358922550, 1091951736453, 0, 0]) (branchResiduals083 26 0) 15099566
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 26) 0) rfl
  constructor <;> decide

theorem integerCheck083_26_1 :
    integerResidualCheck 83 26 1 (dualNumerators083 26 1) ∧
    integerMassCheck 83 26 1 (dualNumerators083 26 1) := by
  apply integerChecks_of_simple 83 26 1 (dualNumerators083 26 1)
    (![793560895359, 146092325472, 793560895359, 0, 0, 0, 0, 0, 1112640731897, 793560895358, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 1317474756464, 2672658879858, 2257127977294, 1229913440069, 0, 1229913440069, 1456337039868, 0, 0, 242543391500, 1317474756463, 0, 0, 0, 2041909977422, 1160334187224, 881575790198, 1025837005087, 204076434982, 768944423926, 955500162657, 0, 0, 1344522571906, 379922014678]) (branchResiduals083 26 1) 15099566
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 26) 1) rfl
  constructor <;> decide

theorem integerCheck083_27_0 :
    integerResidualCheck 83 27 0 (dualNumerators083 27 0) ∧
    integerMassCheck 83 27 0 (dualNumerators083 27 0) := by
  apply integerChecks_of_simple 83 27 0 (dualNumerators083 27 0)
    (![351579929602, 64724874682, 351579929602, 0, 1, 894716117007, 1059430833842, 0, 492945346073, 351579929602, 478411312725, 0, 0, 0, 566485487771, 0, 0, 0, 0, 1000000000000, 544901951702, 1386690528464, 544901951702, 645216866088, 478411312725, 0, 0, 0, 0, 0, 741473662376, 0, 0, 0, 429858986967, 115042964736, 0, 0, 286173900105, 455299762271, 595678484088, 168320989550]) (branchResiduals083 27 0) 7338775
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 27) 0) rfl
  constructor <;> decide

theorem integerCheck083_27_1 :
    integerResidualCheck 83 27 1 (dualNumerators083 27 1) ∧
    integerMassCheck 83 27 1 (dualNumerators083 27 1) := by
  apply integerChecks_of_simple 83 27 1 (dualNumerators083 27 1)
    (![243787181438, 44880533384, 243787181438, 0, 0, 0, 0, 0, 341810627979, 243787181437, 416304804284, 0, 181967583261, 988432197466, 492945346072, 0, 0, 988432197466, 2005155754776, 693404716571, 377837583379, 0, 377837583379, 447396418156, 416304804284, 0, 181967583261, 988432197466, 0, 0, 645216866088, 1531937941208, 530765167249, 1001172773960, 0, 377837583379, 916671368281, 377088943834, 621055226706, 24161639382, 413046270426, 116714568052]) (branchResiduals083 27 1) 7338775
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 27) 1) rfl
  constructor <;> decide

theorem integerCheck083_28_0 :
    integerResidualCheck 83 28 0 (dualNumerators083 28 0) ∧
    integerMassCheck 83 28 0 (dualNumerators083 28 0) := by
  apply integerChecks_of_simple 83 28 0 (dualNumerators083 28 0)
    (![296918136969, 54661792634, 296918136969, 0, 1, 52793406530, 62512523959, 0, 416304804284, 296918136968, 545738752602, 0, 0, 0, 646207719676, 0, 0, 0, 0, 844525275674, 460183470977, 81822731712, 460183470977, 544901951702, 545738752602, 0, 0, 0, 0, 0, 845822205349, 0, 0, 0, 363026779469, 97156691508, 0, 0, 450383711774, 395438493575, 503065535987, 142151330101]) (branchResiduals083 28 0) 10335557
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 28) 0) rfl
  constructor <;> decide

theorem integerCheck083_28_1 :
    integerResidualCheck 83 28 1 (dualNumerators083 28 1) ∧
    integerMassCheck 83 28 1 (dualNumerators083 28 1) := by
  apply integerChecks_of_simple 83 28 1 (dualNumerators083 28 1)
    (![66230462171, 12192841523, 66230462171, 0, 1, 492945346072, 583695195717, 0, 92860812995, 66230462171, 0, 0, 110992481319, 602901573161, 0, 0, 0, 602901573161, 1223059671757, 188379530783, 102648373984, 763999473637, 102648373984, 121545650487, 0, 0, 110992481319, 602901573161, 0, 0, 0, 934416945449, 426731607120, 507685338329, 2156352207, 100492021777, 456143077212, 332995651238, 0, 0, 112213633330, 31708229033]) (branchResiduals083 28 1) 10335557
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 28) 1) rfl
  constructor <;> decide

theorem integerCheck083_29_0 :
    integerResidualCheck 83 29 0 (dualNumerators083 29 0) ∧
    integerMassCheck 83 29 0 (dualNumerators083 29 0) := by
  apply integerChecks_of_simple 83 29 0 (dualNumerators083 29 0)
    (![0, 0, 0, 0, 1, 1192561210956, 1412108370594, 0, 0, 0, 1192561210957, 0, 0, 0, 1412108370594, 0, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 1192561210957, 0, 0, 0, 0, 0, 1848310659003, 0, 0, 0, 0, 0, 0, 0, 1756358922550, 91951736453, 0, 0]) (branchResiduals083 29 0) 40352153
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 29) 0) rfl
  constructor <;> decide

theorem integerCheck083_29_1 :
    integerResidualCheck 83 29 1 (dualNumerators083 29 1) ∧
    integerMassCheck 83 29 1 (dualNumerators083 29 1) := by
  apply integerChecks_of_simple 83 29 1 (dualNumerators083 29 1)
    (![814189538844, 149890000629, 814189538844, 0, 1, 31000670773, 36707806937, 0, 1141563866996, 814189538843, 31000670773, 0, 248848315523, 1351722559260, 36707806937, 0, 0, 1351722559261, 2742134741776, 2315802098733, 1261885083355, 48046900821, 1261885083355, 1494194572624, 31000670773, 0, 248848315523, 1351722559260, 0, 0, 48046900821, 2094989499358, 210158692266, 1884830807092, 72165251132, 1189719832223, 1769271584479, 0, 0, 48046900821, 1379473483620, 389798100860]) (branchResiduals083 29 1) 40352153
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 29) 1) rfl
  constructor <;> decide

theorem integerCheck083_30_0 :
    integerResidualCheck 83 30 0 (dualNumerators083 30 0) ∧
    integerMassCheck 83 30 0 (dualNumerators083 30 0) := by
  apply integerChecks_of_simple 83 30 0 (dualNumerators083 30 0)
    (![124053396170, 22837880792, 124053396170, 0, 1, 115599349926, 136880864618, 0, 173933547275, 124053396170, 115599349926, 0, 37915592376, 205954223378, 136880864618, 0, 0, 205954223378, 417803363028, 1352845500339, 192266201784, 179163558800, 192266201784, 227661867942, 115599349926, 0, 37915592376, 205954223378, 0, 0, 179163558800, 319201549437, 32020676104, 287180873334, 10995405936, 181270795848, 269573776534, 0, 163293901896, 15869656905, 269573776534, 0]) (branchResiduals083 30 0) 7680628
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 30) 0) rfl
  constructor <;> decide

theorem integerCheck083_30_1 :
    integerResidualCheck 83 30 1 (dualNumerators083 30 1) ∧
    integerMassCheck 83 30 1 (dualNumerators083 30 1) := by
  apply integerChecks_of_simple 83 30 1 (dualNumerators083 30 1)
    (![351579929602, 64724874682, 351579929602, 0, 1, 599181151823, 709488714053, 0, 492945346073, 351579929602, 599181151823, 0, 107456641334, 583695195717, 709488714053, 0, 0, 583695195717, 1184097183122, 0, 544901951702, 928650789086, 544901951702, 645216866088, 599181151823, 0, 107456641334, 583695195717, 0, 0, 928650789086, 904649624640, 90749849645, 813899774996, 31162097647, 513739854055, 763999473637, 0, 862736028146, 65914760940, 536287180313, 227712293325]) (branchResiduals083 30 1) 7680628
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 30) 1) rfl
  constructor <;> decide

theorem integerCheck083_31_0 :
    integerResidualCheck 83 31 0 (dualNumerators083 31 0) ∧
    integerMassCheck 83 31 0 (dualNumerators083 31 0) := by
  apply integerChecks_of_simple 83 31 0 (dualNumerators083 31 0)
    (![1471748065526, 270944673129, 1471748065527, 0, 2, 1719079079315, 2035556695381, 0, 2063517562889, 1471748065524, 1719079079316, 0, 1491143233587, 0, 2035556695381, 0, 1259308150413, 1, 2554660796474, 3002000889069, 2281013009552, 2664343059941, 2281013009552, 2700941079273, 1719079079316, 0, 1491143233587, 0, 0, 0, 2664343059941, 1951759503826, 195790587527, 1755968916300, 939253060812, 1341759948741, 1648310233018, 0, 1640459045760, 1023884014182, 1648310233018, 0]) (branchResiduals083 31 0) 32891612
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 31) 0) rfl
  constructor <;> decide

theorem integerCheck083_31_1 :
    integerResidualCheck 83 31 1 (dualNumerators083 31 1) ∧
    integerMassCheck 83 31 1 (dualNumerators083 31 1) := by
  apply integerChecks_of_simple 83 31 1 (dualNumerators083 31 1)
    (![0, 0, 0, 0, 1, 492660014070, 583357334897, 0, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 583357334897, 0, 0, 1184097183122, 2402086139076, 1184097183122, 0, 763557247128, 0, 0, 492660014070, 0, 217988955956, 1184097183121, 0, 0, 763557247128, 1835192545884, 992902647047, 842289898838, 0, 0, 741061026801, 808805463926, 725570984152, 37986262977, 845258320866, 704608169862]) (branchResiduals083 31 1) 32891612
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 31) 1) rfl
  constructor <;> decide

theorem integerCheck083_32_0 :
    integerResidualCheck 83 32 0 (dualNumerators083 32 0) ∧
    integerMassCheck 83 32 0 (dualNumerators083 32 0) := by
  apply integerChecks_of_simple 83 32 0 (dualNumerators083 32 0)
    (![590217607306, 108657398935, 590217607307, 0, 2, 2079538667397, 2462375878259, 0, 827535926244, 590217607306, 0, 2079538667399, 1160276651773, 0, 382837210862, 2079538667397, 979882959195, 1, 1987812578015, 1678757965436, 914758491801, 3223007296772, 914758491801, 1083162953378, 0, 2079538667399, 1160276651773, 0, 0, 0, 3223007296772, 1518687763292, 152347032953, 1366340730340, 52313619645, 862444872157, 1282570201956, 0, 3029568551736, 193438745037, 0, 1282570201956]) (branchResiduals083 32 0) 67647473
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 32) 0) rfl
  constructor <;> decide

theorem integerCheck083_32_1 :
    integerResidualCheck 83 32 1 (dualNumerators083 32 1) ∧
    integerMassCheck 83 32 1 (dualNumerators083 32 1) := by
  apply integerChecks_of_simple 83 32 1 (dualNumerators083 32 1)
    (![2088746807768, 384532403566, 2088746807770, 0, 2, 1946401957494, 2304729075092, 0, 2928602947216, 2088746807766, 1946401957496, 0, 638403098871, 3467750500273, 2304729075092, 0, 0, 3467750500276, 7034756546356, 5941029711609, 3237278684975, 3016663171407, 3237278684975, 3833252571857, 1946401957496, 0, 638403098871, 3467750500273, 0, 0, 3016663171407, 5374550298578, 539147553060, 4835402745519, 185134947997, 3052143736978, 4538943572529, 0, 2749458111138, 267205060270, 4538943572529, 0]) (branchResiduals083 32 1) 67647473
    branchSparseDots083 branchIntegerCurvature083 branchDots083
    branchIntegerCurvature083_entry rfl
    (congrFun (congrFun branchResiduals083_eq 32) 1) rfl
  constructor <;> decide

theorem integerChecks083 (j : Fin 33) (s : Fin 2) :
    integerResidualCheck 83 j s (dualNumerators083 j s) ∧
    integerMassCheck 83 j s (dualNumerators083 j s) := by
  fin_cases j
  · fin_cases s
    · exact integerCheck083_0_0
    · exact integerCheck083_0_1
  · fin_cases s
    · exact integerCheck083_1_0
    · exact integerCheck083_1_1
  · fin_cases s
    · exact integerCheck083_2_0
    · exact integerCheck083_2_1
  · fin_cases s
    · exact integerCheck083_3_0
    · exact integerCheck083_3_1
  · fin_cases s
    · exact integerCheck083_4_0
    · exact integerCheck083_4_1
  · fin_cases s
    · exact integerCheck083_5_0
    · exact integerCheck083_5_1
  · fin_cases s
    · exact integerCheck083_6_0
    · exact integerCheck083_6_1
  · fin_cases s
    · exact integerCheck083_7_0
    · exact integerCheck083_7_1
  · fin_cases s
    · exact integerCheck083_8_0
    · exact integerCheck083_8_1
  · fin_cases s
    · exact integerCheck083_9_0
    · exact integerCheck083_9_1
  · fin_cases s
    · exact integerCheck083_10_0
    · exact integerCheck083_10_1
  · fin_cases s
    · exact integerCheck083_11_0
    · exact integerCheck083_11_1
  · fin_cases s
    · exact integerCheck083_12_0
    · exact integerCheck083_12_1
  · fin_cases s
    · exact integerCheck083_13_0
    · exact integerCheck083_13_1
  · fin_cases s
    · exact integerCheck083_14_0
    · exact integerCheck083_14_1
  · fin_cases s
    · exact integerCheck083_15_0
    · exact integerCheck083_15_1
  · fin_cases s
    · exact integerCheck083_16_0
    · exact integerCheck083_16_1
  · fin_cases s
    · exact integerCheck083_17_0
    · exact integerCheck083_17_1
  · fin_cases s
    · exact integerCheck083_18_0
    · exact integerCheck083_18_1
  · fin_cases s
    · exact integerCheck083_19_0
    · exact integerCheck083_19_1
  · fin_cases s
    · exact integerCheck083_20_0
    · exact integerCheck083_20_1
  · fin_cases s
    · exact integerCheck083_21_0
    · exact integerCheck083_21_1
  · fin_cases s
    · exact integerCheck083_22_0
    · exact integerCheck083_22_1
  · fin_cases s
    · exact integerCheck083_23_0
    · exact integerCheck083_23_1
  · fin_cases s
    · exact integerCheck083_24_0
    · exact integerCheck083_24_1
  · fin_cases s
    · exact integerCheck083_25_0
    · exact integerCheck083_25_1
  · fin_cases s
    · exact integerCheck083_26_0
    · exact integerCheck083_26_1
  · fin_cases s
    · exact integerCheck083_27_0
    · exact integerCheck083_27_1
  · fin_cases s
    · exact integerCheck083_28_0
    · exact integerCheck083_28_1
  · fin_cases s
    · exact integerCheck083_29_0
    · exact integerCheck083_29_1
  · fin_cases s
    · exact integerCheck083_30_0
    · exact integerCheck083_30_1
  · fin_cases s
    · exact integerCheck083_31_0
    · exact integerCheck083_31_1
  · fin_cases s
    · exact integerCheck083_32_0
    · exact integerCheck083_32_1

end ElevenSquare.Tasks.T06
