import ElevenSquare.Tasks.T03.CaseTable
import ElevenSquare.Tasks.T03.Initialization.Library08

namespace ElevenSquare.Pending.T03.Batch10.Seed1955
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,3,4,5,6,7,9,11,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1955]! = [0,3,4,5,6,7,9,11,12,13,14] :=
  (CaseTable.slice30 1955 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1955 := by
  unfold caseMask
  have hv : (1955 : Fin 2184).val = 1955 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1955)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 1955)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed1955

namespace ElevenSquare.Pending.T03.Batch10.Seed2047
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,6,8,10,11,12,13]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2047]! = [1,2,3,4,5,6,8,10,11,12,13] :=
  (CaseTable.slice31 2047 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2047 := by
  unfold caseMask
  have hv : (2047 : Fin 2184).val = 2047 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2047)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2047)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2047

namespace ElevenSquare.Pending.T03.Batch10.Seed2048
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,6,8,10,11,12,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2048]! = [1,2,3,4,5,6,8,10,11,12,14] :=
  (CaseTable.slice32 2048 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2048 := by
  unfold caseMask
  have hv : (2048 : Fin 2184).val = 2048 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2048)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2048)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2048

namespace ElevenSquare.Pending.T03.Batch10.Seed2049
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,6,8,10,11,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2049]! = [1,2,3,4,5,6,8,10,11,13,14] :=
  (CaseTable.slice32 2049 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2049 := by
  unfold caseMask
  have hv : (2049 : Fin 2184).val = 2049 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2049)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2049)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2049

namespace ElevenSquare.Pending.T03.Batch10.Seed2050
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,6,8,10,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2050]! = [1,2,3,4,5,6,8,10,12,13,14] :=
  (CaseTable.slice32 2050 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2050 := by
  unfold caseMask
  have hv : (2050 : Fin 2184).val = 2050 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2050)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2050)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2050

namespace ElevenSquare.Pending.T03.Batch10.Seed2051
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,6,8,11,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2051]! = [1,2,3,4,5,6,8,11,12,13,14] :=
  (CaseTable.slice32 2051 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2051 := by
  unfold caseMask
  have hv : (2051 : Fin 2184).val = 2051 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2051)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2051)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2051

namespace ElevenSquare.Pending.T03.Batch10.Seed2052
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,6,9,10,11,12,13]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2052]! = [1,2,3,4,5,6,9,10,11,12,13] :=
  (CaseTable.slice32 2052 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2052 := by
  unfold caseMask
  have hv : (2052 : Fin 2184).val = 2052 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2052)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2052)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2052

namespace ElevenSquare.Pending.T03.Batch10.Seed2053
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,6,9,10,11,12,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2053]! = [1,2,3,4,5,6,9,10,11,12,14] :=
  (CaseTable.slice32 2053 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2053 := by
  unfold caseMask
  have hv : (2053 : Fin 2184).val = 2053 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2053)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2053)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2053

namespace ElevenSquare.Pending.T03.Batch10.Seed2055
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,6,9,10,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2055]! = [1,2,3,4,5,6,9,10,12,13,14] :=
  (CaseTable.slice32 2055 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2055 := by
  unfold caseMask
  have hv : (2055 : Fin 2184).val = 2055 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2055)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2055)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2055

namespace ElevenSquare.Pending.T03.Batch10.Seed2056
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,6,9,11,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2056]! = [1,2,3,4,5,6,9,11,12,13,14] :=
  (CaseTable.slice32 2056 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2056 := by
  unfold caseMask
  have hv : (2056 : Fin 2184).val = 2056 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2056)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2056)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2056

namespace ElevenSquare.Pending.T03.Batch10.Seed2057
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,6,10,11,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2057]! = [1,2,3,4,5,6,10,11,12,13,14] :=
  (CaseTable.slice32 2057 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2057 := by
  unfold caseMask
  have hv : (2057 : Fin 2184).val = 2057 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2057)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2057)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2057

namespace ElevenSquare.Pending.T03.Batch10.Seed2068
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,7,8,10,11,12,13]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2068]! = [1,2,3,4,5,7,8,10,11,12,13] :=
  (CaseTable.slice32 2068 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2068 := by
  unfold caseMask
  have hv : (2068 : Fin 2184).val = 2068 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2068)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2068)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2068

namespace ElevenSquare.Pending.T03.Batch10.Seed2069
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,7,8,10,11,12,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2069]! = [1,2,3,4,5,7,8,10,11,12,14] :=
  (CaseTable.slice32 2069 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2069 := by
  unfold caseMask
  have hv : (2069 : Fin 2184).val = 2069 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2069)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2069)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2069

namespace ElevenSquare.Pending.T03.Batch10.Seed2070
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![1,2,3,4,5,7,8,10,11,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[2070]! = [1,2,3,4,5,7,8,10,11,13,14] :=
  (CaseTable.slice32 2070 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 2070 := by
  unfold caseMask
  have hv : (2070 : Fin 2184).val = 2070 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 2070)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 2070)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch10.Seed2070
