import ElevenSquare.Tasks.T03.CaseTable
import ElevenSquare.Tasks.T03.Initialization.Library64
import ElevenSquare.Tasks.T03.Initialization.Library08

namespace ElevenSquare.Pending.T03.Batch09.Seed1847
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,3,5,7,8,9,10,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1847]! = [0,2,3,5,7,8,9,10,12,13,14] :=
  (CaseTable.slice28 1847 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1847 := by
  unfold caseMask
  have hv : (1847 : Fin 2184).val = 1847 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1847)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 1847)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1847

namespace ElevenSquare.Pending.T03.Batch09.Seed1848
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,3,5,7,8,9,11,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1848]! = [0,2,3,5,7,8,9,11,12,13,14] :=
  (CaseTable.slice28 1848 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1848 := by
  unfold caseMask
  have hv : (1848 : Fin 2184).val = 1848 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1848)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 1848)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1848

namespace ElevenSquare.Pending.T03.Batch09.Seed1849
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,3,5,7,8,10,11,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1849]! = [0,2,3,5,7,8,10,11,12,13,14] :=
  (CaseTable.slice28 1849 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1849 := by
  unfold caseMask
  have hv : (1849 : Fin 2184).val = 1849 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1849)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 1849)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1849

namespace ElevenSquare.Pending.T03.Batch09.Seed1850
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,3,5,7,9,10,11,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1850]! = [0,2,3,5,7,9,10,11,12,13,14] :=
  (CaseTable.slice28 1850 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1850 := by
  unfold caseMask
  have hv : (1850 : Fin 2184).val = 1850 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1850)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 1850)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1850

namespace ElevenSquare.Pending.T03.Batch09.Seed1864
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,4,5,6,7,8,9,10,11,13]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1864]! = [0,2,4,5,6,7,8,9,10,11,13] :=
  (CaseTable.slice29 1864 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1864 := by
  unfold caseMask
  have hv : (1864 : Fin 2184).val = 1864 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1864)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 1864)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1864

namespace ElevenSquare.Pending.T03.Batch09.Seed1866
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,4,5,6,7,8,9,10,11,15]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1866]! = [0,2,4,5,6,7,8,9,10,11,15] :=
  (CaseTable.slice29 1866 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1866 := by
  unfold caseMask
  have hv : (1866 : Fin 2184).val = 1866 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1866)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 1866)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1866

namespace ElevenSquare.Pending.T03.Batch09.Seed1871
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,4,5,6,7,8,9,10,13,15]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1871]! = [0,2,4,5,6,7,8,9,10,13,15] :=
  (CaseTable.slice29 1871 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1871 := by
  unfold caseMask
  have hv : (1871 : Fin 2184).val = 1871 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1871)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 1871)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1871

namespace ElevenSquare.Pending.T03.Batch09.Seed1875
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,4,5,6,7,8,9,11,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1875]! = [0,2,4,5,6,7,8,9,11,13,14] :=
  (CaseTable.slice29 1875 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1875 := by
  unfold caseMask
  have hv : (1875 : Fin 2184).val = 1875 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1875)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 1875)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1875

namespace ElevenSquare.Pending.T03.Batch09.Seed1882
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,4,5,6,7,8,10,11,13,15]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1882]! = [0,2,4,5,6,7,8,10,11,13,15] :=
  (CaseTable.slice29 1882 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1882 := by
  unfold caseMask
  have hv : (1882 : Fin 2184).val = 1882 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library64.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1882)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library64.initialize cells cells_injective (caseMask 1882)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1882

namespace ElevenSquare.Pending.T03.Batch09.Seed1885
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,4,5,6,7,9,10,11,12,13]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1885]! = [0,2,4,5,6,7,9,10,11,12,13] :=
  (CaseTable.slice29 1885 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1885 := by
  unfold caseMask
  have hv : (1885 : Fin 2184).val = 1885 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1885)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 1885)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1885

namespace ElevenSquare.Pending.T03.Batch09.Seed1887
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,4,5,6,7,9,10,11,12,15]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1887]! = [0,2,4,5,6,7,9,10,11,12,15] :=
  (CaseTable.slice29 1887 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1887 := by
  unfold caseMask
  have hv : (1887 : Fin 2184).val = 1887 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1887)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 1887)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1887

namespace ElevenSquare.Pending.T03.Batch09.Seed1889
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,4,5,6,7,9,10,11,13,15]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1889]! = [0,2,4,5,6,7,9,10,11,13,15] :=
  (CaseTable.slice29 1889 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1889 := by
  unfold caseMask
  have hv : (1889 : Fin 2184).val = 1889 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1889)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 1889)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1889

namespace ElevenSquare.Pending.T03.Batch09.Seed1891
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,2,4,5,6,7,9,11,12,13,14]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1891]! = [0,2,4,5,6,7,9,11,12,13,14] :=
  (CaseTable.slice29 1891 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1891 := by
  unfold caseMask
  have hv : (1891 : Fin 2184).val = 1891 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1891)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 1891)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1891

namespace ElevenSquare.Pending.T03.Batch09.Seed1950
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def cells : Owner → Fin 16 := ![0,3,4,5,6,7,9,10,11,12,13]

theorem cells_injective : Function.Injective cells :=
  of_decide_eq_true (show decide (Function.Injective cells) = true from by rfl)

theorem recorded_tuple : recordedCaseTuples[1950]! = [0,3,4,5,6,7,9,10,11,12,13] :=
  (CaseTable.slice30 1950 (by decide) (by decide)).trans (by rfl)

theorem mask_binding : Finset.univ.image cells = caseMask 1950 := by
  unfold caseMask
  have hv : (1950 : Fin 2184).val = 1950 := by decide
  rw [hv,recorded_tuple]
  decide

def state : PoseState := Initialization.Library08.library.state cells

theorem initializes (P : Packing 11 coverCap) (hchart : IsCharted P)
    (hocc : Occupies P (caseMask 1950)) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) state := by
  exact Initialization.Library08.initialize cells cells_injective (caseMask 1950)
    mask_binding P hchart hocc

end
end ElevenSquare.Pending.T03.Batch09.Seed1950
