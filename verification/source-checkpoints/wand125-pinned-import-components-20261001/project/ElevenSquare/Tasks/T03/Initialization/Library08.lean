import ElevenSquare.Tasks.T03.SeedLibrary
import ElevenSquare.Tasks.T03.Initialization.Pose00_08
import ElevenSquare.Tasks.T03.Initialization.Pose01_08
import ElevenSquare.Tasks.T03.Initialization.Pose02_08
import ElevenSquare.Tasks.T03.Initialization.Pose03_08
import ElevenSquare.Tasks.T03.Initialization.Pose04_08
import ElevenSquare.Tasks.T03.Initialization.Pose05_08
import ElevenSquare.Tasks.T03.Initialization.Pose06_08
import ElevenSquare.Tasks.T03.Initialization.Pose07_08
import ElevenSquare.Tasks.T03.Initialization.Pose08_08
import ElevenSquare.Tasks.T03.Initialization.Pose09_08
import ElevenSquare.Tasks.T03.Initialization.Pose10_08
import ElevenSquare.Tasks.T03.Initialization.Pose11_08
import ElevenSquare.Tasks.T03.Initialization.Pose12_08
import ElevenSquare.Tasks.T03.Initialization.Pose13_08
import ElevenSquare.Tasks.T03.Initialization.Pose14_08
import ElevenSquare.Tasks.T03.Initialization.Pose15_08
import ElevenSquare.Tasks.T03.Initialization.Group00
import ElevenSquare.Tasks.T03.Initialization.Group01
import ElevenSquare.Tasks.T03.Initialization.Group02
import ElevenSquare.Tasks.T03.Initialization.Group03
import ElevenSquare.Tasks.T03.Initialization.Group04
import ElevenSquare.Tasks.T03.Initialization.Group05
import ElevenSquare.Tasks.T03.Initialization.Group06
import ElevenSquare.Tasks.T03.Initialization.Group07
import ElevenSquare.Tasks.T03.Initialization.Group08
import ElevenSquare.Tasks.T03.Initialization.Group09
import ElevenSquare.Tasks.T03.Initialization.Group10
import ElevenSquare.Tasks.T03.Initialization.Group11
import ElevenSquare.Tasks.T03.Initialization.Group12
import ElevenSquare.Tasks.T03.Initialization.Group13
import ElevenSquare.Tasks.T03.Initialization.Group14
import ElevenSquare.Tasks.T03.Initialization.Group15

namespace ElevenSquare.Pending.T03.Initialization.Library08
noncomputable section

def library : InitializationLibrary where
  rows := ![Pose00_08.template.rows,Pose01_08.template.rows,Pose02_08.template.rows,Pose03_08.template.rows,Pose04_08.template.rows,Pose05_08.template.rows,Pose06_08.template.rows,Pose07_08.template.rows,Pose08_08.template.rows,Pose09_08.template.rows,Pose10_08.template.rows,Pose11_08.template.rows,Pose12_08.template.rows,Pose13_08.template.rows,Pose14_08.template.rows,Pose15_08.template.rows]
  owned := ![Group00.vertices,Group01.vertices,Group02.vertices,Group03.vertices,Group04.vertices,Group05.vertices,Group06.vertices,Group07.vertices,Group08.vertices,Group09.vertices,Group10.vertices,Group11.vertices,Group12.vertices,Group13.vertices,Group14.vertices,Group15.vertices]
  rows_valid := by
    intro i q t hc hcell hq ht0 ht1
    fin_cases i
    · exact Pose00_08.covers q t hc hcell hq ht0 ht1
    · exact Pose01_08.covers q t hc hcell hq ht0 ht1
    · exact Pose02_08.covers q t hc hcell hq ht0 ht1
    · exact Pose03_08.covers q t hc hcell hq ht0 ht1
    · exact Pose04_08.covers q t hc hcell hq ht0 ht1
    · exact Pose05_08.covers q t hc hcell hq ht0 ht1
    · exact Pose06_08.covers q t hc hcell hq ht0 ht1
    · exact Pose07_08.covers q t hc hcell hq ht0 ht1
    · exact Pose08_08.covers q t hc hcell hq ht0 ht1
    · exact Pose09_08.covers q t hc hcell hq ht0 ht1
    · exact Pose10_08.covers q t hc hcell hq ht0 ht1
    · exact Pose11_08.covers q t hc hcell hq ht0 ht1
    · exact Pose12_08.covers q t hc hcell hq ht0 ht1
    · exact Pose13_08.covers q t hc hcell hq ht0 ht1
    · exact Pose14_08.covers q t hc hcell hq ht0 ht1
    · exact Pose15_08.covers q t hc hcell hq ht0 ht1
  owned_valid := by
    intro i q t hc hcell hq ht0 ht1
    fin_cases i
    · exact Group00.owned q t hc hcell hq ht0 ht1
    · exact Group01.owned q t hc hcell hq ht0 ht1
    · exact Group02.owned q t hc hcell hq ht0 ht1
    · exact Group03.owned q t hc hcell hq ht0 ht1
    · exact Group04.owned q t hc hcell hq ht0 ht1
    · exact Group05.owned q t hc hcell hq ht0 ht1
    · exact Group06.owned q t hc hcell hq ht0 ht1
    · exact Group07.owned q t hc hcell hq ht0 ht1
    · exact Group08.owned q t hc hcell hq ht0 ht1
    · exact Group09.owned q t hc hcell hq ht0 ht1
    · exact Group10.owned q t hc hcell hq ht0 ht1
    · exact Group11.owned q t hc hcell hq ht0 ht1
    · exact Group12.owned q t hc hcell hq ht0 ht1
    · exact Group13.owned q t hc hcell hq ht0 ht1
    · exact Group14.owned q t hc hcell hq ht0 ht1
    · exact Group15.owned q t hc hcell hq ht0 ht1

theorem «initialize» (cells : Owner → Fin 16) (hcells : Function.Injective cells)
    (m : Finset (Fin 16)) (himage : Finset.univ.image cells = m)
    (P : Packing 11 coverCap) (hchart : IsCharted P) (hocc : Occupies P m) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) (library.state cells) :=
  library.initialize cells hcells m himage P hchart hocc

end
end ElevenSquare.Pending.T03.Initialization.Library08
