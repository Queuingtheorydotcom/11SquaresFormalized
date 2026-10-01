import ElevenSquare.Tasks.T03.SeedLibrary
import ElevenSquare.Tasks.T03.Initialization.Pose00_64
import ElevenSquare.Tasks.T03.Initialization.Pose01_64
import ElevenSquare.Tasks.T03.Initialization.Pose02_64
import ElevenSquare.Tasks.T03.Initialization.Pose03_64
import ElevenSquare.Tasks.T03.Initialization.Pose04_64
import ElevenSquare.Tasks.T03.Initialization.Pose05_64
import ElevenSquare.Tasks.T03.Initialization.Pose06_64
import ElevenSquare.Tasks.T03.Initialization.Pose07_64
import ElevenSquare.Tasks.T03.Initialization.Pose08_64
import ElevenSquare.Tasks.T03.Initialization.Pose09_64
import ElevenSquare.Tasks.T03.Initialization.Pose10_64
import ElevenSquare.Tasks.T03.Initialization.Pose11_64
import ElevenSquare.Tasks.T03.Initialization.Pose12_64
import ElevenSquare.Tasks.T03.Initialization.Pose13_64
import ElevenSquare.Tasks.T03.Initialization.Pose14_64
import ElevenSquare.Tasks.T03.Initialization.Pose15_64
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

namespace ElevenSquare.Pending.T03.Initialization.Library64
noncomputable section

def library : InitializationLibrary where
  rows := ![Pose00_64.template.rows,Pose01_64.template.rows,Pose02_64.template.rows,Pose03_64.template.rows,Pose04_64.template.rows,Pose05_64.template.rows,Pose06_64.template.rows,Pose07_64.template.rows,Pose08_64.template.rows,Pose09_64.template.rows,Pose10_64.template.rows,Pose11_64.template.rows,Pose12_64.template.rows,Pose13_64.template.rows,Pose14_64.template.rows,Pose15_64.template.rows]
  owned := ![Group00.vertices,Group01.vertices,Group02.vertices,Group03.vertices,Group04.vertices,Group05.vertices,Group06.vertices,Group07.vertices,Group08.vertices,Group09.vertices,Group10.vertices,Group11.vertices,Group12.vertices,Group13.vertices,Group14.vertices,Group15.vertices]
  rows_valid := by
    intro i q t hc hcell hq ht0 ht1
    fin_cases i
    · exact Pose00_64.covers q t hc hcell hq ht0 ht1
    · exact Pose01_64.covers q t hc hcell hq ht0 ht1
    · exact Pose02_64.covers q t hc hcell hq ht0 ht1
    · exact Pose03_64.covers q t hc hcell hq ht0 ht1
    · exact Pose04_64.covers q t hc hcell hq ht0 ht1
    · exact Pose05_64.covers q t hc hcell hq ht0 ht1
    · exact Pose06_64.covers q t hc hcell hq ht0 ht1
    · exact Pose07_64.covers q t hc hcell hq ht0 ht1
    · exact Pose08_64.covers q t hc hcell hq ht0 ht1
    · exact Pose09_64.covers q t hc hcell hq ht0 ht1
    · exact Pose10_64.covers q t hc hcell hq ht0 ht1
    · exact Pose11_64.covers q t hc hcell hq ht0 ht1
    · exact Pose12_64.covers q t hc hcell hq ht0 ht1
    · exact Pose13_64.covers q t hc hcell hq ht0 ht1
    · exact Pose14_64.covers q t hc hcell hq ht0 ht1
    · exact Pose15_64.covers q t hc hcell hq ht0 ht1
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
end ElevenSquare.Pending.T03.Initialization.Library64
