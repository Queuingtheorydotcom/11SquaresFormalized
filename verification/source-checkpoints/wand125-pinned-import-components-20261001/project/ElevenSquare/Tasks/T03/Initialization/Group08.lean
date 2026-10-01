import ElevenSquare.Tasks.T03.Initialization.Owned08_00
import ElevenSquare.Tasks.T03.Initialization.Owned08_01
import ElevenSquare.Tasks.T03.Initialization.Owned08_02
import ElevenSquare.Tasks.T03.Initialization.Owned08_03
import ElevenSquare.Tasks.T03.Initialization.Owned08_04
import ElevenSquare.Tasks.T03.Initialization.Owned08_05
import ElevenSquare.Tasks.T03.Initialization.Owned08_06
import ElevenSquare.Tasks.T03.Initialization.Owned08_07
import ElevenSquare.Tasks.T03.Initialization.Owned08_08
import ElevenSquare.Pending.S05_OwnedHull

namespace ElevenSquare.Pending.T03.Initialization.Group08
noncomputable section

def vertices : List QPoint := [Owned08_00.point,Owned08_01.point,Owned08_02.point,Owned08_03.point,Owned08_04.point,Owned08_05.point,Owned08_06.point,Owned08_07.point,Owned08_08.point]

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 8 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rationalHull vertices ⊆ {p | OpenSquare q p} := by
  apply hull_owned_of_vertices
  intro v hv
  simp only [vertices, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Owned08_00.owned q t hc hcell hq ht0 ht1
  · exact Owned08_01.owned q t hc hcell hq ht0 ht1
  · exact Owned08_02.owned q t hc hcell hq ht0 ht1
  · exact Owned08_03.owned q t hc hcell hq ht0 ht1
  · exact Owned08_04.owned q t hc hcell hq ht0 ht1
  · exact Owned08_05.owned q t hc hcell hq ht0 ht1
  · exact Owned08_06.owned q t hc hcell hq ht0 ht1
  · exact Owned08_07.owned q t hc hcell hq ht0 ht1
  · exact Owned08_08.owned q t hc hcell hq ht0 ht1

end
end ElevenSquare.Pending.T03.Initialization.Group08
