import ElevenSquare.Tasks.T03.Initialization.Owned07_00
import ElevenSquare.Tasks.T03.Initialization.Owned07_01
import ElevenSquare.Tasks.T03.Initialization.Owned07_02
import ElevenSquare.Tasks.T03.Initialization.Owned07_03
import ElevenSquare.Tasks.T03.Initialization.Owned07_04
import ElevenSquare.Tasks.T03.Initialization.Owned07_05
import ElevenSquare.Tasks.T03.Initialization.Owned07_06
import ElevenSquare.Tasks.T03.Initialization.Owned07_07
import ElevenSquare.Tasks.T03.Initialization.Owned07_08
import ElevenSquare.Tasks.T03.Initialization.Owned07_09
import ElevenSquare.Pending.S05_OwnedHull

namespace ElevenSquare.Pending.T03.Initialization.Group07
noncomputable section

def vertices : List QPoint := [Owned07_00.point,Owned07_01.point,Owned07_02.point,Owned07_03.point,Owned07_04.point,Owned07_05.point,Owned07_06.point,Owned07_07.point,Owned07_08.point,Owned07_09.point]

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rationalHull vertices ⊆ {p | OpenSquare q p} := by
  apply hull_owned_of_vertices
  intro v hv
  simp only [vertices, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Owned07_00.owned q t hc hcell hq ht0 ht1
  · exact Owned07_01.owned q t hc hcell hq ht0 ht1
  · exact Owned07_02.owned q t hc hcell hq ht0 ht1
  · exact Owned07_03.owned q t hc hcell hq ht0 ht1
  · exact Owned07_04.owned q t hc hcell hq ht0 ht1
  · exact Owned07_05.owned q t hc hcell hq ht0 ht1
  · exact Owned07_06.owned q t hc hcell hq ht0 ht1
  · exact Owned07_07.owned q t hc hcell hq ht0 ht1
  · exact Owned07_08.owned q t hc hcell hq ht0 ht1
  · exact Owned07_09.owned q t hc hcell hq ht0 ht1

end
end ElevenSquare.Pending.T03.Initialization.Group07
