import ElevenSquare.Tasks.T03.Initialization.Owned02_00
import ElevenSquare.Tasks.T03.Initialization.Owned02_01
import ElevenSquare.Tasks.T03.Initialization.Owned02_02
import ElevenSquare.Tasks.T03.Initialization.Owned02_03
import ElevenSquare.Tasks.T03.Initialization.Owned02_04
import ElevenSquare.Tasks.T03.Initialization.Owned02_05
import ElevenSquare.Tasks.T03.Initialization.Owned02_06
import ElevenSquare.Pending.S05_OwnedHull

namespace ElevenSquare.Pending.T03.Initialization.Group02
noncomputable section

def vertices : List QPoint := [Owned02_00.point,Owned02_01.point,Owned02_02.point,Owned02_03.point,Owned02_04.point,Owned02_05.point,Owned02_06.point]

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 2 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rationalHull vertices ⊆ {p | OpenSquare q p} := by
  apply hull_owned_of_vertices
  intro v hv
  simp only [vertices, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Owned02_00.owned q t hc hcell hq ht0 ht1
  · exact Owned02_01.owned q t hc hcell hq ht0 ht1
  · exact Owned02_02.owned q t hc hcell hq ht0 ht1
  · exact Owned02_03.owned q t hc hcell hq ht0 ht1
  · exact Owned02_04.owned q t hc hcell hq ht0 ht1
  · exact Owned02_05.owned q t hc hcell hq ht0 ht1
  · exact Owned02_06.owned q t hc hcell hq ht0 ht1

end
end ElevenSquare.Pending.T03.Initialization.Group02
