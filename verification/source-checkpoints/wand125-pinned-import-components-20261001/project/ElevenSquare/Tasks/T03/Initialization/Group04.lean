import ElevenSquare.Tasks.T03.Initialization.Owned04_00
import ElevenSquare.Tasks.T03.Initialization.Owned04_01
import ElevenSquare.Tasks.T03.Initialization.Owned04_02
import ElevenSquare.Tasks.T03.Initialization.Owned04_03
import ElevenSquare.Tasks.T03.Initialization.Owned04_04
import ElevenSquare.Tasks.T03.Initialization.Owned04_05
import ElevenSquare.Tasks.T03.Initialization.Owned04_06
import ElevenSquare.Tasks.T03.Initialization.Owned04_07
import ElevenSquare.Pending.S05_OwnedHull

namespace ElevenSquare.Pending.T03.Initialization.Group04
noncomputable section

def vertices : List QPoint := [Owned04_00.point,Owned04_01.point,Owned04_02.point,Owned04_03.point,Owned04_04.point,Owned04_05.point,Owned04_06.point,Owned04_07.point]

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 4 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rationalHull vertices ⊆ {p | OpenSquare q p} := by
  apply hull_owned_of_vertices
  intro v hv
  simp only [vertices, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Owned04_00.owned q t hc hcell hq ht0 ht1
  · exact Owned04_01.owned q t hc hcell hq ht0 ht1
  · exact Owned04_02.owned q t hc hcell hq ht0 ht1
  · exact Owned04_03.owned q t hc hcell hq ht0 ht1
  · exact Owned04_04.owned q t hc hcell hq ht0 ht1
  · exact Owned04_05.owned q t hc hcell hq ht0 ht1
  · exact Owned04_06.owned q t hc hcell hq ht0 ht1
  · exact Owned04_07.owned q t hc hcell hq ht0 ht1

end
end ElevenSquare.Pending.T03.Initialization.Group04
