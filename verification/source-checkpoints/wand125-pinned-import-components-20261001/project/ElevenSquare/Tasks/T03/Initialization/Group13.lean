import ElevenSquare.Tasks.T03.Initialization.Owned13_00
import ElevenSquare.Tasks.T03.Initialization.Owned13_01
import ElevenSquare.Tasks.T03.Initialization.Owned13_02
import ElevenSquare.Tasks.T03.Initialization.Owned13_03
import ElevenSquare.Tasks.T03.Initialization.Owned13_04
import ElevenSquare.Tasks.T03.Initialization.Owned13_05
import ElevenSquare.Tasks.T03.Initialization.Owned13_06
import ElevenSquare.Pending.S05_OwnedHull

namespace ElevenSquare.Pending.T03.Initialization.Group13
noncomputable section

def vertices : List QPoint := [Owned13_00.point,Owned13_01.point,Owned13_02.point,Owned13_03.point,Owned13_04.point,Owned13_05.point,Owned13_06.point]

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 13 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rationalHull vertices ⊆ {p | OpenSquare q p} := by
  apply hull_owned_of_vertices
  intro v hv
  simp only [vertices, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Owned13_00.owned q t hc hcell hq ht0 ht1
  · exact Owned13_01.owned q t hc hcell hq ht0 ht1
  · exact Owned13_02.owned q t hc hcell hq ht0 ht1
  · exact Owned13_03.owned q t hc hcell hq ht0 ht1
  · exact Owned13_04.owned q t hc hcell hq ht0 ht1
  · exact Owned13_05.owned q t hc hcell hq ht0 ht1
  · exact Owned13_06.owned q t hc hcell hq ht0 ht1

end
end ElevenSquare.Pending.T03.Initialization.Group13
