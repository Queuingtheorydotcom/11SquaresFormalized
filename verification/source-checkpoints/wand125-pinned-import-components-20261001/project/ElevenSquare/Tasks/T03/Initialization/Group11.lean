import ElevenSquare.Tasks.T03.Initialization.Owned11_00
import ElevenSquare.Tasks.T03.Initialization.Owned11_01
import ElevenSquare.Tasks.T03.Initialization.Owned11_02
import ElevenSquare.Tasks.T03.Initialization.Owned11_03
import ElevenSquare.Tasks.T03.Initialization.Owned11_04
import ElevenSquare.Tasks.T03.Initialization.Owned11_05
import ElevenSquare.Tasks.T03.Initialization.Owned11_06
import ElevenSquare.Tasks.T03.Initialization.Owned11_07
import ElevenSquare.Pending.S05_OwnedHull

namespace ElevenSquare.Pending.T03.Initialization.Group11
noncomputable section

def vertices : List QPoint := [Owned11_00.point,Owned11_01.point,Owned11_02.point,Owned11_03.point,Owned11_04.point,Owned11_05.point,Owned11_06.point,Owned11_07.point]

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 11 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rationalHull vertices ⊆ {p | OpenSquare q p} := by
  apply hull_owned_of_vertices
  intro v hv
  simp only [vertices, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Owned11_00.owned q t hc hcell hq ht0 ht1
  · exact Owned11_01.owned q t hc hcell hq ht0 ht1
  · exact Owned11_02.owned q t hc hcell hq ht0 ht1
  · exact Owned11_03.owned q t hc hcell hq ht0 ht1
  · exact Owned11_04.owned q t hc hcell hq ht0 ht1
  · exact Owned11_05.owned q t hc hcell hq ht0 ht1
  · exact Owned11_06.owned q t hc hcell hq ht0 ht1
  · exact Owned11_07.owned q t hc hcell hq ht0 ht1

end
end ElevenSquare.Pending.T03.Initialization.Group11
