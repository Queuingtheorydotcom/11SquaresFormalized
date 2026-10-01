import ElevenSquare.Tasks.T03.Initialization.Owned06_00
import ElevenSquare.Tasks.T03.Initialization.Owned06_01
import ElevenSquare.Tasks.T03.Initialization.Owned06_02
import ElevenSquare.Tasks.T03.Initialization.Owned06_03
import ElevenSquare.Tasks.T03.Initialization.Owned06_04
import ElevenSquare.Pending.S05_OwnedHull

namespace ElevenSquare.Pending.T03.Initialization.Group06
noncomputable section

def vertices : List QPoint := [Owned06_00.point,Owned06_01.point,Owned06_02.point,Owned06_03.point,Owned06_04.point]

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 6 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rationalHull vertices ⊆ {p | OpenSquare q p} := by
  apply hull_owned_of_vertices
  intro v hv
  simp only [vertices, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact Owned06_00.owned q t hc hcell hq ht0 ht1
  · exact Owned06_01.owned q t hc hcell hq ht0 ht1
  · exact Owned06_02.owned q t hc hcell hq ht0 ht1
  · exact Owned06_03.owned q t hc hcell hq ht0 ht1
  · exact Owned06_04.owned q t hc hcell hq ht0 ht1

end
end ElevenSquare.Pending.T03.Initialization.Group06
