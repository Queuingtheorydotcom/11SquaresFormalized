import ElevenSquare.Tasks.T03.Initialization.Owned01_00
import ElevenSquare.Tasks.T03.Initialization.Owned01_01
import ElevenSquare.Tasks.T03.Initialization.Owned01_02
import ElevenSquare.Tasks.T03.Initialization.Owned01_03
import ElevenSquare.Tasks.T03.Initialization.Owned01_04
import ElevenSquare.Pending.S05_OwnedHull

namespace ElevenSquare.Pending.T03.Initialization.Group01
noncomputable section

def vertices : List QPoint := [Owned01_00.point,Owned01_01.point,Owned01_02.point,Owned01_03.point,Owned01_04.point]

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 1 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rationalHull vertices ⊆ {p | OpenSquare q p} := by
  apply hull_owned_of_vertices
  intro v hv
  simp only [vertices, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact Owned01_00.owned q t hc hcell hq ht0 ht1
  · exact Owned01_01.owned q t hc hcell hq ht0 ht1
  · exact Owned01_02.owned q t hc hcell hq ht0 ht1
  · exact Owned01_03.owned q t hc hcell hq ht0 ht1
  · exact Owned01_04.owned q t hc hcell hq ht0 ht1

end
end ElevenSquare.Pending.T03.Initialization.Group01
