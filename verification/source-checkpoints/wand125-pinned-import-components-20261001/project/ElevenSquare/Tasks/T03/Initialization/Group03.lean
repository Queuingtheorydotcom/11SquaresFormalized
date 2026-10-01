import ElevenSquare.Tasks.T03.Initialization.Owned03_00
import ElevenSquare.Tasks.T03.Initialization.Owned03_01
import ElevenSquare.Tasks.T03.Initialization.Owned03_02
import ElevenSquare.Tasks.T03.Initialization.Owned03_03
import ElevenSquare.Tasks.T03.Initialization.Owned03_04
import ElevenSquare.Tasks.T03.Initialization.Owned03_05
import ElevenSquare.Tasks.T03.Initialization.Owned03_06
import ElevenSquare.Pending.S05_OwnedHull

namespace ElevenSquare.Pending.T03.Initialization.Group03
noncomputable section

def vertices : List QPoint := [Owned03_00.point,Owned03_01.point,Owned03_02.point,Owned03_03.point,Owned03_04.point,Owned03_05.point,Owned03_06.point]

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rationalHull vertices ⊆ {p | OpenSquare q p} := by
  apply hull_owned_of_vertices
  intro v hv
  simp only [vertices, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Owned03_00.owned q t hc hcell hq ht0 ht1
  · exact Owned03_01.owned q t hc hcell hq ht0 ht1
  · exact Owned03_02.owned q t hc hcell hq ht0 ht1
  · exact Owned03_03.owned q t hc hcell hq ht0 ht1
  · exact Owned03_04.owned q t hc hcell hq ht0 ht1
  · exact Owned03_05.owned q t hc hcell hq ht0 ht1
  · exact Owned03_06.owned q t hc hcell hq ht0 ht1

end
end ElevenSquare.Pending.T03.Initialization.Group03
