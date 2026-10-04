import ElevenSquare.Pending.S07_CellPolygon
import ElevenSquare.Pending.S07_LabelData

/-! Pull back closed halfplanes under the exact four affine view maps.
This does not assume that the view maps permute Voronoi cell indices. -/
namespace ElevenSquare.Pending
noncomputable section

def viewPlane (g : Fin 4) (l : Halfplane) : Halfplane :=
  (![l, ⟨-l.a,l.b,l.c-l.a⟩, ⟨l.b,-l.a,l.c-l.a⟩, ⟨l.b,l.a,l.c⟩] : Fin 4 → Halfplane) g

theorem viewPlane_correct (g : Fin 4) (l : Halfplane) (p : Point) :
    (viewPlane g l).contains p ↔ l.contains (view g p) := by
  fin_cases g <;> simp [viewPlane, view, Halfplane.contains] <;>
    constructor <;> intro h <;> linarith

def viewPlanes (g : Fin 4) (P : Polygon) : Polygon := P.map (viewPlane g)

theorem viewPlanes_correct (g : Fin 4) (P : Polygon) (p : Point) :
    p ∈ (viewPlanes g P).carrier ↔ view g p ∈ P.carrier := by
  constructor
  · intro h l hl
    exact (viewPlane_correct g l p).mp (h _ (List.mem_map.mpr ⟨l,hl,rfl⟩))
  · intro h l hl
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
    exact (viewPlane_correct g m p).mpr (h m hm)

def fourViewPlanes (labels : Fin 4 → Fin 16) : Polygon :=
  (List.finRange 4).flatMap (fun g => viewPlanes g (cellPlanes (labels g)))

theorem fourViewPlanes_correct (labels : Fin 4 → Fin 16) (p : Point) :
    p ∈ (fourViewPlanes labels).carrier ↔ ∀ g, ClosedCell (labels g) (view g p) := by
  constructor
  · intro h g
    apply (cellPlanes_correct _ _).mp
    apply (viewPlanes_correct g _ p).mp
    intro l hl
    exact h l (List.mem_flatMap.mpr ⟨g, List.mem_finRange g, hl⟩)
  · intro h l hl
    obtain ⟨g, _, hl⟩ := List.mem_flatMap.mp hl
    exact (viewPlanes_correct g _ p).mpr ((cellPlanes_correct _ _).mpr (h g)) l hl

end
end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.viewPlane_correct
#print axioms ElevenSquare.Pending.fourViewPlanes_correct
