import ElevenSquare.Tasks.T03.CellGeometry

namespace ElevenSquare.Pending.T03
noncomputable section

def cellPlanes (i : Fin 16) : List IntegerPlane :=
  [⟨-1,0,0⟩,⟨1,0,1⟩,⟨0,-1,0⟩,⟨0,1,1⟩] ++
    (List.finRange 16).map (fun j => integerBisector (integerSite i) (integerSite j))

theorem cellPlanes_correct (i : Fin 16) (p : Point) :
    p ∈ IntegerCarrier (cellPlanes i) ↔ ClosedCell i p := by
  change (∀ l ∈ cellPlanes i, l.holds p) ↔ _
  simp only [cellPlanes, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, and_true, List.forall_mem_map_iff, List.mem_finRange,
    true_implies, integerBisector_correct, ← integerSite_correct]
  simp [IntegerPlane.holds, ClosedCell, InUnitBox]

/-- Pull a normalized cell inequality back to the actual center coordinates. -/
def physicalPlane (l : IntegerPlane) : IntegerPlane :=
  ⟨200000000000000000000*l.a,200000000000000000000*l.b,
    575416718004562835462*l.c+100000000000000000000*(l.a+l.b)⟩

theorem physicalPlane_correct (l : IntegerPlane) (p : Point) :
    (physicalPlane l).holds p ↔ l.holds (normalizeCenter p) := by
  have he : ((physicalPlane l).a:ℝ)*p.1+((physicalPlane l).b:ℝ)*p.2-
      ((physicalPlane l).c:ℝ) = (575416718004562835462:ℝ)*
      ((l.a:ℝ)*(normalizeCenter p).1+(l.b:ℝ)*(normalizeCenter p).2-(l.c:ℝ)) := by
    dsimp [physicalPlane, normalizeCenter, coverCap]
    push_cast
    norm_num
    ring
  dsimp [IntegerPlane.holds]
  constructor <;> intro h <;> nlinarith only [he,h]

def physicalCell (i : Fin 16) : List IntegerPlane :=
  (cellPlanes i).map physicalPlane

theorem physicalCell_correct (i : Fin 16) (p : Point) :
    p ∈ IntegerCarrier (physicalCell i) ↔ ClosedCell i (normalizeCenter p) := by
  rw [← cellPlanes_correct]
  simp [physicalCell, IntegerCarrier, physicalPlane_correct]

end
end ElevenSquare.Pending.T03
