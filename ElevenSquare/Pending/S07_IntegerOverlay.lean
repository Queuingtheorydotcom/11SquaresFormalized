import ElevenSquare.Pending.S07_IntegerPlanes
namespace ElevenSquare.Pending

def integerBoxPlanes : List IntegerPlane := [⟨-1,0,0⟩,⟨1,0,1⟩,⟨0,-1,0⟩,⟨0,1,1⟩]
def IntegerCarrier (ls : List IntegerPlane) : Set Point :=
  {p | ∀ l ∈ ls, l.rational.contains p}
def integerCellPlanes (i : Fin 16) : List IntegerPlane :=
  integerBoxPlanes ++ (List.finRange 16).map
    (fun j => integerBisector (integerSite i) (integerSite j))

theorem integerBoxPlanes_correct (p : Point) :
    p ∈ IntegerCarrier integerBoxPlanes ↔ InUnitBox p := by
  simp [IntegerCarrier, integerBoxPlanes, IntegerPlane.rational, Halfplane.contains, InUnitBox]

theorem integerCellPlanes_correct (i : Fin 16) (p : Point) :
    p ∈ IntegerCarrier (integerCellPlanes i) ↔ ClosedCell i p := by
  constructor
  · intro h
    refine ⟨(integerBoxPlanes_correct p).mp ?_, ?_⟩
    · intro l hl
      exact h l (List.mem_append.mpr (Or.inl hl))
    · intro j
      rw [integerSite_correct i, integerSite_correct j]
      apply (integerBisector_correct _ _ p).mp
      exact h _ (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩)))
  · intro h l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact (integerBoxPlanes_correct p).mpr h.1 l hl
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hl
      apply (integerBisector_correct _ _ p).mpr
      rw [← integerSite_correct i, ← integerSite_correct j]
      exact h.2 j

def integerViewPlanes (g : Fin 4) (ls : List IntegerPlane) : List IntegerPlane :=
  ls.map (IntegerPlane.view g)

theorem integerViewPlanes_correct (g : Fin 4) (ls : List IntegerPlane) (p : Point) :
    p ∈ IntegerCarrier (integerViewPlanes g ls) ↔ view g p ∈ IntegerCarrier ls := by
  constructor
  · intro h l hl
    apply (viewPlane_correct g l.rational p).mp
    rw [← IntegerPlane.view_correct]
    exact h _ (List.mem_map.mpr ⟨l,hl,rfl⟩)
  · intro h l hl
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
    rw [IntegerPlane.view_correct]
    exact (viewPlane_correct g m.rational p).mpr (h m hm)

def integerOverlayPlanes (labels : Fin 4 → Fin 16) : List IntegerPlane :=
  (List.finRange 4).flatMap (fun g => integerViewPlanes g (integerCellPlanes (labels g)))

theorem integerOverlayPlanes_correct (labels : Fin 4 → Fin 16) (p : Point) :
    p ∈ IntegerCarrier (integerOverlayPlanes labels) ↔
      ∀ g, ClosedCell (labels g) (view g p) := by
  constructor
  · intro h g
    apply (integerCellPlanes_correct _ _).mp
    apply (integerViewPlanes_correct g _ p).mp
    intro l hl
    exact h l (List.mem_flatMap.mpr ⟨g,List.mem_finRange g,hl⟩)
  · intro h l hl
    obtain ⟨g, _, hl⟩ := List.mem_flatMap.mp hl
    exact (integerViewPlanes_correct g _ p).mpr ((integerCellPlanes_correct _ _).mpr (h g)) l hl

structure FractionPoint where
  nx : ℤ
  dx : ℤ
  ny : ℤ
  dy : ℤ
  deriving DecidableEq, Inhabited

def FractionPoint.rational (q : FractionPoint) : QPoint := (q.nx/q.dx,q.ny/q.dy)
def FractionPoint.fits (q : FractionPoint) (ls : List IntegerPlane) : Bool :=
  ls.all (fun l => l.fractionCheck q.nx q.dx q.ny q.dy)

theorem FractionPoint.fits_sound (q : FractionPoint) (ls : List IntegerPlane)
    (h : q.fits ls = true) : realPoint q.rational ∈ IntegerCarrier ls := by
  intro l hl
  exact l.fractionCheck_sound _ _ _ _ ((List.all_eq_true.mp h) l hl)

def integerHullCheck (ls : List IntegerPlane) (qs : List FractionPoint) : Bool :=
  qs.all (fun q => q.fits ls)

theorem integerHullCheck_sound (ls : List IntegerPlane) (qs : List FractionPoint)
    (h : integerHullCheck ls qs = true) :
    rationalHull (qs.map FractionPoint.rational) ⊆ IntegerCarrier ls := by
  have heq : IntegerCarrier ls = Polygon.carrier (ls.map IntegerPlane.rational) := by
    ext p
    simp [IntegerCarrier, Polygon.carrier]
  rw [heq]
  apply rationalHull_in_polygon
  intro q hq
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
  rw [← heq]
  exact r.fits_sound ls ((List.all_eq_true.mp h) r hr)

theorem integerHullCheck_overlay (labels : Fin 4 → Fin 16) (qs : List FractionPoint)
    (h : integerHullCheck (integerOverlayPlanes labels) qs = true) (p : Point)
    (hp : p ∈ rationalHull (qs.map FractionPoint.rational)) :
    ∀ g, ClosedCell (labels g) (view g p) :=
  (integerOverlayPlanes_correct labels p).mp (integerHullCheck_sound _ _ h hp)

end ElevenSquare.Pending
#print axioms ElevenSquare.Pending.integerOverlayPlanes_correct
#print axioms ElevenSquare.Pending.integerHullCheck_overlay
