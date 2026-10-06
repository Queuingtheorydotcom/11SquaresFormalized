import ElevenSquare.Tasks.T07.CaptureRoot
import ElevenSquare.Tasks.T07.CoordinateBridge
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! An exact geometric seed for the case-438 ownership order. A row centers
polygon encodes the closed nearest-site cell in physical unit coordinates;
the hull is empty until a strict ownership certificate promotes vertices. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def seedCap : ℚ := 387708359002281417731/100000000000000000000

def seedSite : Fin 16 → QPoint :=
  ![(104991/1000000,265837/2000000),
    (186601/500000,45503/1000000),
    (1267243/2000000,34689/250000),
    (1731123/2000000,25701/250000),
    (206181/2000000,400379/1000000),
    (742311/2000000,312933/1000000),
    (635257/1000000,166409/400000),
    (445439/500000,167763/500000),
    (54561/500000,332237/500000),
    (364743/1000000,233591/400000),
    (1257689/2000000,687067/1000000),
    (1793819/2000000,599621/1000000),
    (268877/2000000,224299/250000),
    (732757/2000000,215311/250000),
    (313399/500000,954497/1000000),
    (895009/1000000,1734163/2000000)]

theorem seedCap_cast : (seedCap : ℝ) = coverCap := by
  norm_num [seedCap, coverCap]

theorem seedSite_cast (i : Fin 16) : realPoint (seedSite i) = coverSite i := by
  fin_cases i <;> norm_num [seedSite, coverSite, realPoint]

def seedCellHalfplane (i j : Fin 16) : Halfplane :=
  let a := seedSite i
  let b := seedSite j
  { a := 2*(b.1-a.1), b := 2*(b.2-a.2),
    c := (seedCap-1)*(b.1^2+b.2^2-a.1^2-a.2^2) +
      (b.1-a.1)+(b.2-a.2) }

/-- Four coordinate bounds and all sixteen closed Voronoi comparisons.
The coefficients are rational although the physical center is real. -/
def seedCellPolygon (i : Fin 16) : Polygon :=
  [⟨-1, 0, -1/2⟩, ⟨1, 0, seedCap-1/2⟩,
    ⟨0, -1, -1/2⟩, ⟨0, 1, seedCap-1/2⟩] ++
      (List.finRange 16).map (seedCellHalfplane i)

theorem seedCellHalfplane_sound (i j : Fin 16) (p : Point)
    (h : coordinateDistanceSq (normalizeCenter p) (coverSite i) ≤
      coordinateDistanceSq (normalizeCenter p) (coverSite j)) :
    (seedCellHalfplane i j).contains p := by
  let A : ℝ := coverCap-1
  have hA : 0 < A := sub_pos.mpr coverCap_gt_one
  have hne : A ≠ 0 := ne_of_gt hA
  have hid : A*(coordinateDistanceSq (normalizeCenter p) (coverSite i) -
      coordinateDistanceSq (normalizeCenter p) (coverSite j)) =
      ((seedCellHalfplane i j).a : ℝ)*p.1 +
      ((seedCellHalfplane i j).b : ℝ)*p.2 -
      ((seedCellHalfplane i j).c : ℝ) := by
    rw [← seedSite_cast i, ← seedSite_cast j]
    dsimp [A, coordinateDistanceSq, normalizeCenter, seedCellHalfplane,
      realPoint]
    rw [← seedCap_cast]
    dsimp [seedCap]
    push_cast
    field_simp [show (coverCap-1) ≠ 0 from ne_of_gt (sub_pos.mpr coverCap_gt_one)] <;> ring
  have hmul : A*(coordinateDistanceSq (normalizeCenter p) (coverSite i) -
      coordinateDistanceSq (normalizeCenter p) (coverSite j)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hA.le (sub_nonpos.mpr h)
  dsimp only [Halfplane.contains]
  linarith only [hmul, hid]

theorem seedCellPolygon_sound (i : Fin 16) (p : Point)
    (hp : ClosedCell i (normalizeCenter p)) :
    p ∈ (seedCellPolygon i).carrier := by
  have hA : 0 < coverCap-1 := sub_pos.mpr coverCap_gt_one
  have hx0 : 1/2 ≤ p.1 := by
    have h := hp.1.1
    dsimp [InUnitBox, normalizeCenter] at h
    by_contra hn
    have hd : (p.1-1/2)/(coverCap-1) < 0 :=
      div_neg_of_neg_of_pos (by linarith) hA
    linarith
  have hx1 : p.1 ≤ coverCap-1/2 := by
    have h := hp.1.2.1
    dsimp [InUnitBox, normalizeCenter] at h
    have h' := (div_le_iff₀ hA).mp h
    linarith
  have hy0 : 1/2 ≤ p.2 := by
    have h := hp.1.2.2.1
    dsimp [InUnitBox, normalizeCenter] at h
    by_contra hn
    have hd : (p.2-1/2)/(coverCap-1) < 0 :=
      div_neg_of_neg_of_pos (by linarith) hA
    linarith
  have hy1 : p.2 ≤ coverCap-1/2 := by
    have h := hp.1.2.2.2
    dsimp [InUnitBox, normalizeCenter] at h
    have h' := (div_le_iff₀ hA).mp h
    linarith
  intro l hl
  simp only [seedCellPolygon, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hl
  rcases hl with (rfl | rfl | rfl | rfl) | ⟨j, _, rfl⟩
  · dsimp [Halfplane.contains]; norm_num; linarith
  · dsimp [Halfplane.contains]; push_cast; rw [seedCap_cast]; norm_num; linarith
  · dsimp [Halfplane.contains]; norm_num; linarith
  · dsimp [Halfplane.contains]; push_cast; rw [seedCap_cast]; norm_num; linarith
  · exact seedCellHalfplane_sound i j p (hp.2 j)

/-- The same exact closed cell expressed in the archived propagation field.
Multiplication by this rational factor converts a physical center to a field
center; no physical square is dilated. -/
def seedFieldScale : ℚ :=
  382000000000000000000/387708359002281417731

theorem seedFieldScale_cast : (seedFieldScale : ℝ) = fieldScale := by
  norm_num [seedFieldScale, fieldScale, coverCap]

def seedFieldHalfplane (l : Halfplane) : Halfplane :=
  { a := l.a, b := l.b, c := seedFieldScale*l.c }

def seedFieldCellPolygon (i : Fin 16) : Polygon :=
  (seedCellPolygon i).map seedFieldHalfplane

theorem seedFieldCellPolygon_sound (i : Fin 16) (p : Point)
    (hp : ClosedCell i (normalizeCenter p)) :
    toField p ∈ (seedFieldCellPolygon i).carrier := by
  have hphysical := seedCellPolygon_sound i p hp
  intro l hl
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
  have h := hphysical m hm
  have hscaled := mul_le_mul_of_nonneg_left h fieldScale_pos.le
  dsimp [Halfplane.contains, seedFieldHalfplane, toField] at hscaled ⊢
  push_cast at *
  rw [seedFieldScale_cast]
  nlinarith only [hscaled]

end
end ElevenSquare.Tasks.T07
