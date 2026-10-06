import ElevenSquare.Tasks.T07.CaptureSeedGeometry
import ElevenSquare.Cover
import ElevenSquare.Pending.S05_OwnedHull
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A compact, orientation independent source of one strictly owned point
per occupied nearest-site cell. The existing covering radius theorem certifies
these points directly, before any angular or residual-center propagation. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

/-- The rational physical image of the `i`th covering site. -/
def physicalSite (i : Fin 16) : QPoint :=
  ((seedCap-1)*(seedSite i).1+1/2,
   (seedCap-1)*(seedSite i).2+1/2)

theorem normalized_physicalSite (i : Fin 16) :
    normalizeCenter (realPoint (physicalSite i)) = coverSite i := by
  have hcap : coverCap-1 ≠ 0 := ne_of_gt (sub_pos.mpr coverCap_gt_one)
  have hsite := seedSite_cast i
  apply Prod.ext
  · have hi := congrArg Prod.fst hsite
    dsimp [normalizeCenter, realPoint, physicalSite] at *
    rw [← seedCap_cast]
    push_cast
    rw [hi]
    field_simp [show (seedCap : ℝ)-1 ≠ 0 by rwa [seedCap_cast]] <;> ring
  · have hi := congrArg Prod.snd hsite
    dsimp [normalizeCenter, realPoint, physicalSite] at *
    rw [← seedCap_cast]
    push_cast
    rw [hi]
    field_simp [show (seedCap : ℝ)-1 ≠ 0 by rwa [seedCap_cast]] <;> ring

theorem physicalSite_owned_of_closedCell (i : Fin 16) (q : UnitSquare)
    (hcell : ClosedCell i (normalizeCenter q.center)) :
    OpenSquare q (realPoint (physicalSite i)) := by
  have hr := closedCell_radius hcell
  have hd : coordinateDistanceSq (realPoint (physicalSite i)) q.center =
      (coverCap-1)^2 * coordinateDistanceSq (coverSite i) (normalizeCenter q.center) := by
    rw [normalized_distance, normalized_physicalSite]
  have hsym : coordinateDistanceSq (coverSite i) (normalizeCenter q.center) =
      coordinateDistanceSq (normalizeCenter q.center) (coverSite i) := by
    dsimp [coordinateDistanceSq]
    ring
  have hs : (coverCap-1)^2 * coordinateDistanceSq (normalizeCenter q.center)
      (coverSite i) ≤ (coverCap-1)^2 * coverRadius^2 :=
    mul_le_mul_of_nonneg_left hr (sq_nonneg _)
  have hstrict : (coverCap-1)^2 * coverRadius^2 < 1/4 := by
    norm_num [coverCap, coverRadius]
  apply open_of_normSq_lt
  rw [normSq_sub_eq_distance, hd, hsym]
  exact lt_of_le_of_lt hs hstrict

/-- The owner-ordered root with one guaranteed strict interior point per
square. This root is the exact closed Voronoi-cell seed; it introduces no
assumptions about the source branch tree. -/
def siteSeedFor (a : Owner → Fin 16) : PoseState where
  rows i := [{ lo := 0, hi := 1, centers := seedCellPolygon (a i) }]
  owned i := [physicalSite (a i)]

theorem siteSeedFor_holds {S : ℝ} (P : Packing 11 S)
    (a : Owner → Fin 16)
    (hchart : IsCharted P)
    (hcell : ∀ i, ClosedCell (a i)
      (normalizeCenter (P.squares i).center)) :
    StateHolds P (siteSeedFor a) := by
  constructor
  · intro i
    obtain ⟨t, h0, h1, haxis⟩ := hchart i
    refine ⟨{ lo := 0, hi := 1, centers := seedCellPolygon (a i) },
      by simp [siteSeedFor], ?_⟩
    refine ⟨seedCellPolygon_sound _ _ (hcell i), t, h0, h1, ?_, ?_, haxis⟩
    · simpa using h0
    · simpa using h1
  · intro i
    apply hull_owned_of_vertices
    intro v hv
    simp only [siteSeedFor, List.mem_cons, List.not_mem_nil, or_false] at hv
    subst v
    exact physicalSite_owned_of_closedCell _ _ (hcell i)

end
end ElevenSquare.Tasks.T07
