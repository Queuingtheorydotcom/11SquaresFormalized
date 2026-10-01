import ElevenSquare.Tasks.T02.Root
import ElevenSquare.Pending.S05_Trace

/-!
# Nonempty, unconditional baseline ownership seeds

Every occupied closed cell owns a small rational square about its physical
cover site. The radius proof comes from the already verified cover, not from
an ownership receipt. These conservative seeds are not a claim that the larger
wall-aware hulls in the historical certificates have been formalized.
-/

namespace ElevenSquare.Tasks.T02
open ElevenSquare.Pending
noncomputable section

def baselinePhysicalSite (i : Fin 16) : QPoint :=
  (1/2 + (baselineRationalCap - 1) * (baselineRationalSite i).1,
   1/2 + (baselineRationalCap - 1) * (baselineRationalSite i).2)

theorem baselinePhysicalSite_normalize (i : Fin 16) :
    normalizeCenter (realPoint (baselinePhysicalSite i)) = coverSite i := by
  have hu : coverCap - 1 ≠ 0 := ne_of_gt (sub_pos.mpr coverCap_gt_one)
  have hr := baselineRationalSite_cast i
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only [realPoint] at hx hy
  dsimp only [normalizeCenter, baselinePhysicalSite, realPoint]
  push_cast
  rw [baselineRationalCap_cast, hx, hy]
  ext <;> dsimp <;> field_simp [hu] <;> ring

theorem baseline_site_distance_bound (i : Fin 16) (p : Point)
    (h : ClosedCell i (normalizeCenter p)) :
    normSq (realPoint (baselinePhysicalSite i) - p) < 31/125 := by
  have hd := closedCell_radius h
  have hm := mul_le_mul_of_nonneg_left hd (sq_nonneg (coverCap - 1))
  have he := normalized_distance p (realPoint (baselinePhysicalSite i))
  rw [baselinePhysicalSite_normalize] at he
  have hc : (coverCap - 1)^2 * coverRadius^2 < 31/125 := by
    norm_num [coverCap, coverRadius]
  have hn : normSq (realPoint (baselinePhysicalSite i) - p) =
      coordinateDistanceSq p (realPoint (baselinePhysicalSite i)) := by
    dsimp [normSq, dot, coordinateDistanceSq]
    ring
  rw [hn, he]
  exact lt_of_le_of_lt hm hc

/-- Four distinct rational vertices; no wall or orientation assumption is used. -/
def baselineSeedVertices (i : Fin 16) : List QPoint :=
  let c := baselinePhysicalSite i
  [(c.1 - 1/2000, c.2 - 1/2000), (c.1 + 1/2000, c.2 - 1/2000),
   (c.1 + 1/2000, c.2 + 1/2000), (c.1 - 1/2000, c.2 + 1/2000)]

theorem baseline_seed_vertices_owned (q : UnitSquare) (i : Fin 16)
    (h : ClosedCell i (normalizeCenter q.center)) :
    ∀ v ∈ baselineSeedVertices i, OpenSquare q (realPoint v) := by
  have hd := baseline_site_distance_bound i q.center h
  let c := realPoint (baselinePhysicalSite i)
  change (c.1 - q.center.1) * (c.1 - q.center.1) +
    (c.2 - q.center.2) * (c.2 - q.center.2) < 31/125 at hd
  have hx : -(1/2:ℝ) < c.1 - q.center.1 ∧ c.1 - q.center.1 < 1/2 := by
    constructor <;> nlinarith [sq_nonneg (c.2 - q.center.2)]
  have hy : -(1/2:ℝ) < c.2 - q.center.2 ∧ c.2 - q.center.2 < 1/2 := by
    constructor <;> nlinarith [sq_nonneg (c.1 - q.center.1)]
  dsimp only [c, realPoint] at hd hx hy
  intro v hv
  apply open_of_normSq_lt
  simp only [baselineSeedVertices, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  all_goals
    dsimp [normSq, dot, realPoint]
    push_cast
    nlinarith [hx.1, hx.2, hy.1, hy.2]

def baselineSeedRoot (m : Finset (Fin 16)) : PoseState where
  rows := (baselineRoot m).rows
  owned := fun i => baselineSeedVertices (baselineRoles m i)

theorem baseline_seed_root_initialized {S : ℝ} (P : Packing 11 S)
    (m : Finset (Fin 16)) (hc : IsCharted P) (hocc : Occupies P m) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) (baselineSeedRoot m) := by
  have hm := baseline_occupies_card hocc
  obtain ⟨perm, hcell⟩ := baseline_relabel_to_roles P (baselineRoles m)
    (baselineRoles_injective hm) ((baselineRoles_image hm).symm ▸ hocc)
  refine ⟨perm, ?_, ?_⟩
  · intro i
    refine ⟨⟨0, 1, baselineCellPolygon (baselineRoles m i)⟩,
      by simp [baselineSeedRoot, baselineRoot], ?_⟩
    refine ⟨baselineCellPolygon_contains (hcell i), ?_⟩
    obtain ⟨t, ht0, ht1, haxis⟩ := hc (perm i)
    exact ⟨t, ht0, ht1, by simpa using ht0, by simpa using ht1, haxis⟩
  · intro i
    exact hull_owned_of_vertices _ _
      (baseline_seed_vertices_owned _ _ (hcell i))

end
end ElevenSquare.Tasks.T02
