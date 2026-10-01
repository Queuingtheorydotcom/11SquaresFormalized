import ElevenSquare.Tasks.T03.Wand125.Geometry
import ElevenSquare.Cover
import ElevenSquare.Tasks.T03.Wand125.Upstream.S11Opt.Cells

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace ElevenSquare.Pending.T03.Wand125
noncomputable section
open SquarePacking.S11Opt

theorem cap_eq : coverCap = Ux := by norm_num [coverCap, Ux]

theorem site_eq (i : Fin 16) :
    PU i = (1 / 2 + (coverCap - 1) * (coverSite i).1,
            1 / 2 + (coverCap - 1) * (coverSite i).2) := by
  fin_cases i
  · change ((80206788320008528328995421 / 100000000000000000000000000 : ℝ), (176483527032089485245355847 / 200000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (104991 / 1000000), 1 / 2 + (coverCap - 1) * (265837 / 2000000))
    norm_num [coverCap]
  · change ((78686667498184714830022331 / 50000000000000000000000000 : ℝ), (63091593459680811351013693 / 100000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (186601 / 500000), 1 / 2 + (coverCap - 1) * (45503 / 1000000))
    norm_num [coverCap]
  · change ((464596403987128110649685633 / 200000000000000000000000000 : ℝ), (22480315265430140099670659 / 25000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (1267243 / 2000000), 1 / 2 + (coverCap - 1) * (34689 / 250000))
    norm_num [coverCap]
  · change ((598058557561106414706741913 / 200000000000000000000000000 : ℝ), (19894392534717634717104431 / 25000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (1731123 / 2000000), 1 / 2 + (coverCap - 1) * (25701 / 250000))
    norm_num [coverCap]
  · change ((159319997167449384989195311 / 200000000000000000000000000 : ℝ), (165192385068974431749720049 / 100000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (206181 / 2000000), 1 / 2 + (coverCap - 1) * (400379 / 1000000))
    norm_num [coverCap]
  · change ((313569079679342521477316341 / 200000000000000000000000000 : ℝ), (140033439907660930894815023 / 100000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (742311 / 2000000), 1 / 2 + (coverCap - 1) * (312933 / 1000000))
    norm_num [coverCap]
  · change ((232768749014712286583541867 / 100000000000000000000000000 : ℝ), (67877260313210648443197979 / 40000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (635257 / 1000000), 1 / 2 + (coverCap - 1) * (166409 / 400000))
    norm_num [coverCap]
  · change ((153156523725617232432678909 / 50000000000000000000000000 : ℝ), (73266817431299737482805753 / 50000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (445439 / 500000), 1 / 2 + (coverCap - 1) * (167763 / 500000))
    norm_num [coverCap]
  · change ((40697655775523476432821091 / 50000000000000000000000000 : ℝ), (120587362069840971382694247 / 50000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (54561 / 500000), 1 / 2 + (coverCap - 1) * (332237 / 500000))
    norm_num [coverCap]
  · change ((154939609987569131147458133 / 100000000000000000000000000 : ℝ), (87206083287701918649202021 / 40000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (364743 / 1000000), 1 / 2 + (coverCap - 1) * (233591 / 400000))
    norm_num [coverCap]
  · change ((461847638325220313984683659 / 200000000000000000000000000 : ℝ), (247674919094620486836184977 / 100000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (1257689 / 2000000), 1 / 2 + (coverCap - 1) * (687067 / 1000000))
    norm_num [coverCap]
  · change ((616096720837113450472804689 / 200000000000000000000000000 : ℝ), (222515973933306985981279951 / 100000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (1793819 / 2000000), 1 / 2 + (coverCap - 1) * (599621 / 1000000))
    norm_num [coverCap]
  · change ((177358160443456420755258087 / 200000000000000000000000000 : ℝ), (77032697215852719715645569 / 25000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (268877 / 2000000), 1 / 2 + (coverCap - 1) * (224299 / 250000))
    norm_num [coverCap]
  · change ((310820314017434724812314367 / 200000000000000000000000000 : ℝ), (74446774485140214333079341 / 25000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (732757 / 2000000), 1 / 2 + (coverCap - 1) * (215311 / 250000))
    norm_num [coverCap]
  · change ((115167512002955994035477669 / 50000000000000000000000000 : ℝ), (324616765542600606379986307 / 100000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (313399 / 500000), 1 / 2 + (coverCap - 1) * (954497 / 1000000))
    norm_num [coverCap]
  · change ((307501570682272889402004579 / 100000000000000000000000000 : ℝ), (598933190972473350216644153 / 200000000000000000000000000 : ℝ)) =
      (1 / 2 + (coverCap - 1) * (895009 / 1000000), 1 / 2 + (coverCap - 1) * (1734163 / 2000000))
    norm_num [coverCap]

theorem site_distance (p : Point) (i : Fin 16) :
    (p.1 - (PU i).1)^2 + (p.2 - (PU i).2)^2 =
      (coverCap - 1)^2 * coordinateDistanceSq (normalizeCenter p) (coverSite i) := by
  rw [site_eq]
  have h : coverCap - 1 ≠ 0 := ne_of_gt (sub_pos.mpr coverCap_gt_one)
  simp only [coordinateDistanceSq, normalizeCenter]
  field_simp [h]
  <;> ring

theorem closedCell_to_inCell {i : Fin 16} {p : Point}
    (h : ClosedCell i (normalizeCenter p)) : InCellU i.val p := by
  intro j
  have e : PUn i.val = PU i := by simp [PUn, Nat.mod_eq_of_lt i.isLt]
  rw [e, site_distance, site_distance]
  exact mul_le_mul_of_nonneg_left (h.2 j) (sq_nonneg _)

def cellOf (j : ℕ) : Fin 16 := ⟨j % 16, Nat.mod_lt j (by decide)⟩

def cellsOf (J : List ℕ) : Finset (Fin 16) := (J.map cellOf).toFinset

/-- Occupancy in the original closed cells gives an actual realization in the
imported model. The bounds rule out aliasing through the natural-number labels. -/
theorem realizes_of_occupies (P : Packing 11 coverCap) (J : List ℕ)
    (hJ : ∀ j ∈ J, j < 16) (ho : Occupies P (cellsOf J)) : Realizes J := by
  classical
  obtain ⟨a, ha, himage, hc⟩ := ho
  have hex : ∀ j ∈ J, ∃ i, a i = cellOf j := by
    intro j hj
    have hm : cellOf j ∈ cellsOf J := by
      simp only [cellsOf, List.mem_toFinset, List.mem_map]
      exact ⟨j, hj, rfl⟩
    rw [← himage, Finset.mem_image] at hm
    obtain ⟨i, _, hi⟩ := hm
    exact ⟨i, hi⟩
  let σ : ℕ → Fin 11 := fun j => if h : j ∈ J then Classical.choose (hex j h) else 0
  have hσ : ∀ j ∈ J, a (σ j) = cellOf j := by
    intro j hj
    simpa [σ, hj] using Classical.choose_spec (hex j hj)
  refine ⟨11, fun i => (P.squares i).center, fun i => angle (P.squares i), ?_, ?_, σ, ?_, ?_⟩
  · intro i p hp
    rw [← cap_eq]
    exact P.contained i p ((closed_iff _ _).mpr hp)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    exact P.interior_disjoint i j hij p
      ⟨(open_iff _ _).mpr hi, (open_iff _ _).mpr hj⟩
  · intro j hj k hk he
    have e : cellOf j = cellOf k := (hσ j hj).symm.trans ((congrArg a he).trans (hσ k hk))
    have ev := congrArg Fin.val e
    simpa [cellOf, Nat.mod_eq_of_lt (hJ j hj), Nat.mod_eq_of_lt (hJ k hk)] using ev
  · intro j hj
    have hh := closedCell_to_inCell (hc (σ j))
    rw [hσ j hj] at hh
    simpa [cellOf, Nat.mod_eq_of_lt (hJ j hj)] using hh

theorem excludes_occupancy (J : List ℕ) (hJ : ∀ j ∈ J, j < 16)
    (h : CaseExcluded J) (P : Packing 11 coverCap) : ¬ Occupies P (cellsOf J) :=
  fun ho => h (realizes_of_occupies P J hJ ho)

end
end ElevenSquare.Pending.T03.Wand125

#print axioms ElevenSquare.Pending.T03.Wand125.excludes_occupancy
