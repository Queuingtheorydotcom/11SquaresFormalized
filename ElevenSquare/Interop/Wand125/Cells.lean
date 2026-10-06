import ElevenSquare.Interop.Wand125.Geometry
import ElevenSquare.Cover
import Sqpack.S11Opt.Cells

namespace ElevenSquare.Interop.Wand125
noncomputable section
open SquarePacking.S11Opt

theorem cap_eq : coverCap = Ux := by norm_num [coverCap, Ux]

theorem site_eq (i : Fin 16) :
    PU i = (1 / 2 + (coverCap - 1) * (coverSite i).1,
            1 / 2 + (coverCap - 1) * (coverSite i).2) := by
  fin_cases i <;> norm_num [PU, coverCap, coverSite]

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
end ElevenSquare.Interop.Wand125

#print axioms ElevenSquare.Interop.Wand125.excludes_occupancy
