import ElevenSquare.Pending.S05_OwnedHull
import ElevenSquare.Cover

namespace ElevenSquare.Pending.T03
noncomputable section

/-- A shared, universally valid initialization library. Its fields are proofs,
so instantiating it requires checking every template and every owned group. -/
structure InitializationLibrary where
  rows : Fin 16 → List PoseRow
  owned : Fin 16 → List QPoint
  rows_valid : ∀ (i : Fin 16) (q : UnitSquare) (t : ℝ),
    (∀ p, ClosedSquare q p → InContainer coverCap p) →
    ClosedCell i (normalizeCenter q.center) → q.axis = chartAxis t →
    0 ≤ t → t ≤ 1 → RowsContain (rows i) q
  owned_valid : ∀ (i : Fin 16) (q : UnitSquare) (t : ℝ),
    (∀ p, ClosedSquare q p → InContainer coverCap p) →
    ClosedCell i (normalizeCenter q.center) → q.axis = chartAxis t →
    0 ≤ t → t ≤ 1 → rationalHull (owned i) ⊆ {p | OpenSquare q p}

def InitializationLibrary.state (lib : InitializationLibrary) (cells : Owner → Fin 16) : PoseState :=
  ⟨fun i => lib.rows (cells i), fun i => lib.owned (cells i)⟩

theorem occupancy_relabel (P : Packing 11 coverCap) (m : Finset (Fin 16))
    (cells : Owner → Fin 16) (hcells : Function.Injective cells)
    (himage : Finset.univ.image cells = m) (hocc : Occupies P m) :
    ∃ perm : Equiv.Perm Owner,
      ∀ i, ClosedCell (cells i) (normalizeCenter (P.squares (perm i)).center) := by
  classical
  obtain ⟨a,ha,ham,hcell⟩ := hocc
  have hex : ∀ i, ∃ j, a j = cells i := by
    intro i
    have hmem : cells i ∈ Finset.univ.image a := by
      rw [ham, ← himage]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hmem
    exact ⟨j,hj⟩
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hcells
    rw [← hf i, ← hf j, hij]
  let perm : Equiv.Perm Owner := Equiv.ofBijective f
    ⟨hfinj,Finite.surjective_of_injective hfinj⟩
  refine ⟨perm,?_⟩
  intro i
  have hh := hcell (f i)
  simpa [perm,hf i] using hh

theorem InitializationLibrary.initialize (lib : InitializationLibrary)
    (cells : Owner → Fin 16) (hcells : Function.Injective cells)
    (m : Finset (Fin 16)) (himage : Finset.univ.image cells = m)
    (P : Packing 11 coverCap) (hchart : IsCharted P) (hocc : Occupies P m) :
    ∃ perm : Equiv.Perm Owner, StateHolds (relabelPacking P perm) (lib.state cells) := by
  obtain ⟨perm,hcell⟩ := occupancy_relabel P m cells hcells himage hocc
  refine ⟨perm,?_,?_⟩
  · intro i
    obtain ⟨t,ht0,ht1,hq⟩ := hchart (perm i)
    exact lib.rows_valid (cells i) (P.squares (perm i)) t
      (P.contained (perm i)) (hcell i) hq ht0 ht1
  · intro i
    obtain ⟨t,ht0,ht1,hq⟩ := hchart (perm i)
    exact lib.owned_valid (cells i) (P.squares (perm i)) t
      (P.contained (perm i)) (hcell i) hq ht0 ht1

end
end ElevenSquare.Pending.T03
