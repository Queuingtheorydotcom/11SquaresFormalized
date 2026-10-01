import ElevenSquare.Tasks.T07.Ext.Check
import ElevenSquare.Tasks.T07.NearFinalPacket

/-! A checker for the inclusion of a final trace state in the near packet.

`NearStateBridge` defines the near outer state from the frozen near rows and
their rational field boxes.  Its import chain does not build on the current
toolchain, so the definitions used here are verbatim copies over the same data
(`nearRows`, `nearFieldBox`); `Case438Global` identifies them with the
originals by `rfl`.

Each row of the final trace state names a row of the near packet whose angular
interval contains its own, and carries Farkas certificates that its centre
polygon lies in the four half-planes of the owner's field box. -/
namespace ElevenSquare.Tasks.T07.Ext
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07
noncomputable section

/-- Copy of `nearScaleQ`. -/
def extNearScaleQ : ℚ :=
  Rat.divInt 382000000000000000000 387708359002281417731

/-- Copy of `nearBoxPlanes`. -/
def extNearBoxPlanes (b : NearRatRect) : Polygon :=
  [{a := -extNearScaleQ, b := 0, c := -b.lx},
   {a := extNearScaleQ, b := 0, c := b.hx},
   {a := 0, b := -extNearScaleQ, c := -b.ly},
   {a := 0, b := extNearScaleQ, c := b.hy}]

/-- Copy of `nearOuterRow`. -/
def extNearOuterRow (i : Owner) (r : NearPoseRow) : PoseRow :=
  { lo := r.lo, hi := r.hi, centers := extNearBoxPlanes (nearFieldBox i) }

/-- Copy of `nearOuterState`. -/
def extNearOuterState : PoseState where
  rows i := (nearRows i).map (extNearOuterRow i)
  owned _ := []

/-- The certificate of one row: the index of the near row and the multipliers
for the four box half-planes. -/
structure NRow where
  k : ℕ
  mus : List (List ℚ)

def NRow.check (i : Owner) (r : PoseRow) (c : NRow) : Bool :=
  match (nearRows i)[c.k]? with
  | some nr => decide (nr.lo ≤ r.lo) && decide (r.hi ≤ nr.hi) &&
      subsetB r.centers (extNearBoxPlanes (nearFieldBox i)) c.mus
  | none => false

def nearRowsB (i : Owner) (rows : List PoseRow) (cs : List NRow) : Bool :=
  (rows.length == cs.length) && ((rows.zip cs).all fun rc => rc.2.check i rc.1)

/-- Checked rows are contained in the rows of the near outer state (the copy of
`NearRowsSubsumed`). -/
theorem nearRowsB_sound {s : PoseState} {cs : Owner → List NRow}
    (h : ∀ i, nearRowsB i (s.rows i) (cs i) = true) :
    ∀ i : Owner, ∀ q : UnitSquare, RowsContain (s.rows i) q → RowsContain (extNearOuterState.rows i) q := by
  intro i q hq
  obtain ⟨r, hr, hcenter, t, ht0, ht1, htlo, hthi, haxis⟩ := hq
  have hi := h i
  simp only [nearRowsB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hi
  obtain ⟨hlen, hall⟩ := hi
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hr
  have hn' : n < (cs i).length := hlen ▸ hn
  have hmem : ((s.rows i)[n], (cs i)[n]) ∈ (s.rows i).zip (cs i) := by
    rw [List.mem_iff_getElem]; exact ⟨n, by simp [hn, hn'], by simp⟩
  have hc := hall _ hmem
  simp only [NRow.check] at hc
  split at hc
  · rename_i nr hnr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hlo, hhi⟩, hsub⟩ := hc
    refine ⟨extNearOuterRow i nr, List.mem_map.mpr ⟨nr, List.mem_of_getElem? hnr, rfl⟩, ?_⟩
    exact ⟨subsetB_sound hsub hcenter, t, ht0, ht1,
      le_trans (by exact_mod_cast hlo) htlo, le_trans hthi (by exact_mod_cast hhi), haxis⟩
  · exact absurd hc (by simp)

/-- The copy of `stateHolds_nearOuterState_of_subsumed`. -/
theorem stateHolds_extNearOuterState {S : ℝ} (Q : Packing 11 S) (s : PoseState) (hs : StateHolds Q s)
    (hsub : ∀ i : Owner, ∀ q : UnitSquare, RowsContain (s.rows i) q →
      RowsContain (extNearOuterState.rows i) q) :
    StateHolds Q extNearOuterState := by
  constructor
  · intro i
    exact hsub i (Q.squares i) (hs.1 i)
  · intro i
    simp [extNearOuterState, rationalHull]

end
end ElevenSquare.Tasks.T07.Ext
