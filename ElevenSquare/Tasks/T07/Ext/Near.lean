import ElevenSquare.Tasks.T07.Ext.Check
import ElevenSquare.Tasks.T07.NearStateBridge

/-! A checker for `NearFiniteRowEnclosure`.

Each row of the final trace state names a row of the near packet whose angular
interval contains its own, and carries Farkas certificates that its centre
polygon lies in the four half-planes of the owner's field box. -/
namespace ElevenSquare.Tasks.T07.Ext
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07
noncomputable section

/-- The certificate of one row: the index of the near row and the multipliers
for the four box half-planes. -/
structure NRow where
  k : ℕ
  mus : List (List ℚ)

def NRow.check (i : Owner) (r : PoseRow) (c : NRow) : Bool :=
  match (nearRows i)[c.k]? with
  | some nr => decide (nr.lo ≤ r.lo) && decide (r.hi ≤ nr.hi) &&
      subsetB r.centers (nearBoxPlanes (nearFieldBox i)) c.mus
  | none => false

def nearRowsB (i : Owner) (rows : List PoseRow) (cs : List NRow) : Bool :=
  (rows.length == cs.length) && ((rows.zip cs).all fun rc => rc.2.check i rc.1)

theorem nearRowsB_sound {s : PoseState} {cs : Owner → List NRow}
    (h : ∀ i, nearRowsB i (s.rows i) (cs i) = true) : NearFiniteRowEnclosure s := by
  intro i r hr
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
    refine ⟨nr, List.mem_of_getElem? hnr, by exact_mod_cast hlo, by exact_mod_cast hhi, ?_⟩
    intro p hp
    exact (nearBoxPlanes_iff (nearFieldBox i) p).mp (subsetB_sound hsub hp)
  · exact absurd hc (by simp)

end
end ElevenSquare.Tasks.T07.Ext
