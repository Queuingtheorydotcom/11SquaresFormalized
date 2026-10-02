import ElevenSquare.Pending.S07_EncodedNeighborProofs0
import ElevenSquare.Pending.S07_EncodedNeighborProofs1
import ElevenSquare.Pending.S07_EncodedNeighborProofs2
import ElevenSquare.Pending.S07_EncodedNeighborProofs3
import ElevenSquare.Pending.S07_EncodedNeighborProofs4
import ElevenSquare.Pending.S07_EncodedNeighborProofs5
import ElevenSquare.Pending.S07_EncodedNeighborProofs6
import ElevenSquare.Pending.S07_EncodedNeighborProofs7
import ElevenSquare.Pending.S07_EncodedNeighborProofs8
import ElevenSquare.Pending.S07_EncodedNeighborProofs9
import ElevenSquare.Pending.S07_EncodedNeighborProofs10
import ElevenSquare.Pending.S07_EncodedNeighborProofs11
import ElevenSquare.Pending.S07_EncodedNeighborProofs12
import ElevenSquare.Pending.S07_EncodedNeighborProofs13
import ElevenSquare.Pending.S07_EncodedLabelProofs0
import ElevenSquare.Pending.S07_EncodedLabelProofs1
import ElevenSquare.Pending.S07_EncodedLabelProofs2
import ElevenSquare.Pending.S07_EncodedLabelProofs3
import ElevenSquare.Pending.S07_EncodedLabelProofs4
import ElevenSquare.Pending.S07_EncodedLabelProofs5
import ElevenSquare.Pending.S07_EncodedLabelProofs6
import ElevenSquare.Pending.S07_EncodedLabelProofs7
import ElevenSquare.Pending.S07_EncodedLabelProofs8
import ElevenSquare.Pending.S07_EncodedLabelProofs9
import ElevenSquare.Pending.S07_EncodedLabelProofs10
import ElevenSquare.Pending.S07_EncodedLabelProofs11
import ElevenSquare.Pending.S07_EncodedLabelProofs12
import ElevenSquare.Pending.S07_EncodedLabelProofs13
namespace ElevenSquare.Pending.EncodedSearch
theorem all_neighbors : AllRange NeighborGood 0 220 :=
  (((((((((((((neighbors_range0.append neighbors_range1).append neighbors_range2).append neighbors_range3).append neighbors_range4).append neighbors_range5).append neighbors_range6).append neighbors_range7).append neighbors_range8).append neighbors_range9).append neighbors_range10).append neighbors_range11).append neighbors_range12).append neighbors_range13)
theorem all_labels : AllRange LabelGood 0 220 :=
  (((((((((((((labels_range0.append labels_range1).append labels_range2).append labels_range3).append labels_range4).append labels_range5).append labels_range6).append labels_range7).append labels_range8).append labels_range9).append labels_range10).append labels_range11).append labels_range12).append labels_range13)
set_option maxRecDepth 2048 in
theorem labels_correct (r : Fin 220) (g : Fin 4) :
    label r.val g.val = (overlayLabels r g).val :=
  all_labels r.val (Nat.zero_le _) r.isLt g

theorem neighbors_sound (r s : Fin 220) (h : s.val ∈ neighbors r.val) : pairBanned r s :=
  all_neighbors r.val (Nat.zero_le _) r.isLt s.val h

theorem compatible_of_original (r s : Fin 220)
    (hlabels : ∀ g : Fin 4, overlayLabels r g ≠ overlayLabels s g)
    (hban : ¬ pairBanned r s) : compatible r.val s.val = true := by
  have hd (g : Fin 4) : label r.val g.val ≠ label s.val g.val := by
    rw [labels_correct, labels_correct]
    intro he
    exact hlabels g (Fin.ext he)
  have hn : s.val ∉ neighbors r.val := fun h => hban (neighbors_sound r s h)
  have h0 : label r.val 0 ≠ label s.val 0 := hd 0
  have h1 : label r.val 1 ≠ label s.val 1 := hd 1
  have h2 : label r.val 2 ≠ label s.val 2 := hd 2
  have h3 : label r.val 3 ≠ label s.val 3 := hd 3
  simp only [compatible, List.contains_eq_mem, hn, decide_false,
    Bool.not_false, Bool.and_true]
  exact decide_eq_true_iff.mpr ⟨h0, h1, h2, h3⟩

end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_correct
#print axioms ElevenSquare.Pending.EncodedSearch.neighbors_sound
#print axioms ElevenSquare.Pending.EncodedSearch.compatible_of_original
