import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup48 : recordedOverlayLabels[48]! = recordedOverlayLabelsChunk1[16]! := by
  exact label_lookup_chunk1 48 (by decide) (by decide)
theorem label_good48 : LabelGood 48 := by
  unfold LabelGood
  rw [label_lookup48]
  decide
theorem label_lookup49 : recordedOverlayLabels[49]! = recordedOverlayLabelsChunk1[17]! := by
  exact label_lookup_chunk1 49 (by decide) (by decide)
theorem label_good49 : LabelGood 49 := by
  unfold LabelGood
  rw [label_lookup49]
  decide
theorem label_lookup50 : recordedOverlayLabels[50]! = recordedOverlayLabelsChunk1[18]! := by
  exact label_lookup_chunk1 50 (by decide) (by decide)
theorem label_good50 : LabelGood 50 := by
  unfold LabelGood
  rw [label_lookup50]
  decide
theorem label_lookup51 : recordedOverlayLabels[51]! = recordedOverlayLabelsChunk1[19]! := by
  exact label_lookup_chunk1 51 (by decide) (by decide)
theorem label_good51 : LabelGood 51 := by
  unfold LabelGood
  rw [label_lookup51]
  decide
theorem label_lookup52 : recordedOverlayLabels[52]! = recordedOverlayLabelsChunk1[20]! := by
  exact label_lookup_chunk1 52 (by decide) (by decide)
theorem label_good52 : LabelGood 52 := by
  unfold LabelGood
  rw [label_lookup52]
  decide
theorem label_lookup53 : recordedOverlayLabels[53]! = recordedOverlayLabelsChunk1[21]! := by
  exact label_lookup_chunk1 53 (by decide) (by decide)
theorem label_good53 : LabelGood 53 := by
  unfold LabelGood
  rw [label_lookup53]
  decide
theorem label_lookup54 : recordedOverlayLabels[54]! = recordedOverlayLabelsChunk1[22]! := by
  exact label_lookup_chunk1 54 (by decide) (by decide)
theorem label_good54 : LabelGood 54 := by
  unfold LabelGood
  rw [label_lookup54]
  decide
theorem label_lookup55 : recordedOverlayLabels[55]! = recordedOverlayLabelsChunk1[23]! := by
  exact label_lookup_chunk1 55 (by decide) (by decide)
theorem label_good55 : LabelGood 55 := by
  unfold LabelGood
  rw [label_lookup55]
  decide
theorem label_lookup56 : recordedOverlayLabels[56]! = recordedOverlayLabelsChunk1[24]! := by
  exact label_lookup_chunk1 56 (by decide) (by decide)
theorem label_good56 : LabelGood 56 := by
  unfold LabelGood
  rw [label_lookup56]
  decide
theorem label_lookup57 : recordedOverlayLabels[57]! = recordedOverlayLabelsChunk1[25]! := by
  exact label_lookup_chunk1 57 (by decide) (by decide)
theorem label_good57 : LabelGood 57 := by
  unfold LabelGood
  rw [label_lookup57]
  decide
theorem label_lookup58 : recordedOverlayLabels[58]! = recordedOverlayLabelsChunk1[26]! := by
  exact label_lookup_chunk1 58 (by decide) (by decide)
theorem label_good58 : LabelGood 58 := by
  unfold LabelGood
  rw [label_lookup58]
  decide
theorem label_lookup59 : recordedOverlayLabels[59]! = recordedOverlayLabelsChunk1[27]! := by
  exact label_lookup_chunk1 59 (by decide) (by decide)
theorem label_good59 : LabelGood 59 := by
  unfold LabelGood
  rw [label_lookup59]
  decide
theorem label_lookup60 : recordedOverlayLabels[60]! = recordedOverlayLabelsChunk1[28]! := by
  exact label_lookup_chunk1 60 (by decide) (by decide)
theorem label_good60 : LabelGood 60 := by
  unfold LabelGood
  rw [label_lookup60]
  decide
theorem label_lookup61 : recordedOverlayLabels[61]! = recordedOverlayLabelsChunk1[29]! := by
  exact label_lookup_chunk1 61 (by decide) (by decide)
theorem label_good61 : LabelGood 61 := by
  unfold LabelGood
  rw [label_lookup61]
  decide
theorem label_lookup62 : recordedOverlayLabels[62]! = recordedOverlayLabelsChunk1[30]! := by
  exact label_lookup_chunk1 62 (by decide) (by decide)
theorem label_good62 : LabelGood 62 := by
  unfold LabelGood
  rw [label_lookup62]
  decide
theorem label_lookup63 : recordedOverlayLabels[63]! = recordedOverlayLabelsChunk1[31]! := by
  exact label_lookup_chunk1 63 (by decide) (by decide)
theorem label_good63 : LabelGood 63 := by
  unfold LabelGood
  rw [label_lookup63]
  decide
theorem labels_range3 : AllRange LabelGood 48 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good48, (List.forall_mem_cons.mpr ⟨label_good49, (List.forall_mem_cons.mpr ⟨label_good50, (List.forall_mem_cons.mpr ⟨label_good51, (List.forall_mem_cons.mpr ⟨label_good52, (List.forall_mem_cons.mpr ⟨label_good53, (List.forall_mem_cons.mpr ⟨label_good54, (List.forall_mem_cons.mpr ⟨label_good55, (List.forall_mem_cons.mpr ⟨label_good56, (List.forall_mem_cons.mpr ⟨label_good57, (List.forall_mem_cons.mpr ⟨label_good58, (List.forall_mem_cons.mpr ⟨label_good59, (List.forall_mem_cons.mpr ⟨label_good60, (List.forall_mem_cons.mpr ⟨label_good61, (List.forall_mem_cons.mpr ⟨label_good62, (List.forall_mem_cons.mpr ⟨label_good63, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range3
