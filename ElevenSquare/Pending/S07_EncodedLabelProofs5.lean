import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup80 : recordedOverlayLabels[80]! = recordedOverlayLabelsChunk2[16]! := by
  exact label_lookup_chunk2 80 (by decide) (by decide)
theorem label_good80 : LabelGood 80 := by
  unfold LabelGood
  rw [label_lookup80]
  decide
theorem label_lookup81 : recordedOverlayLabels[81]! = recordedOverlayLabelsChunk2[17]! := by
  exact label_lookup_chunk2 81 (by decide) (by decide)
theorem label_good81 : LabelGood 81 := by
  unfold LabelGood
  rw [label_lookup81]
  decide
theorem label_lookup82 : recordedOverlayLabels[82]! = recordedOverlayLabelsChunk2[18]! := by
  exact label_lookup_chunk2 82 (by decide) (by decide)
theorem label_good82 : LabelGood 82 := by
  unfold LabelGood
  rw [label_lookup82]
  decide
theorem label_lookup83 : recordedOverlayLabels[83]! = recordedOverlayLabelsChunk2[19]! := by
  exact label_lookup_chunk2 83 (by decide) (by decide)
theorem label_good83 : LabelGood 83 := by
  unfold LabelGood
  rw [label_lookup83]
  decide
theorem label_lookup84 : recordedOverlayLabels[84]! = recordedOverlayLabelsChunk2[20]! := by
  exact label_lookup_chunk2 84 (by decide) (by decide)
theorem label_good84 : LabelGood 84 := by
  unfold LabelGood
  rw [label_lookup84]
  decide
theorem label_lookup85 : recordedOverlayLabels[85]! = recordedOverlayLabelsChunk2[21]! := by
  exact label_lookup_chunk2 85 (by decide) (by decide)
theorem label_good85 : LabelGood 85 := by
  unfold LabelGood
  rw [label_lookup85]
  decide
theorem label_lookup86 : recordedOverlayLabels[86]! = recordedOverlayLabelsChunk2[22]! := by
  exact label_lookup_chunk2 86 (by decide) (by decide)
theorem label_good86 : LabelGood 86 := by
  unfold LabelGood
  rw [label_lookup86]
  decide
theorem label_lookup87 : recordedOverlayLabels[87]! = recordedOverlayLabelsChunk2[23]! := by
  exact label_lookup_chunk2 87 (by decide) (by decide)
theorem label_good87 : LabelGood 87 := by
  unfold LabelGood
  rw [label_lookup87]
  decide
theorem label_lookup88 : recordedOverlayLabels[88]! = recordedOverlayLabelsChunk2[24]! := by
  exact label_lookup_chunk2 88 (by decide) (by decide)
theorem label_good88 : LabelGood 88 := by
  unfold LabelGood
  rw [label_lookup88]
  decide
theorem label_lookup89 : recordedOverlayLabels[89]! = recordedOverlayLabelsChunk2[25]! := by
  exact label_lookup_chunk2 89 (by decide) (by decide)
theorem label_good89 : LabelGood 89 := by
  unfold LabelGood
  rw [label_lookup89]
  decide
theorem label_lookup90 : recordedOverlayLabels[90]! = recordedOverlayLabelsChunk2[26]! := by
  exact label_lookup_chunk2 90 (by decide) (by decide)
theorem label_good90 : LabelGood 90 := by
  unfold LabelGood
  rw [label_lookup90]
  decide
theorem label_lookup91 : recordedOverlayLabels[91]! = recordedOverlayLabelsChunk2[27]! := by
  exact label_lookup_chunk2 91 (by decide) (by decide)
theorem label_good91 : LabelGood 91 := by
  unfold LabelGood
  rw [label_lookup91]
  decide
theorem label_lookup92 : recordedOverlayLabels[92]! = recordedOverlayLabelsChunk2[28]! := by
  exact label_lookup_chunk2 92 (by decide) (by decide)
theorem label_good92 : LabelGood 92 := by
  unfold LabelGood
  rw [label_lookup92]
  decide
theorem label_lookup93 : recordedOverlayLabels[93]! = recordedOverlayLabelsChunk2[29]! := by
  exact label_lookup_chunk2 93 (by decide) (by decide)
theorem label_good93 : LabelGood 93 := by
  unfold LabelGood
  rw [label_lookup93]
  decide
theorem label_lookup94 : recordedOverlayLabels[94]! = recordedOverlayLabelsChunk2[30]! := by
  exact label_lookup_chunk2 94 (by decide) (by decide)
theorem label_good94 : LabelGood 94 := by
  unfold LabelGood
  rw [label_lookup94]
  decide
theorem label_lookup95 : recordedOverlayLabels[95]! = recordedOverlayLabelsChunk2[31]! := by
  exact label_lookup_chunk2 95 (by decide) (by decide)
theorem label_good95 : LabelGood 95 := by
  unfold LabelGood
  rw [label_lookup95]
  decide
theorem labels_range5 : AllRange LabelGood 80 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good80, (List.forall_mem_cons.mpr ⟨label_good81, (List.forall_mem_cons.mpr ⟨label_good82, (List.forall_mem_cons.mpr ⟨label_good83, (List.forall_mem_cons.mpr ⟨label_good84, (List.forall_mem_cons.mpr ⟨label_good85, (List.forall_mem_cons.mpr ⟨label_good86, (List.forall_mem_cons.mpr ⟨label_good87, (List.forall_mem_cons.mpr ⟨label_good88, (List.forall_mem_cons.mpr ⟨label_good89, (List.forall_mem_cons.mpr ⟨label_good90, (List.forall_mem_cons.mpr ⟨label_good91, (List.forall_mem_cons.mpr ⟨label_good92, (List.forall_mem_cons.mpr ⟨label_good93, (List.forall_mem_cons.mpr ⟨label_good94, (List.forall_mem_cons.mpr ⟨label_good95, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range5
