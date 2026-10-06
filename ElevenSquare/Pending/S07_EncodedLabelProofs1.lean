import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup16 : recordedOverlayLabels[16]! = recordedOverlayLabelsChunk0[16]! := by
  exact label_lookup_chunk0 16 (by decide) (by decide)
theorem label_good16 : LabelGood 16 := by
  unfold LabelGood
  rw [label_lookup16]
  decide
theorem label_lookup17 : recordedOverlayLabels[17]! = recordedOverlayLabelsChunk0[17]! := by
  exact label_lookup_chunk0 17 (by decide) (by decide)
theorem label_good17 : LabelGood 17 := by
  unfold LabelGood
  rw [label_lookup17]
  decide
theorem label_lookup18 : recordedOverlayLabels[18]! = recordedOverlayLabelsChunk0[18]! := by
  exact label_lookup_chunk0 18 (by decide) (by decide)
theorem label_good18 : LabelGood 18 := by
  unfold LabelGood
  rw [label_lookup18]
  decide
theorem label_lookup19 : recordedOverlayLabels[19]! = recordedOverlayLabelsChunk0[19]! := by
  exact label_lookup_chunk0 19 (by decide) (by decide)
theorem label_good19 : LabelGood 19 := by
  unfold LabelGood
  rw [label_lookup19]
  decide
theorem label_lookup20 : recordedOverlayLabels[20]! = recordedOverlayLabelsChunk0[20]! := by
  exact label_lookup_chunk0 20 (by decide) (by decide)
theorem label_good20 : LabelGood 20 := by
  unfold LabelGood
  rw [label_lookup20]
  decide
theorem label_lookup21 : recordedOverlayLabels[21]! = recordedOverlayLabelsChunk0[21]! := by
  exact label_lookup_chunk0 21 (by decide) (by decide)
theorem label_good21 : LabelGood 21 := by
  unfold LabelGood
  rw [label_lookup21]
  decide
theorem label_lookup22 : recordedOverlayLabels[22]! = recordedOverlayLabelsChunk0[22]! := by
  exact label_lookup_chunk0 22 (by decide) (by decide)
theorem label_good22 : LabelGood 22 := by
  unfold LabelGood
  rw [label_lookup22]
  decide
theorem label_lookup23 : recordedOverlayLabels[23]! = recordedOverlayLabelsChunk0[23]! := by
  exact label_lookup_chunk0 23 (by decide) (by decide)
theorem label_good23 : LabelGood 23 := by
  unfold LabelGood
  rw [label_lookup23]
  decide
theorem label_lookup24 : recordedOverlayLabels[24]! = recordedOverlayLabelsChunk0[24]! := by
  exact label_lookup_chunk0 24 (by decide) (by decide)
theorem label_good24 : LabelGood 24 := by
  unfold LabelGood
  rw [label_lookup24]
  decide
theorem label_lookup25 : recordedOverlayLabels[25]! = recordedOverlayLabelsChunk0[25]! := by
  exact label_lookup_chunk0 25 (by decide) (by decide)
theorem label_good25 : LabelGood 25 := by
  unfold LabelGood
  rw [label_lookup25]
  decide
theorem label_lookup26 : recordedOverlayLabels[26]! = recordedOverlayLabelsChunk0[26]! := by
  exact label_lookup_chunk0 26 (by decide) (by decide)
theorem label_good26 : LabelGood 26 := by
  unfold LabelGood
  rw [label_lookup26]
  decide
theorem label_lookup27 : recordedOverlayLabels[27]! = recordedOverlayLabelsChunk0[27]! := by
  exact label_lookup_chunk0 27 (by decide) (by decide)
theorem label_good27 : LabelGood 27 := by
  unfold LabelGood
  rw [label_lookup27]
  decide
theorem label_lookup28 : recordedOverlayLabels[28]! = recordedOverlayLabelsChunk0[28]! := by
  exact label_lookup_chunk0 28 (by decide) (by decide)
theorem label_good28 : LabelGood 28 := by
  unfold LabelGood
  rw [label_lookup28]
  decide
theorem label_lookup29 : recordedOverlayLabels[29]! = recordedOverlayLabelsChunk0[29]! := by
  exact label_lookup_chunk0 29 (by decide) (by decide)
theorem label_good29 : LabelGood 29 := by
  unfold LabelGood
  rw [label_lookup29]
  decide
theorem label_lookup30 : recordedOverlayLabels[30]! = recordedOverlayLabelsChunk0[30]! := by
  exact label_lookup_chunk0 30 (by decide) (by decide)
theorem label_good30 : LabelGood 30 := by
  unfold LabelGood
  rw [label_lookup30]
  decide
theorem label_lookup31 : recordedOverlayLabels[31]! = recordedOverlayLabelsChunk0[31]! := by
  exact label_lookup_chunk0 31 (by decide) (by decide)
theorem label_good31 : LabelGood 31 := by
  unfold LabelGood
  rw [label_lookup31]
  decide
theorem labels_range1 : AllRange LabelGood 16 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good16, (List.forall_mem_cons.mpr ⟨label_good17, (List.forall_mem_cons.mpr ⟨label_good18, (List.forall_mem_cons.mpr ⟨label_good19, (List.forall_mem_cons.mpr ⟨label_good20, (List.forall_mem_cons.mpr ⟨label_good21, (List.forall_mem_cons.mpr ⟨label_good22, (List.forall_mem_cons.mpr ⟨label_good23, (List.forall_mem_cons.mpr ⟨label_good24, (List.forall_mem_cons.mpr ⟨label_good25, (List.forall_mem_cons.mpr ⟨label_good26, (List.forall_mem_cons.mpr ⟨label_good27, (List.forall_mem_cons.mpr ⟨label_good28, (List.forall_mem_cons.mpr ⟨label_good29, (List.forall_mem_cons.mpr ⟨label_good30, (List.forall_mem_cons.mpr ⟨label_good31, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range1
