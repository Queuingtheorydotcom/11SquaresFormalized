import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup0 : recordedOverlayLabels[0]! = recordedOverlayLabelsChunk0[0]! := by
  exact label_lookup_chunk0 0 (by decide) (by decide)
theorem label_good0 : LabelGood 0 := by
  unfold LabelGood
  rw [label_lookup0]
  decide
theorem label_lookup1 : recordedOverlayLabels[1]! = recordedOverlayLabelsChunk0[1]! := by
  exact label_lookup_chunk0 1 (by decide) (by decide)
theorem label_good1 : LabelGood 1 := by
  unfold LabelGood
  rw [label_lookup1]
  decide
theorem label_lookup2 : recordedOverlayLabels[2]! = recordedOverlayLabelsChunk0[2]! := by
  exact label_lookup_chunk0 2 (by decide) (by decide)
theorem label_good2 : LabelGood 2 := by
  unfold LabelGood
  rw [label_lookup2]
  decide
theorem label_lookup3 : recordedOverlayLabels[3]! = recordedOverlayLabelsChunk0[3]! := by
  exact label_lookup_chunk0 3 (by decide) (by decide)
theorem label_good3 : LabelGood 3 := by
  unfold LabelGood
  rw [label_lookup3]
  decide
theorem label_lookup4 : recordedOverlayLabels[4]! = recordedOverlayLabelsChunk0[4]! := by
  exact label_lookup_chunk0 4 (by decide) (by decide)
theorem label_good4 : LabelGood 4 := by
  unfold LabelGood
  rw [label_lookup4]
  decide
theorem label_lookup5 : recordedOverlayLabels[5]! = recordedOverlayLabelsChunk0[5]! := by
  exact label_lookup_chunk0 5 (by decide) (by decide)
theorem label_good5 : LabelGood 5 := by
  unfold LabelGood
  rw [label_lookup5]
  decide
theorem label_lookup6 : recordedOverlayLabels[6]! = recordedOverlayLabelsChunk0[6]! := by
  exact label_lookup_chunk0 6 (by decide) (by decide)
theorem label_good6 : LabelGood 6 := by
  unfold LabelGood
  rw [label_lookup6]
  decide
theorem label_lookup7 : recordedOverlayLabels[7]! = recordedOverlayLabelsChunk0[7]! := by
  exact label_lookup_chunk0 7 (by decide) (by decide)
theorem label_good7 : LabelGood 7 := by
  unfold LabelGood
  rw [label_lookup7]
  decide
theorem label_lookup8 : recordedOverlayLabels[8]! = recordedOverlayLabelsChunk0[8]! := by
  exact label_lookup_chunk0 8 (by decide) (by decide)
theorem label_good8 : LabelGood 8 := by
  unfold LabelGood
  rw [label_lookup8]
  decide
theorem label_lookup9 : recordedOverlayLabels[9]! = recordedOverlayLabelsChunk0[9]! := by
  exact label_lookup_chunk0 9 (by decide) (by decide)
theorem label_good9 : LabelGood 9 := by
  unfold LabelGood
  rw [label_lookup9]
  decide
theorem label_lookup10 : recordedOverlayLabels[10]! = recordedOverlayLabelsChunk0[10]! := by
  exact label_lookup_chunk0 10 (by decide) (by decide)
theorem label_good10 : LabelGood 10 := by
  unfold LabelGood
  rw [label_lookup10]
  decide
theorem label_lookup11 : recordedOverlayLabels[11]! = recordedOverlayLabelsChunk0[11]! := by
  exact label_lookup_chunk0 11 (by decide) (by decide)
theorem label_good11 : LabelGood 11 := by
  unfold LabelGood
  rw [label_lookup11]
  decide
theorem label_lookup12 : recordedOverlayLabels[12]! = recordedOverlayLabelsChunk0[12]! := by
  exact label_lookup_chunk0 12 (by decide) (by decide)
theorem label_good12 : LabelGood 12 := by
  unfold LabelGood
  rw [label_lookup12]
  decide
theorem label_lookup13 : recordedOverlayLabels[13]! = recordedOverlayLabelsChunk0[13]! := by
  exact label_lookup_chunk0 13 (by decide) (by decide)
theorem label_good13 : LabelGood 13 := by
  unfold LabelGood
  rw [label_lookup13]
  decide
theorem label_lookup14 : recordedOverlayLabels[14]! = recordedOverlayLabelsChunk0[14]! := by
  exact label_lookup_chunk0 14 (by decide) (by decide)
theorem label_good14 : LabelGood 14 := by
  unfold LabelGood
  rw [label_lookup14]
  decide
theorem label_lookup15 : recordedOverlayLabels[15]! = recordedOverlayLabelsChunk0[15]! := by
  exact label_lookup_chunk0 15 (by decide) (by decide)
theorem label_good15 : LabelGood 15 := by
  unfold LabelGood
  rw [label_lookup15]
  decide
theorem labels_range0 : AllRange LabelGood 0 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good0, (List.forall_mem_cons.mpr ⟨label_good1, (List.forall_mem_cons.mpr ⟨label_good2, (List.forall_mem_cons.mpr ⟨label_good3, (List.forall_mem_cons.mpr ⟨label_good4, (List.forall_mem_cons.mpr ⟨label_good5, (List.forall_mem_cons.mpr ⟨label_good6, (List.forall_mem_cons.mpr ⟨label_good7, (List.forall_mem_cons.mpr ⟨label_good8, (List.forall_mem_cons.mpr ⟨label_good9, (List.forall_mem_cons.mpr ⟨label_good10, (List.forall_mem_cons.mpr ⟨label_good11, (List.forall_mem_cons.mpr ⟨label_good12, (List.forall_mem_cons.mpr ⟨label_good13, (List.forall_mem_cons.mpr ⟨label_good14, (List.forall_mem_cons.mpr ⟨label_good15, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range0
