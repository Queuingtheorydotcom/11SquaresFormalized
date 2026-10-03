import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup32 : recordedOverlayLabels[32]! = recordedOverlayLabelsChunk1[0]! := by
  exact label_lookup_chunk1 32 (by decide) (by decide)
theorem label_good32 : LabelGood 32 := by
  unfold LabelGood
  rw [label_lookup32]
  decide
theorem label_lookup33 : recordedOverlayLabels[33]! = recordedOverlayLabelsChunk1[1]! := by
  exact label_lookup_chunk1 33 (by decide) (by decide)
theorem label_good33 : LabelGood 33 := by
  unfold LabelGood
  rw [label_lookup33]
  decide
theorem label_lookup34 : recordedOverlayLabels[34]! = recordedOverlayLabelsChunk1[2]! := by
  exact label_lookup_chunk1 34 (by decide) (by decide)
theorem label_good34 : LabelGood 34 := by
  unfold LabelGood
  rw [label_lookup34]
  decide
theorem label_lookup35 : recordedOverlayLabels[35]! = recordedOverlayLabelsChunk1[3]! := by
  exact label_lookup_chunk1 35 (by decide) (by decide)
theorem label_good35 : LabelGood 35 := by
  unfold LabelGood
  rw [label_lookup35]
  decide
theorem label_lookup36 : recordedOverlayLabels[36]! = recordedOverlayLabelsChunk1[4]! := by
  exact label_lookup_chunk1 36 (by decide) (by decide)
theorem label_good36 : LabelGood 36 := by
  unfold LabelGood
  rw [label_lookup36]
  decide
theorem label_lookup37 : recordedOverlayLabels[37]! = recordedOverlayLabelsChunk1[5]! := by
  exact label_lookup_chunk1 37 (by decide) (by decide)
theorem label_good37 : LabelGood 37 := by
  unfold LabelGood
  rw [label_lookup37]
  decide
theorem label_lookup38 : recordedOverlayLabels[38]! = recordedOverlayLabelsChunk1[6]! := by
  exact label_lookup_chunk1 38 (by decide) (by decide)
theorem label_good38 : LabelGood 38 := by
  unfold LabelGood
  rw [label_lookup38]
  decide
theorem label_lookup39 : recordedOverlayLabels[39]! = recordedOverlayLabelsChunk1[7]! := by
  exact label_lookup_chunk1 39 (by decide) (by decide)
theorem label_good39 : LabelGood 39 := by
  unfold LabelGood
  rw [label_lookup39]
  decide
theorem label_lookup40 : recordedOverlayLabels[40]! = recordedOverlayLabelsChunk1[8]! := by
  exact label_lookup_chunk1 40 (by decide) (by decide)
theorem label_good40 : LabelGood 40 := by
  unfold LabelGood
  rw [label_lookup40]
  decide
theorem label_lookup41 : recordedOverlayLabels[41]! = recordedOverlayLabelsChunk1[9]! := by
  exact label_lookup_chunk1 41 (by decide) (by decide)
theorem label_good41 : LabelGood 41 := by
  unfold LabelGood
  rw [label_lookup41]
  decide
theorem label_lookup42 : recordedOverlayLabels[42]! = recordedOverlayLabelsChunk1[10]! := by
  exact label_lookup_chunk1 42 (by decide) (by decide)
theorem label_good42 : LabelGood 42 := by
  unfold LabelGood
  rw [label_lookup42]
  decide
theorem label_lookup43 : recordedOverlayLabels[43]! = recordedOverlayLabelsChunk1[11]! := by
  exact label_lookup_chunk1 43 (by decide) (by decide)
theorem label_good43 : LabelGood 43 := by
  unfold LabelGood
  rw [label_lookup43]
  decide
theorem label_lookup44 : recordedOverlayLabels[44]! = recordedOverlayLabelsChunk1[12]! := by
  exact label_lookup_chunk1 44 (by decide) (by decide)
theorem label_good44 : LabelGood 44 := by
  unfold LabelGood
  rw [label_lookup44]
  decide
theorem label_lookup45 : recordedOverlayLabels[45]! = recordedOverlayLabelsChunk1[13]! := by
  exact label_lookup_chunk1 45 (by decide) (by decide)
theorem label_good45 : LabelGood 45 := by
  unfold LabelGood
  rw [label_lookup45]
  decide
theorem label_lookup46 : recordedOverlayLabels[46]! = recordedOverlayLabelsChunk1[14]! := by
  exact label_lookup_chunk1 46 (by decide) (by decide)
theorem label_good46 : LabelGood 46 := by
  unfold LabelGood
  rw [label_lookup46]
  decide
theorem label_lookup47 : recordedOverlayLabels[47]! = recordedOverlayLabelsChunk1[15]! := by
  exact label_lookup_chunk1 47 (by decide) (by decide)
theorem label_good47 : LabelGood 47 := by
  unfold LabelGood
  rw [label_lookup47]
  decide
theorem labels_range2 : AllRange LabelGood 32 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good32, (List.forall_mem_cons.mpr ⟨label_good33, (List.forall_mem_cons.mpr ⟨label_good34, (List.forall_mem_cons.mpr ⟨label_good35, (List.forall_mem_cons.mpr ⟨label_good36, (List.forall_mem_cons.mpr ⟨label_good37, (List.forall_mem_cons.mpr ⟨label_good38, (List.forall_mem_cons.mpr ⟨label_good39, (List.forall_mem_cons.mpr ⟨label_good40, (List.forall_mem_cons.mpr ⟨label_good41, (List.forall_mem_cons.mpr ⟨label_good42, (List.forall_mem_cons.mpr ⟨label_good43, (List.forall_mem_cons.mpr ⟨label_good44, (List.forall_mem_cons.mpr ⟨label_good45, (List.forall_mem_cons.mpr ⟨label_good46, (List.forall_mem_cons.mpr ⟨label_good47, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range2
