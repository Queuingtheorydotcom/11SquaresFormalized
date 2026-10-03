import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup96 : recordedOverlayLabels[96]! = recordedOverlayLabelsChunk3[0]! := by
  exact label_lookup_chunk3 96 (by decide) (by decide)
theorem label_good96 : LabelGood 96 := by
  unfold LabelGood
  rw [label_lookup96]
  decide
theorem label_lookup97 : recordedOverlayLabels[97]! = recordedOverlayLabelsChunk3[1]! := by
  exact label_lookup_chunk3 97 (by decide) (by decide)
theorem label_good97 : LabelGood 97 := by
  unfold LabelGood
  rw [label_lookup97]
  decide
theorem label_lookup98 : recordedOverlayLabels[98]! = recordedOverlayLabelsChunk3[2]! := by
  exact label_lookup_chunk3 98 (by decide) (by decide)
theorem label_good98 : LabelGood 98 := by
  unfold LabelGood
  rw [label_lookup98]
  decide
theorem label_lookup99 : recordedOverlayLabels[99]! = recordedOverlayLabelsChunk3[3]! := by
  exact label_lookup_chunk3 99 (by decide) (by decide)
theorem label_good99 : LabelGood 99 := by
  unfold LabelGood
  rw [label_lookup99]
  decide
theorem label_lookup100 : recordedOverlayLabels[100]! = recordedOverlayLabelsChunk3[4]! := by
  exact label_lookup_chunk3 100 (by decide) (by decide)
theorem label_good100 : LabelGood 100 := by
  unfold LabelGood
  rw [label_lookup100]
  decide
theorem label_lookup101 : recordedOverlayLabels[101]! = recordedOverlayLabelsChunk3[5]! := by
  exact label_lookup_chunk3 101 (by decide) (by decide)
theorem label_good101 : LabelGood 101 := by
  unfold LabelGood
  rw [label_lookup101]
  decide
theorem label_lookup102 : recordedOverlayLabels[102]! = recordedOverlayLabelsChunk3[6]! := by
  exact label_lookup_chunk3 102 (by decide) (by decide)
theorem label_good102 : LabelGood 102 := by
  unfold LabelGood
  rw [label_lookup102]
  decide
theorem label_lookup103 : recordedOverlayLabels[103]! = recordedOverlayLabelsChunk3[7]! := by
  exact label_lookup_chunk3 103 (by decide) (by decide)
theorem label_good103 : LabelGood 103 := by
  unfold LabelGood
  rw [label_lookup103]
  decide
theorem label_lookup104 : recordedOverlayLabels[104]! = recordedOverlayLabelsChunk3[8]! := by
  exact label_lookup_chunk3 104 (by decide) (by decide)
theorem label_good104 : LabelGood 104 := by
  unfold LabelGood
  rw [label_lookup104]
  decide
theorem label_lookup105 : recordedOverlayLabels[105]! = recordedOverlayLabelsChunk3[9]! := by
  exact label_lookup_chunk3 105 (by decide) (by decide)
theorem label_good105 : LabelGood 105 := by
  unfold LabelGood
  rw [label_lookup105]
  decide
theorem label_lookup106 : recordedOverlayLabels[106]! = recordedOverlayLabelsChunk3[10]! := by
  exact label_lookup_chunk3 106 (by decide) (by decide)
theorem label_good106 : LabelGood 106 := by
  unfold LabelGood
  rw [label_lookup106]
  decide
theorem label_lookup107 : recordedOverlayLabels[107]! = recordedOverlayLabelsChunk3[11]! := by
  exact label_lookup_chunk3 107 (by decide) (by decide)
theorem label_good107 : LabelGood 107 := by
  unfold LabelGood
  rw [label_lookup107]
  decide
theorem label_lookup108 : recordedOverlayLabels[108]! = recordedOverlayLabelsChunk3[12]! := by
  exact label_lookup_chunk3 108 (by decide) (by decide)
theorem label_good108 : LabelGood 108 := by
  unfold LabelGood
  rw [label_lookup108]
  decide
theorem label_lookup109 : recordedOverlayLabels[109]! = recordedOverlayLabelsChunk3[13]! := by
  exact label_lookup_chunk3 109 (by decide) (by decide)
theorem label_good109 : LabelGood 109 := by
  unfold LabelGood
  rw [label_lookup109]
  decide
theorem label_lookup110 : recordedOverlayLabels[110]! = recordedOverlayLabelsChunk3[14]! := by
  exact label_lookup_chunk3 110 (by decide) (by decide)
theorem label_good110 : LabelGood 110 := by
  unfold LabelGood
  rw [label_lookup110]
  decide
theorem label_lookup111 : recordedOverlayLabels[111]! = recordedOverlayLabelsChunk3[15]! := by
  exact label_lookup_chunk3 111 (by decide) (by decide)
theorem label_good111 : LabelGood 111 := by
  unfold LabelGood
  rw [label_lookup111]
  decide
theorem labels_range6 : AllRange LabelGood 96 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good96, (List.forall_mem_cons.mpr ⟨label_good97, (List.forall_mem_cons.mpr ⟨label_good98, (List.forall_mem_cons.mpr ⟨label_good99, (List.forall_mem_cons.mpr ⟨label_good100, (List.forall_mem_cons.mpr ⟨label_good101, (List.forall_mem_cons.mpr ⟨label_good102, (List.forall_mem_cons.mpr ⟨label_good103, (List.forall_mem_cons.mpr ⟨label_good104, (List.forall_mem_cons.mpr ⟨label_good105, (List.forall_mem_cons.mpr ⟨label_good106, (List.forall_mem_cons.mpr ⟨label_good107, (List.forall_mem_cons.mpr ⟨label_good108, (List.forall_mem_cons.mpr ⟨label_good109, (List.forall_mem_cons.mpr ⟨label_good110, (List.forall_mem_cons.mpr ⟨label_good111, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range6
