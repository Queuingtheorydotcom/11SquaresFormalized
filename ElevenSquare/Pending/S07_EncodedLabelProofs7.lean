import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup112 : recordedOverlayLabels[112]! = recordedOverlayLabelsChunk3[16]! := by
  exact label_lookup_chunk3 112 (by decide) (by decide)
theorem label_good112 : LabelGood 112 := by
  unfold LabelGood
  rw [label_lookup112]
  decide
theorem label_lookup113 : recordedOverlayLabels[113]! = recordedOverlayLabelsChunk3[17]! := by
  exact label_lookup_chunk3 113 (by decide) (by decide)
theorem label_good113 : LabelGood 113 := by
  unfold LabelGood
  rw [label_lookup113]
  decide
theorem label_lookup114 : recordedOverlayLabels[114]! = recordedOverlayLabelsChunk3[18]! := by
  exact label_lookup_chunk3 114 (by decide) (by decide)
theorem label_good114 : LabelGood 114 := by
  unfold LabelGood
  rw [label_lookup114]
  decide
theorem label_lookup115 : recordedOverlayLabels[115]! = recordedOverlayLabelsChunk3[19]! := by
  exact label_lookup_chunk3 115 (by decide) (by decide)
theorem label_good115 : LabelGood 115 := by
  unfold LabelGood
  rw [label_lookup115]
  decide
theorem label_lookup116 : recordedOverlayLabels[116]! = recordedOverlayLabelsChunk3[20]! := by
  exact label_lookup_chunk3 116 (by decide) (by decide)
theorem label_good116 : LabelGood 116 := by
  unfold LabelGood
  rw [label_lookup116]
  decide
theorem label_lookup117 : recordedOverlayLabels[117]! = recordedOverlayLabelsChunk3[21]! := by
  exact label_lookup_chunk3 117 (by decide) (by decide)
theorem label_good117 : LabelGood 117 := by
  unfold LabelGood
  rw [label_lookup117]
  decide
theorem label_lookup118 : recordedOverlayLabels[118]! = recordedOverlayLabelsChunk3[22]! := by
  exact label_lookup_chunk3 118 (by decide) (by decide)
theorem label_good118 : LabelGood 118 := by
  unfold LabelGood
  rw [label_lookup118]
  decide
theorem label_lookup119 : recordedOverlayLabels[119]! = recordedOverlayLabelsChunk3[23]! := by
  exact label_lookup_chunk3 119 (by decide) (by decide)
theorem label_good119 : LabelGood 119 := by
  unfold LabelGood
  rw [label_lookup119]
  decide
theorem label_lookup120 : recordedOverlayLabels[120]! = recordedOverlayLabelsChunk3[24]! := by
  exact label_lookup_chunk3 120 (by decide) (by decide)
theorem label_good120 : LabelGood 120 := by
  unfold LabelGood
  rw [label_lookup120]
  decide
theorem label_lookup121 : recordedOverlayLabels[121]! = recordedOverlayLabelsChunk3[25]! := by
  exact label_lookup_chunk3 121 (by decide) (by decide)
theorem label_good121 : LabelGood 121 := by
  unfold LabelGood
  rw [label_lookup121]
  decide
theorem label_lookup122 : recordedOverlayLabels[122]! = recordedOverlayLabelsChunk3[26]! := by
  exact label_lookup_chunk3 122 (by decide) (by decide)
theorem label_good122 : LabelGood 122 := by
  unfold LabelGood
  rw [label_lookup122]
  decide
theorem label_lookup123 : recordedOverlayLabels[123]! = recordedOverlayLabelsChunk3[27]! := by
  exact label_lookup_chunk3 123 (by decide) (by decide)
theorem label_good123 : LabelGood 123 := by
  unfold LabelGood
  rw [label_lookup123]
  decide
theorem label_lookup124 : recordedOverlayLabels[124]! = recordedOverlayLabelsChunk3[28]! := by
  exact label_lookup_chunk3 124 (by decide) (by decide)
theorem label_good124 : LabelGood 124 := by
  unfold LabelGood
  rw [label_lookup124]
  decide
theorem label_lookup125 : recordedOverlayLabels[125]! = recordedOverlayLabelsChunk3[29]! := by
  exact label_lookup_chunk3 125 (by decide) (by decide)
theorem label_good125 : LabelGood 125 := by
  unfold LabelGood
  rw [label_lookup125]
  decide
theorem label_lookup126 : recordedOverlayLabels[126]! = recordedOverlayLabelsChunk3[30]! := by
  exact label_lookup_chunk3 126 (by decide) (by decide)
theorem label_good126 : LabelGood 126 := by
  unfold LabelGood
  rw [label_lookup126]
  decide
theorem label_lookup127 : recordedOverlayLabels[127]! = recordedOverlayLabelsChunk3[31]! := by
  exact label_lookup_chunk3 127 (by decide) (by decide)
theorem label_good127 : LabelGood 127 := by
  unfold LabelGood
  rw [label_lookup127]
  decide
theorem labels_range7 : AllRange LabelGood 112 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good112, (List.forall_mem_cons.mpr ⟨label_good113, (List.forall_mem_cons.mpr ⟨label_good114, (List.forall_mem_cons.mpr ⟨label_good115, (List.forall_mem_cons.mpr ⟨label_good116, (List.forall_mem_cons.mpr ⟨label_good117, (List.forall_mem_cons.mpr ⟨label_good118, (List.forall_mem_cons.mpr ⟨label_good119, (List.forall_mem_cons.mpr ⟨label_good120, (List.forall_mem_cons.mpr ⟨label_good121, (List.forall_mem_cons.mpr ⟨label_good122, (List.forall_mem_cons.mpr ⟨label_good123, (List.forall_mem_cons.mpr ⟨label_good124, (List.forall_mem_cons.mpr ⟨label_good125, (List.forall_mem_cons.mpr ⟨label_good126, (List.forall_mem_cons.mpr ⟨label_good127, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range7
