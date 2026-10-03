import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup176 : recordedOverlayLabels[176]! = recordedOverlayLabelsChunk5[16]! := by
  exact label_lookup_chunk5 176 (by decide) (by decide)
theorem label_good176 : LabelGood 176 := by
  unfold LabelGood
  rw [label_lookup176]
  decide
theorem label_lookup177 : recordedOverlayLabels[177]! = recordedOverlayLabelsChunk5[17]! := by
  exact label_lookup_chunk5 177 (by decide) (by decide)
theorem label_good177 : LabelGood 177 := by
  unfold LabelGood
  rw [label_lookup177]
  decide
theorem label_lookup178 : recordedOverlayLabels[178]! = recordedOverlayLabelsChunk5[18]! := by
  exact label_lookup_chunk5 178 (by decide) (by decide)
theorem label_good178 : LabelGood 178 := by
  unfold LabelGood
  rw [label_lookup178]
  decide
theorem label_lookup179 : recordedOverlayLabels[179]! = recordedOverlayLabelsChunk5[19]! := by
  exact label_lookup_chunk5 179 (by decide) (by decide)
theorem label_good179 : LabelGood 179 := by
  unfold LabelGood
  rw [label_lookup179]
  decide
theorem label_lookup180 : recordedOverlayLabels[180]! = recordedOverlayLabelsChunk5[20]! := by
  exact label_lookup_chunk5 180 (by decide) (by decide)
theorem label_good180 : LabelGood 180 := by
  unfold LabelGood
  rw [label_lookup180]
  decide
theorem label_lookup181 : recordedOverlayLabels[181]! = recordedOverlayLabelsChunk5[21]! := by
  exact label_lookup_chunk5 181 (by decide) (by decide)
theorem label_good181 : LabelGood 181 := by
  unfold LabelGood
  rw [label_lookup181]
  decide
theorem label_lookup182 : recordedOverlayLabels[182]! = recordedOverlayLabelsChunk5[22]! := by
  exact label_lookup_chunk5 182 (by decide) (by decide)
theorem label_good182 : LabelGood 182 := by
  unfold LabelGood
  rw [label_lookup182]
  decide
theorem label_lookup183 : recordedOverlayLabels[183]! = recordedOverlayLabelsChunk5[23]! := by
  exact label_lookup_chunk5 183 (by decide) (by decide)
theorem label_good183 : LabelGood 183 := by
  unfold LabelGood
  rw [label_lookup183]
  decide
theorem label_lookup184 : recordedOverlayLabels[184]! = recordedOverlayLabelsChunk5[24]! := by
  exact label_lookup_chunk5 184 (by decide) (by decide)
theorem label_good184 : LabelGood 184 := by
  unfold LabelGood
  rw [label_lookup184]
  decide
theorem label_lookup185 : recordedOverlayLabels[185]! = recordedOverlayLabelsChunk5[25]! := by
  exact label_lookup_chunk5 185 (by decide) (by decide)
theorem label_good185 : LabelGood 185 := by
  unfold LabelGood
  rw [label_lookup185]
  decide
theorem label_lookup186 : recordedOverlayLabels[186]! = recordedOverlayLabelsChunk5[26]! := by
  exact label_lookup_chunk5 186 (by decide) (by decide)
theorem label_good186 : LabelGood 186 := by
  unfold LabelGood
  rw [label_lookup186]
  decide
theorem label_lookup187 : recordedOverlayLabels[187]! = recordedOverlayLabelsChunk5[27]! := by
  exact label_lookup_chunk5 187 (by decide) (by decide)
theorem label_good187 : LabelGood 187 := by
  unfold LabelGood
  rw [label_lookup187]
  decide
theorem label_lookup188 : recordedOverlayLabels[188]! = recordedOverlayLabelsChunk5[28]! := by
  exact label_lookup_chunk5 188 (by decide) (by decide)
theorem label_good188 : LabelGood 188 := by
  unfold LabelGood
  rw [label_lookup188]
  decide
theorem label_lookup189 : recordedOverlayLabels[189]! = recordedOverlayLabelsChunk5[29]! := by
  exact label_lookup_chunk5 189 (by decide) (by decide)
theorem label_good189 : LabelGood 189 := by
  unfold LabelGood
  rw [label_lookup189]
  decide
theorem label_lookup190 : recordedOverlayLabels[190]! = recordedOverlayLabelsChunk5[30]! := by
  exact label_lookup_chunk5 190 (by decide) (by decide)
theorem label_good190 : LabelGood 190 := by
  unfold LabelGood
  rw [label_lookup190]
  decide
theorem label_lookup191 : recordedOverlayLabels[191]! = recordedOverlayLabelsChunk5[31]! := by
  exact label_lookup_chunk5 191 (by decide) (by decide)
theorem label_good191 : LabelGood 191 := by
  unfold LabelGood
  rw [label_lookup191]
  decide
theorem labels_range11 : AllRange LabelGood 176 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good176, (List.forall_mem_cons.mpr ⟨label_good177, (List.forall_mem_cons.mpr ⟨label_good178, (List.forall_mem_cons.mpr ⟨label_good179, (List.forall_mem_cons.mpr ⟨label_good180, (List.forall_mem_cons.mpr ⟨label_good181, (List.forall_mem_cons.mpr ⟨label_good182, (List.forall_mem_cons.mpr ⟨label_good183, (List.forall_mem_cons.mpr ⟨label_good184, (List.forall_mem_cons.mpr ⟨label_good185, (List.forall_mem_cons.mpr ⟨label_good186, (List.forall_mem_cons.mpr ⟨label_good187, (List.forall_mem_cons.mpr ⟨label_good188, (List.forall_mem_cons.mpr ⟨label_good189, (List.forall_mem_cons.mpr ⟨label_good190, (List.forall_mem_cons.mpr ⟨label_good191, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range11
