import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup192 : recordedOverlayLabels[192]! = recordedOverlayLabelsChunk6[0]! := by
  exact label_lookup_chunk6 192 (by decide) (by decide)
theorem label_good192 : LabelGood 192 := by
  unfold LabelGood
  rw [label_lookup192]
  decide
theorem label_lookup193 : recordedOverlayLabels[193]! = recordedOverlayLabelsChunk6[1]! := by
  exact label_lookup_chunk6 193 (by decide) (by decide)
theorem label_good193 : LabelGood 193 := by
  unfold LabelGood
  rw [label_lookup193]
  decide
theorem label_lookup194 : recordedOverlayLabels[194]! = recordedOverlayLabelsChunk6[2]! := by
  exact label_lookup_chunk6 194 (by decide) (by decide)
theorem label_good194 : LabelGood 194 := by
  unfold LabelGood
  rw [label_lookup194]
  decide
theorem label_lookup195 : recordedOverlayLabels[195]! = recordedOverlayLabelsChunk6[3]! := by
  exact label_lookup_chunk6 195 (by decide) (by decide)
theorem label_good195 : LabelGood 195 := by
  unfold LabelGood
  rw [label_lookup195]
  decide
theorem label_lookup196 : recordedOverlayLabels[196]! = recordedOverlayLabelsChunk6[4]! := by
  exact label_lookup_chunk6 196 (by decide) (by decide)
theorem label_good196 : LabelGood 196 := by
  unfold LabelGood
  rw [label_lookup196]
  decide
theorem label_lookup197 : recordedOverlayLabels[197]! = recordedOverlayLabelsChunk6[5]! := by
  exact label_lookup_chunk6 197 (by decide) (by decide)
theorem label_good197 : LabelGood 197 := by
  unfold LabelGood
  rw [label_lookup197]
  decide
theorem label_lookup198 : recordedOverlayLabels[198]! = recordedOverlayLabelsChunk6[6]! := by
  exact label_lookup_chunk6 198 (by decide) (by decide)
theorem label_good198 : LabelGood 198 := by
  unfold LabelGood
  rw [label_lookup198]
  decide
theorem label_lookup199 : recordedOverlayLabels[199]! = recordedOverlayLabelsChunk6[7]! := by
  exact label_lookup_chunk6 199 (by decide) (by decide)
theorem label_good199 : LabelGood 199 := by
  unfold LabelGood
  rw [label_lookup199]
  decide
theorem label_lookup200 : recordedOverlayLabels[200]! = recordedOverlayLabelsChunk6[8]! := by
  exact label_lookup_chunk6 200 (by decide) (by decide)
theorem label_good200 : LabelGood 200 := by
  unfold LabelGood
  rw [label_lookup200]
  decide
theorem label_lookup201 : recordedOverlayLabels[201]! = recordedOverlayLabelsChunk6[9]! := by
  exact label_lookup_chunk6 201 (by decide) (by decide)
theorem label_good201 : LabelGood 201 := by
  unfold LabelGood
  rw [label_lookup201]
  decide
theorem label_lookup202 : recordedOverlayLabels[202]! = recordedOverlayLabelsChunk6[10]! := by
  exact label_lookup_chunk6 202 (by decide) (by decide)
theorem label_good202 : LabelGood 202 := by
  unfold LabelGood
  rw [label_lookup202]
  decide
theorem label_lookup203 : recordedOverlayLabels[203]! = recordedOverlayLabelsChunk6[11]! := by
  exact label_lookup_chunk6 203 (by decide) (by decide)
theorem label_good203 : LabelGood 203 := by
  unfold LabelGood
  rw [label_lookup203]
  decide
theorem label_lookup204 : recordedOverlayLabels[204]! = recordedOverlayLabelsChunk6[12]! := by
  exact label_lookup_chunk6 204 (by decide) (by decide)
theorem label_good204 : LabelGood 204 := by
  unfold LabelGood
  rw [label_lookup204]
  decide
theorem label_lookup205 : recordedOverlayLabels[205]! = recordedOverlayLabelsChunk6[13]! := by
  exact label_lookup_chunk6 205 (by decide) (by decide)
theorem label_good205 : LabelGood 205 := by
  unfold LabelGood
  rw [label_lookup205]
  decide
theorem label_lookup206 : recordedOverlayLabels[206]! = recordedOverlayLabelsChunk6[14]! := by
  exact label_lookup_chunk6 206 (by decide) (by decide)
theorem label_good206 : LabelGood 206 := by
  unfold LabelGood
  rw [label_lookup206]
  decide
theorem label_lookup207 : recordedOverlayLabels[207]! = recordedOverlayLabelsChunk6[15]! := by
  exact label_lookup_chunk6 207 (by decide) (by decide)
theorem label_good207 : LabelGood 207 := by
  unfold LabelGood
  rw [label_lookup207]
  decide
theorem labels_range12 : AllRange LabelGood 192 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good192, (List.forall_mem_cons.mpr ⟨label_good193, (List.forall_mem_cons.mpr ⟨label_good194, (List.forall_mem_cons.mpr ⟨label_good195, (List.forall_mem_cons.mpr ⟨label_good196, (List.forall_mem_cons.mpr ⟨label_good197, (List.forall_mem_cons.mpr ⟨label_good198, (List.forall_mem_cons.mpr ⟨label_good199, (List.forall_mem_cons.mpr ⟨label_good200, (List.forall_mem_cons.mpr ⟨label_good201, (List.forall_mem_cons.mpr ⟨label_good202, (List.forall_mem_cons.mpr ⟨label_good203, (List.forall_mem_cons.mpr ⟨label_good204, (List.forall_mem_cons.mpr ⟨label_good205, (List.forall_mem_cons.mpr ⟨label_good206, (List.forall_mem_cons.mpr ⟨label_good207, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range12
