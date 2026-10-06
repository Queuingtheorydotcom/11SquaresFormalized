import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup208 : recordedOverlayLabels[208]! = recordedOverlayLabelsChunk6[16]! := by
  exact label_lookup_chunk6 208 (by decide) (by decide)
theorem label_good208 : LabelGood 208 := by
  unfold LabelGood
  rw [label_lookup208]
  decide
theorem label_lookup209 : recordedOverlayLabels[209]! = recordedOverlayLabelsChunk6[17]! := by
  exact label_lookup_chunk6 209 (by decide) (by decide)
theorem label_good209 : LabelGood 209 := by
  unfold LabelGood
  rw [label_lookup209]
  decide
theorem label_lookup210 : recordedOverlayLabels[210]! = recordedOverlayLabelsChunk6[18]! := by
  exact label_lookup_chunk6 210 (by decide) (by decide)
theorem label_good210 : LabelGood 210 := by
  unfold LabelGood
  rw [label_lookup210]
  decide
theorem label_lookup211 : recordedOverlayLabels[211]! = recordedOverlayLabelsChunk6[19]! := by
  exact label_lookup_chunk6 211 (by decide) (by decide)
theorem label_good211 : LabelGood 211 := by
  unfold LabelGood
  rw [label_lookup211]
  decide
theorem label_lookup212 : recordedOverlayLabels[212]! = recordedOverlayLabelsChunk6[20]! := by
  exact label_lookup_chunk6 212 (by decide) (by decide)
theorem label_good212 : LabelGood 212 := by
  unfold LabelGood
  rw [label_lookup212]
  decide
theorem label_lookup213 : recordedOverlayLabels[213]! = recordedOverlayLabelsChunk6[21]! := by
  exact label_lookup_chunk6 213 (by decide) (by decide)
theorem label_good213 : LabelGood 213 := by
  unfold LabelGood
  rw [label_lookup213]
  decide
theorem label_lookup214 : recordedOverlayLabels[214]! = recordedOverlayLabelsChunk6[22]! := by
  exact label_lookup_chunk6 214 (by decide) (by decide)
theorem label_good214 : LabelGood 214 := by
  unfold LabelGood
  rw [label_lookup214]
  decide
theorem label_lookup215 : recordedOverlayLabels[215]! = recordedOverlayLabelsChunk6[23]! := by
  exact label_lookup_chunk6 215 (by decide) (by decide)
theorem label_good215 : LabelGood 215 := by
  unfold LabelGood
  rw [label_lookup215]
  decide
theorem label_lookup216 : recordedOverlayLabels[216]! = recordedOverlayLabelsChunk6[24]! := by
  exact label_lookup_chunk6 216 (by decide) (by decide)
theorem label_good216 : LabelGood 216 := by
  unfold LabelGood
  rw [label_lookup216]
  decide
theorem label_lookup217 : recordedOverlayLabels[217]! = recordedOverlayLabelsChunk6[25]! := by
  exact label_lookup_chunk6 217 (by decide) (by decide)
theorem label_good217 : LabelGood 217 := by
  unfold LabelGood
  rw [label_lookup217]
  decide
theorem label_lookup218 : recordedOverlayLabels[218]! = recordedOverlayLabelsChunk6[26]! := by
  exact label_lookup_chunk6 218 (by decide) (by decide)
theorem label_good218 : LabelGood 218 := by
  unfold LabelGood
  rw [label_lookup218]
  decide
theorem label_lookup219 : recordedOverlayLabels[219]! = recordedOverlayLabelsChunk6[27]! := by
  exact label_lookup_chunk6 219 (by decide) (by decide)
theorem label_good219 : LabelGood 219 := by
  unfold LabelGood
  rw [label_lookup219]
  decide
theorem labels_range13 : AllRange LabelGood 208 12 := by
  apply AllRange.of_list
  change ∀ r ∈ [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good208, (List.forall_mem_cons.mpr ⟨label_good209, (List.forall_mem_cons.mpr ⟨label_good210, (List.forall_mem_cons.mpr ⟨label_good211, (List.forall_mem_cons.mpr ⟨label_good212, (List.forall_mem_cons.mpr ⟨label_good213, (List.forall_mem_cons.mpr ⟨label_good214, (List.forall_mem_cons.mpr ⟨label_good215, (List.forall_mem_cons.mpr ⟨label_good216, (List.forall_mem_cons.mpr ⟨label_good217, (List.forall_mem_cons.mpr ⟨label_good218, (List.forall_mem_cons.mpr ⟨label_good219, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range13
