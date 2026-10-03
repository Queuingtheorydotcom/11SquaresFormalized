import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup144 : recordedOverlayLabels[144]! = recordedOverlayLabelsChunk4[16]! := by
  exact label_lookup_chunk4 144 (by decide) (by decide)
theorem label_good144 : LabelGood 144 := by
  unfold LabelGood
  rw [label_lookup144]
  decide
theorem label_lookup145 : recordedOverlayLabels[145]! = recordedOverlayLabelsChunk4[17]! := by
  exact label_lookup_chunk4 145 (by decide) (by decide)
theorem label_good145 : LabelGood 145 := by
  unfold LabelGood
  rw [label_lookup145]
  decide
theorem label_lookup146 : recordedOverlayLabels[146]! = recordedOverlayLabelsChunk4[18]! := by
  exact label_lookup_chunk4 146 (by decide) (by decide)
theorem label_good146 : LabelGood 146 := by
  unfold LabelGood
  rw [label_lookup146]
  decide
theorem label_lookup147 : recordedOverlayLabels[147]! = recordedOverlayLabelsChunk4[19]! := by
  exact label_lookup_chunk4 147 (by decide) (by decide)
theorem label_good147 : LabelGood 147 := by
  unfold LabelGood
  rw [label_lookup147]
  decide
theorem label_lookup148 : recordedOverlayLabels[148]! = recordedOverlayLabelsChunk4[20]! := by
  exact label_lookup_chunk4 148 (by decide) (by decide)
theorem label_good148 : LabelGood 148 := by
  unfold LabelGood
  rw [label_lookup148]
  decide
theorem label_lookup149 : recordedOverlayLabels[149]! = recordedOverlayLabelsChunk4[21]! := by
  exact label_lookup_chunk4 149 (by decide) (by decide)
theorem label_good149 : LabelGood 149 := by
  unfold LabelGood
  rw [label_lookup149]
  decide
theorem label_lookup150 : recordedOverlayLabels[150]! = recordedOverlayLabelsChunk4[22]! := by
  exact label_lookup_chunk4 150 (by decide) (by decide)
theorem label_good150 : LabelGood 150 := by
  unfold LabelGood
  rw [label_lookup150]
  decide
theorem label_lookup151 : recordedOverlayLabels[151]! = recordedOverlayLabelsChunk4[23]! := by
  exact label_lookup_chunk4 151 (by decide) (by decide)
theorem label_good151 : LabelGood 151 := by
  unfold LabelGood
  rw [label_lookup151]
  decide
theorem label_lookup152 : recordedOverlayLabels[152]! = recordedOverlayLabelsChunk4[24]! := by
  exact label_lookup_chunk4 152 (by decide) (by decide)
theorem label_good152 : LabelGood 152 := by
  unfold LabelGood
  rw [label_lookup152]
  decide
theorem label_lookup153 : recordedOverlayLabels[153]! = recordedOverlayLabelsChunk4[25]! := by
  exact label_lookup_chunk4 153 (by decide) (by decide)
theorem label_good153 : LabelGood 153 := by
  unfold LabelGood
  rw [label_lookup153]
  decide
theorem label_lookup154 : recordedOverlayLabels[154]! = recordedOverlayLabelsChunk4[26]! := by
  exact label_lookup_chunk4 154 (by decide) (by decide)
theorem label_good154 : LabelGood 154 := by
  unfold LabelGood
  rw [label_lookup154]
  decide
theorem label_lookup155 : recordedOverlayLabels[155]! = recordedOverlayLabelsChunk4[27]! := by
  exact label_lookup_chunk4 155 (by decide) (by decide)
theorem label_good155 : LabelGood 155 := by
  unfold LabelGood
  rw [label_lookup155]
  decide
theorem label_lookup156 : recordedOverlayLabels[156]! = recordedOverlayLabelsChunk4[28]! := by
  exact label_lookup_chunk4 156 (by decide) (by decide)
theorem label_good156 : LabelGood 156 := by
  unfold LabelGood
  rw [label_lookup156]
  decide
theorem label_lookup157 : recordedOverlayLabels[157]! = recordedOverlayLabelsChunk4[29]! := by
  exact label_lookup_chunk4 157 (by decide) (by decide)
theorem label_good157 : LabelGood 157 := by
  unfold LabelGood
  rw [label_lookup157]
  decide
theorem label_lookup158 : recordedOverlayLabels[158]! = recordedOverlayLabelsChunk4[30]! := by
  exact label_lookup_chunk4 158 (by decide) (by decide)
theorem label_good158 : LabelGood 158 := by
  unfold LabelGood
  rw [label_lookup158]
  decide
theorem label_lookup159 : recordedOverlayLabels[159]! = recordedOverlayLabelsChunk4[31]! := by
  exact label_lookup_chunk4 159 (by decide) (by decide)
theorem label_good159 : LabelGood 159 := by
  unfold LabelGood
  rw [label_lookup159]
  decide
theorem labels_range9 : AllRange LabelGood 144 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good144, (List.forall_mem_cons.mpr ⟨label_good145, (List.forall_mem_cons.mpr ⟨label_good146, (List.forall_mem_cons.mpr ⟨label_good147, (List.forall_mem_cons.mpr ⟨label_good148, (List.forall_mem_cons.mpr ⟨label_good149, (List.forall_mem_cons.mpr ⟨label_good150, (List.forall_mem_cons.mpr ⟨label_good151, (List.forall_mem_cons.mpr ⟨label_good152, (List.forall_mem_cons.mpr ⟨label_good153, (List.forall_mem_cons.mpr ⟨label_good154, (List.forall_mem_cons.mpr ⟨label_good155, (List.forall_mem_cons.mpr ⟨label_good156, (List.forall_mem_cons.mpr ⟨label_good157, (List.forall_mem_cons.mpr ⟨label_good158, (List.forall_mem_cons.mpr ⟨label_good159, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range9
