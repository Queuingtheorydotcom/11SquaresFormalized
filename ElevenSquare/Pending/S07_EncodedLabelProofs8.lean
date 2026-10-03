import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup128 : recordedOverlayLabels[128]! = recordedOverlayLabelsChunk4[0]! := by
  exact label_lookup_chunk4 128 (by decide) (by decide)
theorem label_good128 : LabelGood 128 := by
  unfold LabelGood
  rw [label_lookup128]
  decide
theorem label_lookup129 : recordedOverlayLabels[129]! = recordedOverlayLabelsChunk4[1]! := by
  exact label_lookup_chunk4 129 (by decide) (by decide)
theorem label_good129 : LabelGood 129 := by
  unfold LabelGood
  rw [label_lookup129]
  decide
theorem label_lookup130 : recordedOverlayLabels[130]! = recordedOverlayLabelsChunk4[2]! := by
  exact label_lookup_chunk4 130 (by decide) (by decide)
theorem label_good130 : LabelGood 130 := by
  unfold LabelGood
  rw [label_lookup130]
  decide
theorem label_lookup131 : recordedOverlayLabels[131]! = recordedOverlayLabelsChunk4[3]! := by
  exact label_lookup_chunk4 131 (by decide) (by decide)
theorem label_good131 : LabelGood 131 := by
  unfold LabelGood
  rw [label_lookup131]
  decide
theorem label_lookup132 : recordedOverlayLabels[132]! = recordedOverlayLabelsChunk4[4]! := by
  exact label_lookup_chunk4 132 (by decide) (by decide)
theorem label_good132 : LabelGood 132 := by
  unfold LabelGood
  rw [label_lookup132]
  decide
theorem label_lookup133 : recordedOverlayLabels[133]! = recordedOverlayLabelsChunk4[5]! := by
  exact label_lookup_chunk4 133 (by decide) (by decide)
theorem label_good133 : LabelGood 133 := by
  unfold LabelGood
  rw [label_lookup133]
  decide
theorem label_lookup134 : recordedOverlayLabels[134]! = recordedOverlayLabelsChunk4[6]! := by
  exact label_lookup_chunk4 134 (by decide) (by decide)
theorem label_good134 : LabelGood 134 := by
  unfold LabelGood
  rw [label_lookup134]
  decide
theorem label_lookup135 : recordedOverlayLabels[135]! = recordedOverlayLabelsChunk4[7]! := by
  exact label_lookup_chunk4 135 (by decide) (by decide)
theorem label_good135 : LabelGood 135 := by
  unfold LabelGood
  rw [label_lookup135]
  decide
theorem label_lookup136 : recordedOverlayLabels[136]! = recordedOverlayLabelsChunk4[8]! := by
  exact label_lookup_chunk4 136 (by decide) (by decide)
theorem label_good136 : LabelGood 136 := by
  unfold LabelGood
  rw [label_lookup136]
  decide
theorem label_lookup137 : recordedOverlayLabels[137]! = recordedOverlayLabelsChunk4[9]! := by
  exact label_lookup_chunk4 137 (by decide) (by decide)
theorem label_good137 : LabelGood 137 := by
  unfold LabelGood
  rw [label_lookup137]
  decide
theorem label_lookup138 : recordedOverlayLabels[138]! = recordedOverlayLabelsChunk4[10]! := by
  exact label_lookup_chunk4 138 (by decide) (by decide)
theorem label_good138 : LabelGood 138 := by
  unfold LabelGood
  rw [label_lookup138]
  decide
theorem label_lookup139 : recordedOverlayLabels[139]! = recordedOverlayLabelsChunk4[11]! := by
  exact label_lookup_chunk4 139 (by decide) (by decide)
theorem label_good139 : LabelGood 139 := by
  unfold LabelGood
  rw [label_lookup139]
  decide
theorem label_lookup140 : recordedOverlayLabels[140]! = recordedOverlayLabelsChunk4[12]! := by
  exact label_lookup_chunk4 140 (by decide) (by decide)
theorem label_good140 : LabelGood 140 := by
  unfold LabelGood
  rw [label_lookup140]
  decide
theorem label_lookup141 : recordedOverlayLabels[141]! = recordedOverlayLabelsChunk4[13]! := by
  exact label_lookup_chunk4 141 (by decide) (by decide)
theorem label_good141 : LabelGood 141 := by
  unfold LabelGood
  rw [label_lookup141]
  decide
theorem label_lookup142 : recordedOverlayLabels[142]! = recordedOverlayLabelsChunk4[14]! := by
  exact label_lookup_chunk4 142 (by decide) (by decide)
theorem label_good142 : LabelGood 142 := by
  unfold LabelGood
  rw [label_lookup142]
  decide
theorem label_lookup143 : recordedOverlayLabels[143]! = recordedOverlayLabelsChunk4[15]! := by
  exact label_lookup_chunk4 143 (by decide) (by decide)
theorem label_good143 : LabelGood 143 := by
  unfold LabelGood
  rw [label_lookup143]
  decide
theorem labels_range8 : AllRange LabelGood 128 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good128, (List.forall_mem_cons.mpr ⟨label_good129, (List.forall_mem_cons.mpr ⟨label_good130, (List.forall_mem_cons.mpr ⟨label_good131, (List.forall_mem_cons.mpr ⟨label_good132, (List.forall_mem_cons.mpr ⟨label_good133, (List.forall_mem_cons.mpr ⟨label_good134, (List.forall_mem_cons.mpr ⟨label_good135, (List.forall_mem_cons.mpr ⟨label_good136, (List.forall_mem_cons.mpr ⟨label_good137, (List.forall_mem_cons.mpr ⟨label_good138, (List.forall_mem_cons.mpr ⟨label_good139, (List.forall_mem_cons.mpr ⟨label_good140, (List.forall_mem_cons.mpr ⟨label_good141, (List.forall_mem_cons.mpr ⟨label_good142, (List.forall_mem_cons.mpr ⟨label_good143, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range8
