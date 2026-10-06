import ElevenSquare.Pending.S07_EncodedLabelLookupSupport
namespace ElevenSquare.Pending.EncodedSearch
theorem label_lookup160 : recordedOverlayLabels[160]! = recordedOverlayLabelsChunk5[0]! := by
  exact label_lookup_chunk5 160 (by decide) (by decide)
theorem label_good160 : LabelGood 160 := by
  unfold LabelGood
  rw [label_lookup160]
  decide
theorem label_lookup161 : recordedOverlayLabels[161]! = recordedOverlayLabelsChunk5[1]! := by
  exact label_lookup_chunk5 161 (by decide) (by decide)
theorem label_good161 : LabelGood 161 := by
  unfold LabelGood
  rw [label_lookup161]
  decide
theorem label_lookup162 : recordedOverlayLabels[162]! = recordedOverlayLabelsChunk5[2]! := by
  exact label_lookup_chunk5 162 (by decide) (by decide)
theorem label_good162 : LabelGood 162 := by
  unfold LabelGood
  rw [label_lookup162]
  decide
theorem label_lookup163 : recordedOverlayLabels[163]! = recordedOverlayLabelsChunk5[3]! := by
  exact label_lookup_chunk5 163 (by decide) (by decide)
theorem label_good163 : LabelGood 163 := by
  unfold LabelGood
  rw [label_lookup163]
  decide
theorem label_lookup164 : recordedOverlayLabels[164]! = recordedOverlayLabelsChunk5[4]! := by
  exact label_lookup_chunk5 164 (by decide) (by decide)
theorem label_good164 : LabelGood 164 := by
  unfold LabelGood
  rw [label_lookup164]
  decide
theorem label_lookup165 : recordedOverlayLabels[165]! = recordedOverlayLabelsChunk5[5]! := by
  exact label_lookup_chunk5 165 (by decide) (by decide)
theorem label_good165 : LabelGood 165 := by
  unfold LabelGood
  rw [label_lookup165]
  decide
theorem label_lookup166 : recordedOverlayLabels[166]! = recordedOverlayLabelsChunk5[6]! := by
  exact label_lookup_chunk5 166 (by decide) (by decide)
theorem label_good166 : LabelGood 166 := by
  unfold LabelGood
  rw [label_lookup166]
  decide
theorem label_lookup167 : recordedOverlayLabels[167]! = recordedOverlayLabelsChunk5[7]! := by
  exact label_lookup_chunk5 167 (by decide) (by decide)
theorem label_good167 : LabelGood 167 := by
  unfold LabelGood
  rw [label_lookup167]
  decide
theorem label_lookup168 : recordedOverlayLabels[168]! = recordedOverlayLabelsChunk5[8]! := by
  exact label_lookup_chunk5 168 (by decide) (by decide)
theorem label_good168 : LabelGood 168 := by
  unfold LabelGood
  rw [label_lookup168]
  decide
theorem label_lookup169 : recordedOverlayLabels[169]! = recordedOverlayLabelsChunk5[9]! := by
  exact label_lookup_chunk5 169 (by decide) (by decide)
theorem label_good169 : LabelGood 169 := by
  unfold LabelGood
  rw [label_lookup169]
  decide
theorem label_lookup170 : recordedOverlayLabels[170]! = recordedOverlayLabelsChunk5[10]! := by
  exact label_lookup_chunk5 170 (by decide) (by decide)
theorem label_good170 : LabelGood 170 := by
  unfold LabelGood
  rw [label_lookup170]
  decide
theorem label_lookup171 : recordedOverlayLabels[171]! = recordedOverlayLabelsChunk5[11]! := by
  exact label_lookup_chunk5 171 (by decide) (by decide)
theorem label_good171 : LabelGood 171 := by
  unfold LabelGood
  rw [label_lookup171]
  decide
theorem label_lookup172 : recordedOverlayLabels[172]! = recordedOverlayLabelsChunk5[12]! := by
  exact label_lookup_chunk5 172 (by decide) (by decide)
theorem label_good172 : LabelGood 172 := by
  unfold LabelGood
  rw [label_lookup172]
  decide
theorem label_lookup173 : recordedOverlayLabels[173]! = recordedOverlayLabelsChunk5[13]! := by
  exact label_lookup_chunk5 173 (by decide) (by decide)
theorem label_good173 : LabelGood 173 := by
  unfold LabelGood
  rw [label_lookup173]
  decide
theorem label_lookup174 : recordedOverlayLabels[174]! = recordedOverlayLabelsChunk5[14]! := by
  exact label_lookup_chunk5 174 (by decide) (by decide)
theorem label_good174 : LabelGood 174 := by
  unfold LabelGood
  rw [label_lookup174]
  decide
theorem label_lookup175 : recordedOverlayLabels[175]! = recordedOverlayLabelsChunk5[15]! := by
  exact label_lookup_chunk5 175 (by decide) (by decide)
theorem label_good175 : LabelGood 175 := by
  unfold LabelGood
  rw [label_lookup175]
  decide
theorem labels_range10 : AllRange LabelGood 160 16 := by
  apply AllRange.of_list
  change ∀ r ∈ [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175], LabelGood r
  exact (List.forall_mem_cons.mpr ⟨label_good160, (List.forall_mem_cons.mpr ⟨label_good161, (List.forall_mem_cons.mpr ⟨label_good162, (List.forall_mem_cons.mpr ⟨label_good163, (List.forall_mem_cons.mpr ⟨label_good164, (List.forall_mem_cons.mpr ⟨label_good165, (List.forall_mem_cons.mpr ⟨label_good166, (List.forall_mem_cons.mpr ⟨label_good167, (List.forall_mem_cons.mpr ⟨label_good168, (List.forall_mem_cons.mpr ⟨label_good169, (List.forall_mem_cons.mpr ⟨label_good170, (List.forall_mem_cons.mpr ⟨label_good171, (List.forall_mem_cons.mpr ⟨label_good172, (List.forall_mem_cons.mpr ⟨label_good173, (List.forall_mem_cons.mpr ⟨label_good174, (List.forall_mem_cons.mpr ⟨label_good175, List.forall_mem_nil _⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end ElevenSquare.Pending.EncodedSearch
#print axioms ElevenSquare.Pending.EncodedSearch.labels_range10
