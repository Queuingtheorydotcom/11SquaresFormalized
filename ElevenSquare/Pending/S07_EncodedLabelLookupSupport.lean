import ElevenSquare.Pending.S07_EncodedSemanticSupport
namespace ElevenSquare.Pending.EncodedSearch


theorem lookup_left {α : Type} [Inhabited α] (as bs : Array α)
    (i : ℕ) (h : i < as.size) : (as ++ bs)[i]! = as[i]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega), getElem!_pos as i h]
  exact Array.getElem_append_left h

theorem lookup_right {α : Type} [Inhabited α] (as bs : Array α)
    (i : ℕ) (ha : as.size ≤ i) (hb : i-as.size < bs.size) :
    (as ++ bs)[i]! = bs[i-as.size]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega), getElem!_pos bs (i-as.size) hb]
  exact Array.getElem_append_right ha


theorem label_chunk_size0 : recordedOverlayLabelsChunk0.size = 32 := rfl
theorem label_chunk_size1 : recordedOverlayLabelsChunk1.size = 32 := rfl
theorem label_chunk_size2 : recordedOverlayLabelsChunk2.size = 32 := rfl
theorem label_chunk_size3 : recordedOverlayLabelsChunk3.size = 32 := rfl
theorem label_chunk_size4 : recordedOverlayLabelsChunk4.size = 32 := rfl
theorem label_chunk_size5 : recordedOverlayLabelsChunk5.size = 32 := rfl
theorem label_chunk_size6 : recordedOverlayLabelsChunk6.size = 28 := rfl
def labelPrefix0 : Array (Fin 4 → Fin 16) := recordedOverlayLabelsChunk0
theorem label_prefix_size0 : labelPrefix0.size = 32 := rfl
def labelPrefix1 : Array (Fin 4 → Fin 16) := labelPrefix0 ++ recordedOverlayLabelsChunk1
theorem label_prefix_size1 : labelPrefix1.size = 64 := by
  rw [labelPrefix1, Array.size_append, label_prefix_size0, label_chunk_size1]
def labelPrefix2 : Array (Fin 4 → Fin 16) := labelPrefix1 ++ recordedOverlayLabelsChunk2
theorem label_prefix_size2 : labelPrefix2.size = 96 := by
  rw [labelPrefix2, Array.size_append, label_prefix_size1, label_chunk_size2]
def labelPrefix3 : Array (Fin 4 → Fin 16) := labelPrefix2 ++ recordedOverlayLabelsChunk3
theorem label_prefix_size3 : labelPrefix3.size = 128 := by
  rw [labelPrefix3, Array.size_append, label_prefix_size2, label_chunk_size3]
def labelPrefix4 : Array (Fin 4 → Fin 16) := labelPrefix3 ++ recordedOverlayLabelsChunk4
theorem label_prefix_size4 : labelPrefix4.size = 160 := by
  rw [labelPrefix4, Array.size_append, label_prefix_size3, label_chunk_size4]
def labelPrefix5 : Array (Fin 4 → Fin 16) := labelPrefix4 ++ recordedOverlayLabelsChunk5
theorem label_prefix_size5 : labelPrefix5.size = 192 := by
  rw [labelPrefix5, Array.size_append, label_prefix_size4, label_chunk_size5]
def labelPrefix6 : Array (Fin 4 → Fin 16) := labelPrefix5 ++ recordedOverlayLabelsChunk6
theorem label_prefix_size6 : labelPrefix6.size = 220 := by
  rw [labelPrefix6, Array.size_append, label_prefix_size5, label_chunk_size6]
theorem label_array_eq_prefix : recordedOverlayLabels = labelPrefix6 := rfl

/-- Resolve a whole label chunk once, sharing the append proof across its entries. -/
theorem label_lookup_chunk0 (i : ℕ) (lo : 0 ≤ i) (hi : i < 32) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk0[i - 0]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 i
    (by rw [label_prefix_size5]; omega)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 i
    (by rw [label_prefix_size4]; omega)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 i
    (by rw [label_prefix_size3]; omega)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 i
    (by rw [label_prefix_size2]; omega)]
  rw [labelPrefix2, lookup_left labelPrefix1 recordedOverlayLabelsChunk2 i
    (by rw [label_prefix_size1]; omega)]
  rw [labelPrefix1, lookup_left labelPrefix0 recordedOverlayLabelsChunk1 i
    (by rw [label_prefix_size0]; omega)]
  simp only [labelPrefix0, Nat.sub_zero]

theorem label_lookup_chunk1 (i : ℕ) (lo : 32 ≤ i) (hi : i < 64) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk1[i - 32]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 i
    (by rw [label_prefix_size5]; omega)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 i
    (by rw [label_prefix_size4]; omega)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 i
    (by rw [label_prefix_size3]; omega)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 i
    (by rw [label_prefix_size2]; omega)]
  rw [labelPrefix2, lookup_left labelPrefix1 recordedOverlayLabelsChunk2 i
    (by rw [label_prefix_size1]; omega)]
  rw [labelPrefix1, lookup_right labelPrefix0 recordedOverlayLabelsChunk1 i
    (by rw [label_prefix_size0]; exact lo)
    (by rw [label_prefix_size0, label_chunk_size1]; omega), label_prefix_size0]

theorem label_lookup_chunk2 (i : ℕ) (lo : 64 ≤ i) (hi : i < 96) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk2[i - 64]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 i
    (by rw [label_prefix_size5]; omega)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 i
    (by rw [label_prefix_size4]; omega)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 i
    (by rw [label_prefix_size3]; omega)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 i
    (by rw [label_prefix_size2]; omega)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 i
    (by rw [label_prefix_size1]; exact lo)
    (by rw [label_prefix_size1, label_chunk_size2]; omega), label_prefix_size1]

theorem label_lookup_chunk3 (i : ℕ) (lo : 96 ≤ i) (hi : i < 128) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk3[i - 96]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 i
    (by rw [label_prefix_size5]; omega)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 i
    (by rw [label_prefix_size4]; omega)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 i
    (by rw [label_prefix_size3]; omega)]
  rw [labelPrefix3, lookup_right labelPrefix2 recordedOverlayLabelsChunk3 i
    (by rw [label_prefix_size2]; exact lo)
    (by rw [label_prefix_size2, label_chunk_size3]; omega), label_prefix_size2]

theorem label_lookup_chunk4 (i : ℕ) (lo : 128 ≤ i) (hi : i < 160) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk4[i - 128]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 i
    (by rw [label_prefix_size5]; omega)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 i
    (by rw [label_prefix_size4]; omega)]
  rw [labelPrefix4, lookup_right labelPrefix3 recordedOverlayLabelsChunk4 i
    (by rw [label_prefix_size3]; exact lo)
    (by rw [label_prefix_size3, label_chunk_size4]; omega), label_prefix_size3]

theorem label_lookup_chunk5 (i : ℕ) (lo : 160 ≤ i) (hi : i < 192) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk5[i - 160]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 i
    (by rw [label_prefix_size5]; omega)]
  rw [labelPrefix5, lookup_right labelPrefix4 recordedOverlayLabelsChunk5 i
    (by rw [label_prefix_size4]; exact lo)
    (by rw [label_prefix_size4, label_chunk_size5]; omega), label_prefix_size4]

theorem label_lookup_chunk6 (i : ℕ) (lo : 192 ≤ i) (hi : i < 220) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk6[i - 192]! := by
  rw [label_array_eq_prefix]
  rw [labelPrefix6, lookup_right labelPrefix5 recordedOverlayLabelsChunk6 i
    (by rw [label_prefix_size5]; exact lo)
    (by rw [label_prefix_size5, label_chunk_size6]; omega), label_prefix_size5]

end ElevenSquare.Pending.EncodedSearch
