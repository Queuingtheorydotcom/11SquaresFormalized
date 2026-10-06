import ElevenSquare.Pending.S07_Data

/-! Bounded lookup into the frozen overlay label chunks. -/
namespace ElevenSquare.Pending.T04LabelLookup
set_option maxRecDepth 2048

private theorem lookup_left {α : Type} [Inhabited α] (as bs : Array α)
    (i : ℕ) (h : i < as.size) : (as ++ bs)[i]! = as[i]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega), getElem!_pos as i h]
  exact Array.getElem_append_left h

private theorem lookup_right {α : Type} [Inhabited α] (as bs : Array α)
    (i : ℕ) (ha : as.size ≤ i) (hb : i-as.size < bs.size) :
    (as ++ bs)[i]! = bs[i-as.size]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega), getElem!_pos bs (i-as.size) hb]
  exact Array.getElem_append_right ha

theorem chunk_size0 : recordedOverlayLabelsChunk0.size = 32 := rfl
theorem chunk_size1 : recordedOverlayLabelsChunk1.size = 32 := rfl
theorem chunk_size2 : recordedOverlayLabelsChunk2.size = 32 := rfl
theorem chunk_size3 : recordedOverlayLabelsChunk3.size = 32 := rfl
theorem chunk_size4 : recordedOverlayLabelsChunk4.size = 32 := rfl
theorem chunk_size5 : recordedOverlayLabelsChunk5.size = 32 := rfl
theorem chunk_size6 : recordedOverlayLabelsChunk6.size = 28 := rfl
def labelPrefix0 : Array (Fin 4 → Fin 16) := recordedOverlayLabelsChunk0
theorem prefix_size0 : labelPrefix0.size = 32 := rfl
def labelPrefix1 : Array (Fin 4 → Fin 16) := labelPrefix0 ++ recordedOverlayLabelsChunk1
theorem prefix_size1 : labelPrefix1.size = 64 := by
  rw [labelPrefix1, Array.size_append, prefix_size0, chunk_size1]
def labelPrefix2 : Array (Fin 4 → Fin 16) := labelPrefix1 ++ recordedOverlayLabelsChunk2
theorem prefix_size2 : labelPrefix2.size = 96 := by
  rw [labelPrefix2, Array.size_append, prefix_size1, chunk_size2]
def labelPrefix3 : Array (Fin 4 → Fin 16) := labelPrefix2 ++ recordedOverlayLabelsChunk3
theorem prefix_size3 : labelPrefix3.size = 128 := by
  rw [labelPrefix3, Array.size_append, prefix_size2, chunk_size3]
def labelPrefix4 : Array (Fin 4 → Fin 16) := labelPrefix3 ++ recordedOverlayLabelsChunk4
theorem prefix_size4 : labelPrefix4.size = 160 := by
  rw [labelPrefix4, Array.size_append, prefix_size3, chunk_size4]
def labelPrefix5 : Array (Fin 4 → Fin 16) := labelPrefix4 ++ recordedOverlayLabelsChunk5
theorem prefix_size5 : labelPrefix5.size = 192 := by
  rw [labelPrefix5, Array.size_append, prefix_size4, chunk_size5]
def labelPrefix6 : Array (Fin 4 → Fin 16) := labelPrefix5 ++ recordedOverlayLabelsChunk6
theorem prefix_size6 : labelPrefix6.size = 220 := by
  rw [labelPrefix6, Array.size_append, prefix_size5, chunk_size6]

theorem recorded_eq_prefix : recordedOverlayLabels = labelPrefix6 := rfl

theorem lookup_chunk0 (i : ℕ) (hlo : 0 ≤ i) (hhi : i < 32) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk0[i-0]! := by
  rw [recorded_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 i (by rw [prefix_size5]; omega)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 i (by rw [prefix_size4]; omega)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 i (by rw [prefix_size3]; omega)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 i (by rw [prefix_size2]; omega)]
  rw [labelPrefix2, lookup_left labelPrefix1 recordedOverlayLabelsChunk2 i (by rw [prefix_size1]; omega)]
  rw [labelPrefix1, lookup_left labelPrefix0 recordedOverlayLabelsChunk1 i (by rw [prefix_size0]; omega)]
  rw [labelPrefix0, Nat.sub_zero]

theorem lookup_chunk1 (i : ℕ) (hlo : 32 ≤ i) (hhi : i < 64) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk1[i-32]! := by
  rw [recorded_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 i (by rw [prefix_size5]; omega)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 i (by rw [prefix_size4]; omega)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 i (by rw [prefix_size3]; omega)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 i (by rw [prefix_size2]; omega)]
  rw [labelPrefix2, lookup_left labelPrefix1 recordedOverlayLabelsChunk2 i (by rw [prefix_size1]; omega)]
  rw [labelPrefix1, lookup_right labelPrefix0 recordedOverlayLabelsChunk1 i
    (by rw [prefix_size0]; omega)
    (by rw [prefix_size0, chunk_size1]; omega), prefix_size0]

theorem lookup_chunk2 (i : ℕ) (hlo : 64 ≤ i) (hhi : i < 96) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk2[i-64]! := by
  rw [recorded_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 i (by rw [prefix_size5]; omega)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 i (by rw [prefix_size4]; omega)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 i (by rw [prefix_size3]; omega)]
  rw [labelPrefix3, lookup_left labelPrefix2 recordedOverlayLabelsChunk3 i (by rw [prefix_size2]; omega)]
  rw [labelPrefix2, lookup_right labelPrefix1 recordedOverlayLabelsChunk2 i
    (by rw [prefix_size1]; omega)
    (by rw [prefix_size1, chunk_size2]; omega), prefix_size1]

theorem lookup_chunk3 (i : ℕ) (hlo : 96 ≤ i) (hhi : i < 128) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk3[i-96]! := by
  rw [recorded_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 i (by rw [prefix_size5]; omega)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 i (by rw [prefix_size4]; omega)]
  rw [labelPrefix4, lookup_left labelPrefix3 recordedOverlayLabelsChunk4 i (by rw [prefix_size3]; omega)]
  rw [labelPrefix3, lookup_right labelPrefix2 recordedOverlayLabelsChunk3 i
    (by rw [prefix_size2]; omega)
    (by rw [prefix_size2, chunk_size3]; omega), prefix_size2]

theorem lookup_chunk4 (i : ℕ) (hlo : 128 ≤ i) (hhi : i < 160) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk4[i-128]! := by
  rw [recorded_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 i (by rw [prefix_size5]; omega)]
  rw [labelPrefix5, lookup_left labelPrefix4 recordedOverlayLabelsChunk5 i (by rw [prefix_size4]; omega)]
  rw [labelPrefix4, lookup_right labelPrefix3 recordedOverlayLabelsChunk4 i
    (by rw [prefix_size3]; omega)
    (by rw [prefix_size3, chunk_size4]; omega), prefix_size3]

theorem lookup_chunk5 (i : ℕ) (hlo : 160 ≤ i) (hhi : i < 192) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk5[i-160]! := by
  rw [recorded_eq_prefix]
  rw [labelPrefix6, lookup_left labelPrefix5 recordedOverlayLabelsChunk6 i (by rw [prefix_size5]; omega)]
  rw [labelPrefix5, lookup_right labelPrefix4 recordedOverlayLabelsChunk5 i
    (by rw [prefix_size4]; omega)
    (by rw [prefix_size4, chunk_size5]; omega), prefix_size4]

theorem lookup_chunk6 (i : ℕ) (hlo : 192 ≤ i) (hhi : i < 220) :
    recordedOverlayLabels[i]! = recordedOverlayLabelsChunk6[i-192]! := by
  rw [recorded_eq_prefix]
  rw [labelPrefix6, lookup_right labelPrefix5 recordedOverlayLabelsChunk6 i
    (by rw [prefix_size5]; omega)
    (by rw [prefix_size5, chunk_size6]; omega), prefix_size5]

theorem label_of_lookup (i : ℕ) (hi : i < 220) (row : Fin 4 → Fin 16)
    (h : recordedOverlayLabels[i]! = row) : overlayLabels ⟨i, hi⟩ = row := h

end ElevenSquare.Pending.T04LabelLookup

#print axioms ElevenSquare.Pending.T04LabelLookup.lookup_chunk0
#print axioms ElevenSquare.Pending.T04LabelLookup.lookup_chunk6
