import ElevenSquare.Pending.S06_TupleBounds

namespace ElevenSquare.Pending.CandidateLookup
open TupleBounds

theorem lookup_left {α : Type} [Inhabited α] (as bs : Array α)
    (i : ℕ) (h : i < as.size) : (as ++ bs)[i]! = as[i]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega), getElem!_pos as i h]
  exact Array.getElem_append_left h

theorem lookup_right {α : Type} [Inhabited α] (as bs : Array α)
    (i : ℕ) (ha : as.size ≤ i) (hb : i-as.size < bs.size) :
    (as ++ bs)[i]! = bs[i-as.size]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [Array.size_append]; omega), getElem!_pos bs (i-as.size) hb]
  exact Array.getElem_append_right ha

def prefix0 : Array (List ℕ) := recordedCaseTuplesChunk0
 theorem size_prefix0 : prefix0.size = 64 := tuple_block0.1

def prefix1 : Array (List ℕ) := prefix0 ++ recordedCaseTuplesChunk1
theorem size_prefix1 : prefix1.size = 128 := by
  rw [prefix1, Array.size_append, size_prefix0, tuple_block1.1]

def prefix2 : Array (List ℕ) := prefix1 ++ recordedCaseTuplesChunk2
theorem size_prefix2 : prefix2.size = 192 := by
  rw [prefix2, Array.size_append, size_prefix1, tuple_block2.1]

def prefix3 : Array (List ℕ) := prefix2 ++ recordedCaseTuplesChunk3
theorem size_prefix3 : prefix3.size = 256 := by
  rw [prefix3, Array.size_append, size_prefix2, tuple_block3.1]

def prefix4 : Array (List ℕ) := prefix3 ++ recordedCaseTuplesChunk4
theorem size_prefix4 : prefix4.size = 320 := by
  rw [prefix4, Array.size_append, size_prefix3, tuple_block4.1]

def prefix5 : Array (List ℕ) := prefix4 ++ recordedCaseTuplesChunk5
theorem size_prefix5 : prefix5.size = 384 := by
  rw [prefix5, Array.size_append, size_prefix4, tuple_block5.1]

def prefix6 : Array (List ℕ) := prefix5 ++ recordedCaseTuplesChunk6
theorem size_prefix6 : prefix6.size = 448 := by
  rw [prefix6, Array.size_append, size_prefix5, tuple_block6.1]

def prefix7 : Array (List ℕ) := prefix6 ++ recordedCaseTuplesChunk7
theorem size_prefix7 : prefix7.size = 512 := by
  rw [prefix7, Array.size_append, size_prefix6, tuple_block7.1]

def prefix8 : Array (List ℕ) := prefix7 ++ recordedCaseTuplesChunk8
theorem size_prefix8 : prefix8.size = 576 := by
  rw [prefix8, Array.size_append, size_prefix7, tuple_block8.1]

def prefix9 : Array (List ℕ) := prefix8 ++ recordedCaseTuplesChunk9
theorem size_prefix9 : prefix9.size = 640 := by
  rw [prefix9, Array.size_append, size_prefix8, tuple_block9.1]

def prefix10 : Array (List ℕ) := prefix9 ++ recordedCaseTuplesChunk10
theorem size_prefix10 : prefix10.size = 704 := by
  rw [prefix10, Array.size_append, size_prefix9, tuple_block10.1]

def prefix11 : Array (List ℕ) := prefix10 ++ recordedCaseTuplesChunk11
theorem size_prefix11 : prefix11.size = 768 := by
  rw [prefix11, Array.size_append, size_prefix10, tuple_block11.1]

def prefix12 : Array (List ℕ) := prefix11 ++ recordedCaseTuplesChunk12
theorem size_prefix12 : prefix12.size = 832 := by
  rw [prefix12, Array.size_append, size_prefix11, tuple_block12.1]

def prefix13 : Array (List ℕ) := prefix12 ++ recordedCaseTuplesChunk13
theorem size_prefix13 : prefix13.size = 896 := by
  rw [prefix13, Array.size_append, size_prefix12, tuple_block13.1]

def prefix14 : Array (List ℕ) := prefix13 ++ recordedCaseTuplesChunk14
theorem size_prefix14 : prefix14.size = 960 := by
  rw [prefix14, Array.size_append, size_prefix13, tuple_block14.1]

def prefix15 : Array (List ℕ) := prefix14 ++ recordedCaseTuplesChunk15
theorem size_prefix15 : prefix15.size = 1024 := by
  rw [prefix15, Array.size_append, size_prefix14, tuple_block15.1]

def prefix16 : Array (List ℕ) := prefix15 ++ recordedCaseTuplesChunk16
theorem size_prefix16 : prefix16.size = 1088 := by
  rw [prefix16, Array.size_append, size_prefix15, tuple_block16.1]

def prefix17 : Array (List ℕ) := prefix16 ++ recordedCaseTuplesChunk17
theorem size_prefix17 : prefix17.size = 1152 := by
  rw [prefix17, Array.size_append, size_prefix16, tuple_block17.1]

def prefix18 : Array (List ℕ) := prefix17 ++ recordedCaseTuplesChunk18
theorem size_prefix18 : prefix18.size = 1216 := by
  rw [prefix18, Array.size_append, size_prefix17, tuple_block18.1]

def prefix19 : Array (List ℕ) := prefix18 ++ recordedCaseTuplesChunk19
theorem size_prefix19 : prefix19.size = 1280 := by
  rw [prefix19, Array.size_append, size_prefix18, tuple_block19.1]

def prefix20 : Array (List ℕ) := prefix19 ++ recordedCaseTuplesChunk20
theorem size_prefix20 : prefix20.size = 1344 := by
  rw [prefix20, Array.size_append, size_prefix19, tuple_block20.1]

def prefix21 : Array (List ℕ) := prefix20 ++ recordedCaseTuplesChunk21
theorem size_prefix21 : prefix21.size = 1408 := by
  rw [prefix21, Array.size_append, size_prefix20, tuple_block21.1]

def prefix22 : Array (List ℕ) := prefix21 ++ recordedCaseTuplesChunk22
theorem size_prefix22 : prefix22.size = 1472 := by
  rw [prefix22, Array.size_append, size_prefix21, tuple_block22.1]

def prefix23 : Array (List ℕ) := prefix22 ++ recordedCaseTuplesChunk23
theorem size_prefix23 : prefix23.size = 1536 := by
  rw [prefix23, Array.size_append, size_prefix22, tuple_block23.1]

def prefix24 : Array (List ℕ) := prefix23 ++ recordedCaseTuplesChunk24
theorem size_prefix24 : prefix24.size = 1600 := by
  rw [prefix24, Array.size_append, size_prefix23, tuple_block24.1]

def prefix25 : Array (List ℕ) := prefix24 ++ recordedCaseTuplesChunk25
theorem size_prefix25 : prefix25.size = 1664 := by
  rw [prefix25, Array.size_append, size_prefix24, tuple_block25.1]

def prefix26 : Array (List ℕ) := prefix25 ++ recordedCaseTuplesChunk26
theorem size_prefix26 : prefix26.size = 1728 := by
  rw [prefix26, Array.size_append, size_prefix25, tuple_block26.1]

def prefix27 : Array (List ℕ) := prefix26 ++ recordedCaseTuplesChunk27
theorem size_prefix27 : prefix27.size = 1792 := by
  rw [prefix27, Array.size_append, size_prefix26, tuple_block27.1]

def prefix28 : Array (List ℕ) := prefix27 ++ recordedCaseTuplesChunk28
theorem size_prefix28 : prefix28.size = 1856 := by
  rw [prefix28, Array.size_append, size_prefix27, tuple_block28.1]

def prefix29 : Array (List ℕ) := prefix28 ++ recordedCaseTuplesChunk29
theorem size_prefix29 : prefix29.size = 1920 := by
  rw [prefix29, Array.size_append, size_prefix28, tuple_block29.1]

def prefix30 : Array (List ℕ) := prefix29 ++ recordedCaseTuplesChunk30
theorem size_prefix30 : prefix30.size = 1984 := by
  rw [prefix30, Array.size_append, size_prefix29, tuple_block30.1]

def prefix31 : Array (List ℕ) := prefix30 ++ recordedCaseTuplesChunk31
theorem size_prefix31 : prefix31.size = 2048 := by
  rw [prefix31, Array.size_append, size_prefix30, tuple_block31.1]

def prefix32 : Array (List ℕ) := prefix31 ++ recordedCaseTuplesChunk32
theorem size_prefix32 : prefix32.size = 2112 := by
  rw [prefix32, Array.size_append, size_prefix31, tuple_block32.1]

def prefix33 : Array (List ℕ) := prefix32 ++ recordedCaseTuplesChunk33
theorem size_prefix33 : prefix33.size = 2176 := by
  rw [prefix33, Array.size_append, size_prefix32, tuple_block33.1]

def prefix34 : Array (List ℕ) := prefix33 ++ recordedCaseTuplesChunk34
theorem size_prefix34 : prefix34.size = 2184 := by
  rw [prefix34, Array.size_append, size_prefix33, tuple_block34.1]

theorem recorded_eq_prefix : recordedCaseTuples = prefix34 := rfl
end ElevenSquare.Pending.CandidateLookup
#print axioms ElevenSquare.Pending.CandidateLookup.lookup_left
#print axioms ElevenSquare.Pending.CandidateLookup.lookup_right
