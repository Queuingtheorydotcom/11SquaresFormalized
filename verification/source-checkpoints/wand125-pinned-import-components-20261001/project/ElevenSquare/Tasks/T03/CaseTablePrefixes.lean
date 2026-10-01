import ElevenSquare.Pending.S06_Data

namespace ElevenSquare.Pending.T03.CaseTable
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem get_append_left (a b : Array (List ℕ)) (k : ℕ) (hk : k < a.size) :
    (a++b)[k]! = a[k]! := by
  have hab : k < (a++b).size := by rw [Array.size_append]; omega
  rw [_root_.getElem!_pos (a++b) k hab,_root_.getElem!_pos a k hk]
  exact Array.get_append_left hk

theorem get_append_right (a b : Array (List ℕ)) (k : ℕ)
    (h0 : a.size ≤ k) (h1 : k < a.size+b.size) :
    (a++b)[k]! = b[k-a.size]! := by
  have hab : k < (a++b).size := by rwa [Array.size_append]
  have hb : k-a.size < b.size := by omega
  rw [_root_.getElem!_pos (a++b) k hab,_root_.getElem!_pos b (k-a.size) hb]
  exact Array.get_append_right h0

theorem chunk00_size : recordedCaseTuplesChunk0.size = 64 := by rfl
@[irreducible] def prefix00 : Array (List ℕ) := recordedCaseTuplesChunk0
theorem prefix00_size : prefix00.size = 64 := by
  rfl

theorem chunk01_size : recordedCaseTuplesChunk1.size = 64 := by rfl
@[irreducible] def prefix01 : Array (List ℕ) := prefix00 ++ recordedCaseTuplesChunk1
theorem prefix01_size : prefix01.size = 128 := by
  rw [prefix01,Array.size_append,prefix00_size,chunk01_size]

theorem chunk02_size : recordedCaseTuplesChunk2.size = 64 := by rfl
@[irreducible] def prefix02 : Array (List ℕ) := prefix01 ++ recordedCaseTuplesChunk2
theorem prefix02_size : prefix02.size = 192 := by
  rw [prefix02,Array.size_append,prefix01_size,chunk02_size]

theorem chunk03_size : recordedCaseTuplesChunk3.size = 64 := by rfl
@[irreducible] def prefix03 : Array (List ℕ) := prefix02 ++ recordedCaseTuplesChunk3
theorem prefix03_size : prefix03.size = 256 := by
  rw [prefix03,Array.size_append,prefix02_size,chunk03_size]

theorem chunk04_size : recordedCaseTuplesChunk4.size = 64 := by rfl
@[irreducible] def prefix04 : Array (List ℕ) := prefix03 ++ recordedCaseTuplesChunk4
theorem prefix04_size : prefix04.size = 320 := by
  rw [prefix04,Array.size_append,prefix03_size,chunk04_size]

theorem chunk05_size : recordedCaseTuplesChunk5.size = 64 := by rfl
@[irreducible] def prefix05 : Array (List ℕ) := prefix04 ++ recordedCaseTuplesChunk5
theorem prefix05_size : prefix05.size = 384 := by
  rw [prefix05,Array.size_append,prefix04_size,chunk05_size]

theorem chunk06_size : recordedCaseTuplesChunk6.size = 64 := by rfl
@[irreducible] def prefix06 : Array (List ℕ) := prefix05 ++ recordedCaseTuplesChunk6
theorem prefix06_size : prefix06.size = 448 := by
  rw [prefix06,Array.size_append,prefix05_size,chunk06_size]

theorem chunk07_size : recordedCaseTuplesChunk7.size = 64 := by rfl
@[irreducible] def prefix07 : Array (List ℕ) := prefix06 ++ recordedCaseTuplesChunk7
theorem prefix07_size : prefix07.size = 512 := by
  rw [prefix07,Array.size_append,prefix06_size,chunk07_size]

theorem chunk08_size : recordedCaseTuplesChunk8.size = 64 := by rfl
@[irreducible] def prefix08 : Array (List ℕ) := prefix07 ++ recordedCaseTuplesChunk8
theorem prefix08_size : prefix08.size = 576 := by
  rw [prefix08,Array.size_append,prefix07_size,chunk08_size]

theorem chunk09_size : recordedCaseTuplesChunk9.size = 64 := by rfl
@[irreducible] def prefix09 : Array (List ℕ) := prefix08 ++ recordedCaseTuplesChunk9
theorem prefix09_size : prefix09.size = 640 := by
  rw [prefix09,Array.size_append,prefix08_size,chunk09_size]

theorem chunk10_size : recordedCaseTuplesChunk10.size = 64 := by rfl
@[irreducible] def prefix10 : Array (List ℕ) := prefix09 ++ recordedCaseTuplesChunk10
theorem prefix10_size : prefix10.size = 704 := by
  rw [prefix10,Array.size_append,prefix09_size,chunk10_size]

theorem chunk11_size : recordedCaseTuplesChunk11.size = 64 := by rfl
@[irreducible] def prefix11 : Array (List ℕ) := prefix10 ++ recordedCaseTuplesChunk11
theorem prefix11_size : prefix11.size = 768 := by
  rw [prefix11,Array.size_append,prefix10_size,chunk11_size]

theorem chunk12_size : recordedCaseTuplesChunk12.size = 64 := by rfl
@[irreducible] def prefix12 : Array (List ℕ) := prefix11 ++ recordedCaseTuplesChunk12
theorem prefix12_size : prefix12.size = 832 := by
  rw [prefix12,Array.size_append,prefix11_size,chunk12_size]

theorem chunk13_size : recordedCaseTuplesChunk13.size = 64 := by rfl
@[irreducible] def prefix13 : Array (List ℕ) := prefix12 ++ recordedCaseTuplesChunk13
theorem prefix13_size : prefix13.size = 896 := by
  rw [prefix13,Array.size_append,prefix12_size,chunk13_size]

theorem chunk14_size : recordedCaseTuplesChunk14.size = 64 := by rfl
@[irreducible] def prefix14 : Array (List ℕ) := prefix13 ++ recordedCaseTuplesChunk14
theorem prefix14_size : prefix14.size = 960 := by
  rw [prefix14,Array.size_append,prefix13_size,chunk14_size]

theorem chunk15_size : recordedCaseTuplesChunk15.size = 64 := by rfl
@[irreducible] def prefix15 : Array (List ℕ) := prefix14 ++ recordedCaseTuplesChunk15
theorem prefix15_size : prefix15.size = 1024 := by
  rw [prefix15,Array.size_append,prefix14_size,chunk15_size]

theorem chunk16_size : recordedCaseTuplesChunk16.size = 64 := by rfl
@[irreducible] def prefix16 : Array (List ℕ) := prefix15 ++ recordedCaseTuplesChunk16
theorem prefix16_size : prefix16.size = 1088 := by
  rw [prefix16,Array.size_append,prefix15_size,chunk16_size]

theorem chunk17_size : recordedCaseTuplesChunk17.size = 64 := by rfl
@[irreducible] def prefix17 : Array (List ℕ) := prefix16 ++ recordedCaseTuplesChunk17
theorem prefix17_size : prefix17.size = 1152 := by
  rw [prefix17,Array.size_append,prefix16_size,chunk17_size]

theorem chunk18_size : recordedCaseTuplesChunk18.size = 64 := by rfl
@[irreducible] def prefix18 : Array (List ℕ) := prefix17 ++ recordedCaseTuplesChunk18
theorem prefix18_size : prefix18.size = 1216 := by
  rw [prefix18,Array.size_append,prefix17_size,chunk18_size]

theorem chunk19_size : recordedCaseTuplesChunk19.size = 64 := by rfl
@[irreducible] def prefix19 : Array (List ℕ) := prefix18 ++ recordedCaseTuplesChunk19
theorem prefix19_size : prefix19.size = 1280 := by
  rw [prefix19,Array.size_append,prefix18_size,chunk19_size]

theorem chunk20_size : recordedCaseTuplesChunk20.size = 64 := by rfl
@[irreducible] def prefix20 : Array (List ℕ) := prefix19 ++ recordedCaseTuplesChunk20
theorem prefix20_size : prefix20.size = 1344 := by
  rw [prefix20,Array.size_append,prefix19_size,chunk20_size]

theorem chunk21_size : recordedCaseTuplesChunk21.size = 64 := by rfl
@[irreducible] def prefix21 : Array (List ℕ) := prefix20 ++ recordedCaseTuplesChunk21
theorem prefix21_size : prefix21.size = 1408 := by
  rw [prefix21,Array.size_append,prefix20_size,chunk21_size]

theorem chunk22_size : recordedCaseTuplesChunk22.size = 64 := by rfl
@[irreducible] def prefix22 : Array (List ℕ) := prefix21 ++ recordedCaseTuplesChunk22
theorem prefix22_size : prefix22.size = 1472 := by
  rw [prefix22,Array.size_append,prefix21_size,chunk22_size]

theorem chunk23_size : recordedCaseTuplesChunk23.size = 64 := by rfl
@[irreducible] def prefix23 : Array (List ℕ) := prefix22 ++ recordedCaseTuplesChunk23
theorem prefix23_size : prefix23.size = 1536 := by
  rw [prefix23,Array.size_append,prefix22_size,chunk23_size]

theorem chunk24_size : recordedCaseTuplesChunk24.size = 64 := by rfl
@[irreducible] def prefix24 : Array (List ℕ) := prefix23 ++ recordedCaseTuplesChunk24
theorem prefix24_size : prefix24.size = 1600 := by
  rw [prefix24,Array.size_append,prefix23_size,chunk24_size]

theorem chunk25_size : recordedCaseTuplesChunk25.size = 64 := by rfl
@[irreducible] def prefix25 : Array (List ℕ) := prefix24 ++ recordedCaseTuplesChunk25
theorem prefix25_size : prefix25.size = 1664 := by
  rw [prefix25,Array.size_append,prefix24_size,chunk25_size]

theorem chunk26_size : recordedCaseTuplesChunk26.size = 64 := by rfl
@[irreducible] def prefix26 : Array (List ℕ) := prefix25 ++ recordedCaseTuplesChunk26
theorem prefix26_size : prefix26.size = 1728 := by
  rw [prefix26,Array.size_append,prefix25_size,chunk26_size]

theorem chunk27_size : recordedCaseTuplesChunk27.size = 64 := by rfl
@[irreducible] def prefix27 : Array (List ℕ) := prefix26 ++ recordedCaseTuplesChunk27
theorem prefix27_size : prefix27.size = 1792 := by
  rw [prefix27,Array.size_append,prefix26_size,chunk27_size]

theorem chunk28_size : recordedCaseTuplesChunk28.size = 64 := by rfl
@[irreducible] def prefix28 : Array (List ℕ) := prefix27 ++ recordedCaseTuplesChunk28
theorem prefix28_size : prefix28.size = 1856 := by
  rw [prefix28,Array.size_append,prefix27_size,chunk28_size]

theorem chunk29_size : recordedCaseTuplesChunk29.size = 64 := by rfl
@[irreducible] def prefix29 : Array (List ℕ) := prefix28 ++ recordedCaseTuplesChunk29
theorem prefix29_size : prefix29.size = 1920 := by
  rw [prefix29,Array.size_append,prefix28_size,chunk29_size]

theorem chunk30_size : recordedCaseTuplesChunk30.size = 64 := by rfl
@[irreducible] def prefix30 : Array (List ℕ) := prefix29 ++ recordedCaseTuplesChunk30
theorem prefix30_size : prefix30.size = 1984 := by
  rw [prefix30,Array.size_append,prefix29_size,chunk30_size]

theorem chunk31_size : recordedCaseTuplesChunk31.size = 64 := by rfl
@[irreducible] def prefix31 : Array (List ℕ) := prefix30 ++ recordedCaseTuplesChunk31
theorem prefix31_size : prefix31.size = 2048 := by
  rw [prefix31,Array.size_append,prefix30_size,chunk31_size]

theorem chunk32_size : recordedCaseTuplesChunk32.size = 64 := by rfl
@[irreducible] def prefix32 : Array (List ℕ) := prefix31 ++ recordedCaseTuplesChunk32
theorem prefix32_size : prefix32.size = 2112 := by
  rw [prefix32,Array.size_append,prefix31_size,chunk32_size]

theorem chunk33_size : recordedCaseTuplesChunk33.size = 64 := by rfl
@[irreducible] def prefix33 : Array (List ℕ) := prefix32 ++ recordedCaseTuplesChunk33
theorem prefix33_size : prefix33.size = 2176 := by
  rw [prefix33,Array.size_append,prefix32_size,chunk33_size]

theorem chunk34_size : recordedCaseTuplesChunk34.size = 8 := by rfl
@[irreducible] def prefix34 : Array (List ℕ) := prefix33 ++ recordedCaseTuplesChunk34
theorem prefix34_size : prefix34.size = 2184 := by
  rw [prefix34,Array.size_append,prefix33_size,chunk34_size]

end
end ElevenSquare.Pending.T03.CaseTable
