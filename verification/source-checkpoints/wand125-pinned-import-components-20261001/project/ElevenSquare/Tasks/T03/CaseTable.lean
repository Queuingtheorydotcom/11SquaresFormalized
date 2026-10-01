import ElevenSquare.Tasks.T03.CaseTablePrefixes

namespace ElevenSquare.Pending.T03.CaseTable
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem table_eq_prefix : recordedCaseTuples = prefix34 := by
  unfold recordedCaseTuples prefix34 prefix33 prefix32 prefix31 prefix30 prefix29 prefix28 prefix27 prefix26 prefix25 prefix24 prefix23 prefix22 prefix21 prefix20 prefix19 prefix18 prefix17 prefix16 prefix15 prefix14 prefix13 prefix12 prefix11 prefix10 prefix09 prefix08 prefix07 prefix06 prefix05 prefix04 prefix03 prefix02 prefix01 prefix00
  rfl

theorem slice00 (k : ℕ) (h0 : 0 ≤ k) (h1 : k < 64) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk0[k-0]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_left _ _ k (by rw [prefix11_size]; omega)]
  rw [prefix11,get_append_left _ _ k (by rw [prefix10_size]; omega)]
  rw [prefix10,get_append_left _ _ k (by rw [prefix09_size]; omega)]
  rw [prefix09,get_append_left _ _ k (by rw [prefix08_size]; omega)]
  rw [prefix08,get_append_left _ _ k (by rw [prefix07_size]; omega)]
  rw [prefix07,get_append_left _ _ k (by rw [prefix06_size]; omega)]
  rw [prefix06,get_append_left _ _ k (by rw [prefix05_size]; omega)]
  rw [prefix05,get_append_left _ _ k (by rw [prefix04_size]; omega)]
  rw [prefix04,get_append_left _ _ k (by rw [prefix03_size]; omega)]
  rw [prefix03,get_append_left _ _ k (by rw [prefix02_size]; omega)]
  rw [prefix02,get_append_left _ _ k (by rw [prefix01_size]; omega)]
  rw [prefix01,get_append_left _ _ k (by rw [prefix00_size]; omega)]
  exact congrArg (fun a : Array (List ℕ) => a[k]!)
    (show prefix00 = recordedCaseTuplesChunk0 from by delta prefix00 <;> rfl)

theorem slice01 (k : ℕ) (h0 : 64 ≤ k) (h1 : k < 128) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk1[k-64]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_left _ _ k (by rw [prefix11_size]; omega)]
  rw [prefix11,get_append_left _ _ k (by rw [prefix10_size]; omega)]
  rw [prefix10,get_append_left _ _ k (by rw [prefix09_size]; omega)]
  rw [prefix09,get_append_left _ _ k (by rw [prefix08_size]; omega)]
  rw [prefix08,get_append_left _ _ k (by rw [prefix07_size]; omega)]
  rw [prefix07,get_append_left _ _ k (by rw [prefix06_size]; omega)]
  rw [prefix06,get_append_left _ _ k (by rw [prefix05_size]; omega)]
  rw [prefix05,get_append_left _ _ k (by rw [prefix04_size]; omega)]
  rw [prefix04,get_append_left _ _ k (by rw [prefix03_size]; omega)]
  rw [prefix03,get_append_left _ _ k (by rw [prefix02_size]; omega)]
  rw [prefix02,get_append_left _ _ k (by rw [prefix01_size]; omega)]
  rw [prefix01,get_append_right _ _ k
    (by rwa [prefix00_size])
    (by rw [prefix00_size,chunk01_size]; exact h1),prefix00_size]

theorem slice02 (k : ℕ) (h0 : 128 ≤ k) (h1 : k < 192) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk2[k-128]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_left _ _ k (by rw [prefix11_size]; omega)]
  rw [prefix11,get_append_left _ _ k (by rw [prefix10_size]; omega)]
  rw [prefix10,get_append_left _ _ k (by rw [prefix09_size]; omega)]
  rw [prefix09,get_append_left _ _ k (by rw [prefix08_size]; omega)]
  rw [prefix08,get_append_left _ _ k (by rw [prefix07_size]; omega)]
  rw [prefix07,get_append_left _ _ k (by rw [prefix06_size]; omega)]
  rw [prefix06,get_append_left _ _ k (by rw [prefix05_size]; omega)]
  rw [prefix05,get_append_left _ _ k (by rw [prefix04_size]; omega)]
  rw [prefix04,get_append_left _ _ k (by rw [prefix03_size]; omega)]
  rw [prefix03,get_append_left _ _ k (by rw [prefix02_size]; omega)]
  rw [prefix02,get_append_right _ _ k
    (by rwa [prefix01_size])
    (by rw [prefix01_size,chunk02_size]; exact h1),prefix01_size]

theorem slice03 (k : ℕ) (h0 : 192 ≤ k) (h1 : k < 256) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk3[k-192]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_left _ _ k (by rw [prefix11_size]; omega)]
  rw [prefix11,get_append_left _ _ k (by rw [prefix10_size]; omega)]
  rw [prefix10,get_append_left _ _ k (by rw [prefix09_size]; omega)]
  rw [prefix09,get_append_left _ _ k (by rw [prefix08_size]; omega)]
  rw [prefix08,get_append_left _ _ k (by rw [prefix07_size]; omega)]
  rw [prefix07,get_append_left _ _ k (by rw [prefix06_size]; omega)]
  rw [prefix06,get_append_left _ _ k (by rw [prefix05_size]; omega)]
  rw [prefix05,get_append_left _ _ k (by rw [prefix04_size]; omega)]
  rw [prefix04,get_append_left _ _ k (by rw [prefix03_size]; omega)]
  rw [prefix03,get_append_right _ _ k
    (by rwa [prefix02_size])
    (by rw [prefix02_size,chunk03_size]; exact h1),prefix02_size]

theorem slice04 (k : ℕ) (h0 : 256 ≤ k) (h1 : k < 320) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk4[k-256]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_left _ _ k (by rw [prefix11_size]; omega)]
  rw [prefix11,get_append_left _ _ k (by rw [prefix10_size]; omega)]
  rw [prefix10,get_append_left _ _ k (by rw [prefix09_size]; omega)]
  rw [prefix09,get_append_left _ _ k (by rw [prefix08_size]; omega)]
  rw [prefix08,get_append_left _ _ k (by rw [prefix07_size]; omega)]
  rw [prefix07,get_append_left _ _ k (by rw [prefix06_size]; omega)]
  rw [prefix06,get_append_left _ _ k (by rw [prefix05_size]; omega)]
  rw [prefix05,get_append_left _ _ k (by rw [prefix04_size]; omega)]
  rw [prefix04,get_append_right _ _ k
    (by rwa [prefix03_size])
    (by rw [prefix03_size,chunk04_size]; exact h1),prefix03_size]

theorem slice05 (k : ℕ) (h0 : 320 ≤ k) (h1 : k < 384) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk5[k-320]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_left _ _ k (by rw [prefix11_size]; omega)]
  rw [prefix11,get_append_left _ _ k (by rw [prefix10_size]; omega)]
  rw [prefix10,get_append_left _ _ k (by rw [prefix09_size]; omega)]
  rw [prefix09,get_append_left _ _ k (by rw [prefix08_size]; omega)]
  rw [prefix08,get_append_left _ _ k (by rw [prefix07_size]; omega)]
  rw [prefix07,get_append_left _ _ k (by rw [prefix06_size]; omega)]
  rw [prefix06,get_append_left _ _ k (by rw [prefix05_size]; omega)]
  rw [prefix05,get_append_right _ _ k
    (by rwa [prefix04_size])
    (by rw [prefix04_size,chunk05_size]; exact h1),prefix04_size]

theorem slice06 (k : ℕ) (h0 : 384 ≤ k) (h1 : k < 448) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk6[k-384]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_left _ _ k (by rw [prefix11_size]; omega)]
  rw [prefix11,get_append_left _ _ k (by rw [prefix10_size]; omega)]
  rw [prefix10,get_append_left _ _ k (by rw [prefix09_size]; omega)]
  rw [prefix09,get_append_left _ _ k (by rw [prefix08_size]; omega)]
  rw [prefix08,get_append_left _ _ k (by rw [prefix07_size]; omega)]
  rw [prefix07,get_append_left _ _ k (by rw [prefix06_size]; omega)]
  rw [prefix06,get_append_right _ _ k
    (by rwa [prefix05_size])
    (by rw [prefix05_size,chunk06_size]; exact h1),prefix05_size]

theorem slice07 (k : ℕ) (h0 : 448 ≤ k) (h1 : k < 512) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk7[k-448]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_left _ _ k (by rw [prefix11_size]; omega)]
  rw [prefix11,get_append_left _ _ k (by rw [prefix10_size]; omega)]
  rw [prefix10,get_append_left _ _ k (by rw [prefix09_size]; omega)]
  rw [prefix09,get_append_left _ _ k (by rw [prefix08_size]; omega)]
  rw [prefix08,get_append_left _ _ k (by rw [prefix07_size]; omega)]
  rw [prefix07,get_append_right _ _ k
    (by rwa [prefix06_size])
    (by rw [prefix06_size,chunk07_size]; exact h1),prefix06_size]

theorem slice08 (k : ℕ) (h0 : 512 ≤ k) (h1 : k < 576) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk8[k-512]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_left _ _ k (by rw [prefix11_size]; omega)]
  rw [prefix11,get_append_left _ _ k (by rw [prefix10_size]; omega)]
  rw [prefix10,get_append_left _ _ k (by rw [prefix09_size]; omega)]
  rw [prefix09,get_append_left _ _ k (by rw [prefix08_size]; omega)]
  rw [prefix08,get_append_right _ _ k
    (by rwa [prefix07_size])
    (by rw [prefix07_size,chunk08_size]; exact h1),prefix07_size]

theorem slice09 (k : ℕ) (h0 : 576 ≤ k) (h1 : k < 640) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk9[k-576]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_left _ _ k (by rw [prefix11_size]; omega)]
  rw [prefix11,get_append_left _ _ k (by rw [prefix10_size]; omega)]
  rw [prefix10,get_append_left _ _ k (by rw [prefix09_size]; omega)]
  rw [prefix09,get_append_right _ _ k
    (by rwa [prefix08_size])
    (by rw [prefix08_size,chunk09_size]; exact h1),prefix08_size]

theorem slice10 (k : ℕ) (h0 : 640 ≤ k) (h1 : k < 704) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk10[k-640]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_left _ _ k (by rw [prefix11_size]; omega)]
  rw [prefix11,get_append_left _ _ k (by rw [prefix10_size]; omega)]
  rw [prefix10,get_append_right _ _ k
    (by rwa [prefix09_size])
    (by rw [prefix09_size,chunk10_size]; exact h1),prefix09_size]

theorem slice11 (k : ℕ) (h0 : 704 ≤ k) (h1 : k < 768) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk11[k-704]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_left _ _ k (by rw [prefix11_size]; omega)]
  rw [prefix11,get_append_right _ _ k
    (by rwa [prefix10_size])
    (by rw [prefix10_size,chunk11_size]; exact h1),prefix10_size]

theorem slice12 (k : ℕ) (h0 : 768 ≤ k) (h1 : k < 832) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk12[k-768]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_left _ _ k (by rw [prefix12_size]; omega)]
  rw [prefix12,get_append_right _ _ k
    (by rwa [prefix11_size])
    (by rw [prefix11_size,chunk12_size]; exact h1),prefix11_size]

theorem slice13 (k : ℕ) (h0 : 832 ≤ k) (h1 : k < 896) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk13[k-832]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_left _ _ k (by rw [prefix13_size]; omega)]
  rw [prefix13,get_append_right _ _ k
    (by rwa [prefix12_size])
    (by rw [prefix12_size,chunk13_size]; exact h1),prefix12_size]

theorem slice14 (k : ℕ) (h0 : 896 ≤ k) (h1 : k < 960) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk14[k-896]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_left _ _ k (by rw [prefix14_size]; omega)]
  rw [prefix14,get_append_right _ _ k
    (by rwa [prefix13_size])
    (by rw [prefix13_size,chunk14_size]; exact h1),prefix13_size]

theorem slice15 (k : ℕ) (h0 : 960 ≤ k) (h1 : k < 1024) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk15[k-960]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_left _ _ k (by rw [prefix15_size]; omega)]
  rw [prefix15,get_append_right _ _ k
    (by rwa [prefix14_size])
    (by rw [prefix14_size,chunk15_size]; exact h1),prefix14_size]

theorem slice16 (k : ℕ) (h0 : 1024 ≤ k) (h1 : k < 1088) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk16[k-1024]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_left _ _ k (by rw [prefix16_size]; omega)]
  rw [prefix16,get_append_right _ _ k
    (by rwa [prefix15_size])
    (by rw [prefix15_size,chunk16_size]; exact h1),prefix15_size]

theorem slice17 (k : ℕ) (h0 : 1088 ≤ k) (h1 : k < 1152) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk17[k-1088]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_left _ _ k (by rw [prefix17_size]; omega)]
  rw [prefix17,get_append_right _ _ k
    (by rwa [prefix16_size])
    (by rw [prefix16_size,chunk17_size]; exact h1),prefix16_size]

theorem slice18 (k : ℕ) (h0 : 1152 ≤ k) (h1 : k < 1216) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk18[k-1152]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_left _ _ k (by rw [prefix18_size]; omega)]
  rw [prefix18,get_append_right _ _ k
    (by rwa [prefix17_size])
    (by rw [prefix17_size,chunk18_size]; exact h1),prefix17_size]

theorem slice19 (k : ℕ) (h0 : 1216 ≤ k) (h1 : k < 1280) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk19[k-1216]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_left _ _ k (by rw [prefix19_size]; omega)]
  rw [prefix19,get_append_right _ _ k
    (by rwa [prefix18_size])
    (by rw [prefix18_size,chunk19_size]; exact h1),prefix18_size]

theorem slice20 (k : ℕ) (h0 : 1280 ≤ k) (h1 : k < 1344) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk20[k-1280]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_left _ _ k (by rw [prefix20_size]; omega)]
  rw [prefix20,get_append_right _ _ k
    (by rwa [prefix19_size])
    (by rw [prefix19_size,chunk20_size]; exact h1),prefix19_size]

theorem slice21 (k : ℕ) (h0 : 1344 ≤ k) (h1 : k < 1408) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk21[k-1344]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_left _ _ k (by rw [prefix21_size]; omega)]
  rw [prefix21,get_append_right _ _ k
    (by rwa [prefix20_size])
    (by rw [prefix20_size,chunk21_size]; exact h1),prefix20_size]

theorem slice22 (k : ℕ) (h0 : 1408 ≤ k) (h1 : k < 1472) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk22[k-1408]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_left _ _ k (by rw [prefix22_size]; omega)]
  rw [prefix22,get_append_right _ _ k
    (by rwa [prefix21_size])
    (by rw [prefix21_size,chunk22_size]; exact h1),prefix21_size]

theorem slice23 (k : ℕ) (h0 : 1472 ≤ k) (h1 : k < 1536) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk23[k-1472]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_left _ _ k (by rw [prefix23_size]; omega)]
  rw [prefix23,get_append_right _ _ k
    (by rwa [prefix22_size])
    (by rw [prefix22_size,chunk23_size]; exact h1),prefix22_size]

theorem slice24 (k : ℕ) (h0 : 1536 ≤ k) (h1 : k < 1600) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk24[k-1536]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_left _ _ k (by rw [prefix24_size]; omega)]
  rw [prefix24,get_append_right _ _ k
    (by rwa [prefix23_size])
    (by rw [prefix23_size,chunk24_size]; exact h1),prefix23_size]

theorem slice25 (k : ℕ) (h0 : 1600 ≤ k) (h1 : k < 1664) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk25[k-1600]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_left _ _ k (by rw [prefix25_size]; omega)]
  rw [prefix25,get_append_right _ _ k
    (by rwa [prefix24_size])
    (by rw [prefix24_size,chunk25_size]; exact h1),prefix24_size]

theorem slice26 (k : ℕ) (h0 : 1664 ≤ k) (h1 : k < 1728) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk26[k-1664]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_left _ _ k (by rw [prefix26_size]; omega)]
  rw [prefix26,get_append_right _ _ k
    (by rwa [prefix25_size])
    (by rw [prefix25_size,chunk26_size]; exact h1),prefix25_size]

theorem slice27 (k : ℕ) (h0 : 1728 ≤ k) (h1 : k < 1792) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk27[k-1728]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_left _ _ k (by rw [prefix27_size]; omega)]
  rw [prefix27,get_append_right _ _ k
    (by rwa [prefix26_size])
    (by rw [prefix26_size,chunk27_size]; exact h1),prefix26_size]

theorem slice28 (k : ℕ) (h0 : 1792 ≤ k) (h1 : k < 1856) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk28[k-1792]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_left _ _ k (by rw [prefix28_size]; omega)]
  rw [prefix28,get_append_right _ _ k
    (by rwa [prefix27_size])
    (by rw [prefix27_size,chunk28_size]; exact h1),prefix27_size]

theorem slice29 (k : ℕ) (h0 : 1856 ≤ k) (h1 : k < 1920) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk29[k-1856]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_left _ _ k (by rw [prefix29_size]; omega)]
  rw [prefix29,get_append_right _ _ k
    (by rwa [prefix28_size])
    (by rw [prefix28_size,chunk29_size]; exact h1),prefix28_size]

theorem slice30 (k : ℕ) (h0 : 1920 ≤ k) (h1 : k < 1984) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk30[k-1920]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_left _ _ k (by rw [prefix30_size]; omega)]
  rw [prefix30,get_append_right _ _ k
    (by rwa [prefix29_size])
    (by rw [prefix29_size,chunk30_size]; exact h1),prefix29_size]

theorem slice31 (k : ℕ) (h0 : 1984 ≤ k) (h1 : k < 2048) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk31[k-1984]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_left _ _ k (by rw [prefix31_size]; omega)]
  rw [prefix31,get_append_right _ _ k
    (by rwa [prefix30_size])
    (by rw [prefix30_size,chunk31_size]; exact h1),prefix30_size]

theorem slice32 (k : ℕ) (h0 : 2048 ≤ k) (h1 : k < 2112) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk32[k-2048]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_left _ _ k (by rw [prefix32_size]; omega)]
  rw [prefix32,get_append_right _ _ k
    (by rwa [prefix31_size])
    (by rw [prefix31_size,chunk32_size]; exact h1),prefix31_size]

theorem slice33 (k : ℕ) (h0 : 2112 ≤ k) (h1 : k < 2176) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk33[k-2112]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_left _ _ k (by rw [prefix33_size]; omega)]
  rw [prefix33,get_append_right _ _ k
    (by rwa [prefix32_size])
    (by rw [prefix32_size,chunk33_size]; exact h1),prefix32_size]

theorem slice34 (k : ℕ) (h0 : 2176 ≤ k) (h1 : k < 2184) :
    recordedCaseTuples[k]! = recordedCaseTuplesChunk34[k-2176]! := by
  rw [table_eq_prefix]
  rw [prefix34,get_append_right _ _ k
    (by rwa [prefix33_size])
    (by rw [prefix33_size,chunk34_size]; exact h1),prefix33_size]

end
end ElevenSquare.Pending.T03.CaseTable
