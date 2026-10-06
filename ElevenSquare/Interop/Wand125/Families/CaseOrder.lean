import ElevenSquare.Pending.S06_Data
import Sqpack.S11Opt.Split.Interface

/-!
# Case order: recorded case tuples against wand125's `authorMasks`

One kernel check per 64-row chunk; checking the concatenated array at once is
much more expensive in the kernel.
-/

namespace ElevenSquare.Interop.Wand125.CaseOrder
open ElevenSquare.Pending
open SquarePacking.S11Opt.Split

set_option maxRecDepth 100000

theorem chunk0 : recordedCaseTuplesChunk0.toList = (authorMasks.drop 0).take 64 := by decide +kernel

theorem chunk1 : recordedCaseTuplesChunk1.toList = (authorMasks.drop 64).take 64 := by decide +kernel

theorem chunk2 : recordedCaseTuplesChunk2.toList = (authorMasks.drop 128).take 64 := by decide +kernel

theorem chunk3 : recordedCaseTuplesChunk3.toList = (authorMasks.drop 192).take 64 := by decide +kernel

theorem chunk4 : recordedCaseTuplesChunk4.toList = (authorMasks.drop 256).take 64 := by decide +kernel

theorem chunk5 : recordedCaseTuplesChunk5.toList = (authorMasks.drop 320).take 64 := by decide +kernel

theorem chunk6 : recordedCaseTuplesChunk6.toList = (authorMasks.drop 384).take 64 := by decide +kernel

theorem chunk7 : recordedCaseTuplesChunk7.toList = (authorMasks.drop 448).take 64 := by decide +kernel

theorem chunk8 : recordedCaseTuplesChunk8.toList = (authorMasks.drop 512).take 64 := by decide +kernel

theorem chunk9 : recordedCaseTuplesChunk9.toList = (authorMasks.drop 576).take 64 := by decide +kernel

theorem chunk10 : recordedCaseTuplesChunk10.toList = (authorMasks.drop 640).take 64 := by decide +kernel

theorem chunk11 : recordedCaseTuplesChunk11.toList = (authorMasks.drop 704).take 64 := by decide +kernel

theorem chunk12 : recordedCaseTuplesChunk12.toList = (authorMasks.drop 768).take 64 := by decide +kernel

theorem chunk13 : recordedCaseTuplesChunk13.toList = (authorMasks.drop 832).take 64 := by decide +kernel

theorem chunk14 : recordedCaseTuplesChunk14.toList = (authorMasks.drop 896).take 64 := by decide +kernel

theorem chunk15 : recordedCaseTuplesChunk15.toList = (authorMasks.drop 960).take 64 := by decide +kernel

theorem chunk16 : recordedCaseTuplesChunk16.toList = (authorMasks.drop 1024).take 64 := by decide +kernel

theorem chunk17 : recordedCaseTuplesChunk17.toList = (authorMasks.drop 1088).take 64 := by decide +kernel

theorem chunk18 : recordedCaseTuplesChunk18.toList = (authorMasks.drop 1152).take 64 := by decide +kernel

theorem chunk19 : recordedCaseTuplesChunk19.toList = (authorMasks.drop 1216).take 64 := by decide +kernel

theorem chunk20 : recordedCaseTuplesChunk20.toList = (authorMasks.drop 1280).take 64 := by decide +kernel

theorem chunk21 : recordedCaseTuplesChunk21.toList = (authorMasks.drop 1344).take 64 := by decide +kernel

theorem chunk22 : recordedCaseTuplesChunk22.toList = (authorMasks.drop 1408).take 64 := by decide +kernel

theorem chunk23 : recordedCaseTuplesChunk23.toList = (authorMasks.drop 1472).take 64 := by decide +kernel

theorem chunk24 : recordedCaseTuplesChunk24.toList = (authorMasks.drop 1536).take 64 := by decide +kernel

theorem chunk25 : recordedCaseTuplesChunk25.toList = (authorMasks.drop 1600).take 64 := by decide +kernel

theorem chunk26 : recordedCaseTuplesChunk26.toList = (authorMasks.drop 1664).take 64 := by decide +kernel

theorem chunk27 : recordedCaseTuplesChunk27.toList = (authorMasks.drop 1728).take 64 := by decide +kernel

theorem chunk28 : recordedCaseTuplesChunk28.toList = (authorMasks.drop 1792).take 64 := by decide +kernel

theorem chunk29 : recordedCaseTuplesChunk29.toList = (authorMasks.drop 1856).take 64 := by decide +kernel

theorem chunk30 : recordedCaseTuplesChunk30.toList = (authorMasks.drop 1920).take 64 := by decide +kernel

theorem chunk31 : recordedCaseTuplesChunk31.toList = (authorMasks.drop 1984).take 64 := by decide +kernel

theorem chunk32 : recordedCaseTuplesChunk32.toList = (authorMasks.drop 2048).take 64 := by decide +kernel

theorem chunk33 : recordedCaseTuplesChunk33.toList = (authorMasks.drop 2112).take 64 := by decide +kernel

theorem chunk34 : recordedCaseTuplesChunk34.toList = authorMasks.drop 2176 := by decide +kernel

theorem block {α : Type} (l : List α) (a n b : ℕ) (h : a + n = b) :
    (l.drop a).take n ++ l.drop b = l.drop a := by
  subst h
  conv_rhs => rw [← List.take_append_drop n (l.drop a)]
  rw [List.drop_drop]

theorem tuples_eq_authorMasks : recordedCaseTuples.toList = authorMasks := by
  simp only [recordedCaseTuples, Array.toList_append, List.append_assoc]
  rw [chunk0, chunk1, chunk2, chunk3, chunk4, chunk5, chunk6, chunk7, chunk8, chunk9, chunk10, chunk11, chunk12, chunk13, chunk14, chunk15, chunk16, chunk17, chunk18, chunk19, chunk20, chunk21, chunk22, chunk23, chunk24, chunk25, chunk26, chunk27, chunk28, chunk29, chunk30, chunk31, chunk32, chunk33, chunk34]
  rw [block authorMasks 2112 64 2176 rfl]
  rw [block authorMasks 2048 64 2112 rfl]
  rw [block authorMasks 1984 64 2048 rfl]
  rw [block authorMasks 1920 64 1984 rfl]
  rw [block authorMasks 1856 64 1920 rfl]
  rw [block authorMasks 1792 64 1856 rfl]
  rw [block authorMasks 1728 64 1792 rfl]
  rw [block authorMasks 1664 64 1728 rfl]
  rw [block authorMasks 1600 64 1664 rfl]
  rw [block authorMasks 1536 64 1600 rfl]
  rw [block authorMasks 1472 64 1536 rfl]
  rw [block authorMasks 1408 64 1472 rfl]
  rw [block authorMasks 1344 64 1408 rfl]
  rw [block authorMasks 1280 64 1344 rfl]
  rw [block authorMasks 1216 64 1280 rfl]
  rw [block authorMasks 1152 64 1216 rfl]
  rw [block authorMasks 1088 64 1152 rfl]
  rw [block authorMasks 1024 64 1088 rfl]
  rw [block authorMasks 960 64 1024 rfl]
  rw [block authorMasks 896 64 960 rfl]
  rw [block authorMasks 832 64 896 rfl]
  rw [block authorMasks 768 64 832 rfl]
  rw [block authorMasks 704 64 768 rfl]
  rw [block authorMasks 640 64 704 rfl]
  rw [block authorMasks 576 64 640 rfl]
  rw [block authorMasks 512 64 576 rfl]
  rw [block authorMasks 448 64 512 rfl]
  rw [block authorMasks 384 64 448 rfl]
  rw [block authorMasks 320 64 384 rfl]
  rw [block authorMasks 256 64 320 rfl]
  rw [block authorMasks 192 64 256 rfl]
  rw [block authorMasks 128 64 192 rfl]
  rw [block authorMasks 64 64 128 rfl]
  rw [block authorMasks 0 64 64 rfl]
  simp

end ElevenSquare.Interop.Wand125.CaseOrder

#print axioms ElevenSquare.Interop.Wand125.CaseOrder.tuples_eq_authorMasks
