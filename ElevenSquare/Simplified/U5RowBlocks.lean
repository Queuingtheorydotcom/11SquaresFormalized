import ElevenSquare.Tasks.T07.Ext.Check

/-! Kernel computations for a geometric pruning step are bounded by row blocks.
The generic assembly theorem still proves the original `stepB` proposition. -/
namespace ElevenSquare.Simplified.U5RowBlocks
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext

def rowBlockB (s : PoseState) (i : Owner) (rs : List PoseRow)
    (pcov : ℕ → List (List PartnerPiece)) (certs : List (List Sub))
    (start width : ℕ) : Bool :=
  (List.range width).all fun k =>
    if start + k < (s.rows i).length then
      rowB s i rs pcov ((s.rows i).getD (start + k) ⟨0, 0, []⟩)
        (certs.getD (start + k) [])
    else true

theorem stepB_of_row_blocks {s : PoseState} {i : Owner} {rs : List PoseRow}
    {pcov : ℕ → List (List PartnerPiece)} {certs : List (List Sub)}
    {width blocks : ℕ} (hwidth : 0 < width)
    (hlen : certs.length = (s.rows i).length)
    (hcover : (s.rows i).length ≤ blocks * width)
    (hblocks : ∀ b < blocks, rowBlockB s i rs pcov certs (b * width) width = true) :
    stepB s i rs pcov certs = true := by
  apply stepB_of_rows hlen
  intro n hn
  have hb : n / width < blocks :=
    (Nat.div_lt_iff_lt_mul hwidth).mpr (lt_of_lt_of_le hn hcover)
  have h := hblocks (n / width) hb
  rw [rowBlockB, List.all_eq_true] at h
  have hrem := h (n % width) (List.mem_range.mpr (Nat.mod_lt n hwidth))
  have he : n / width * width + n % width = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n width
  simpa only [he, hn, ↓reduceIte] using hrem

end ElevenSquare.Simplified.U5RowBlocks
#print axioms ElevenSquare.Simplified.U5RowBlocks.stepB_of_row_blocks
