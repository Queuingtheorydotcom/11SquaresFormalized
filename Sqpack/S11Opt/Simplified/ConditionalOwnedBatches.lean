import Sqpack.S11Opt.Simplified.OwnedBatches
import Sqpack.S11Opt.Split.U2P.Branch

/-! The triangle checker also works under closed centre half-plane conditions.
Each earlier ownership batch is transported once to the current conditions,
instead of repeating that transport for every corner of every triangle. -/
namespace SquarePacking.S11Opt.Split.U2P

def BatchesOwnedC (S : ℝ) (J : List ℕ) (cs : List Cond)
    (bs : List OwnedBatch) : Prop :=
  ∀ b ∈ bs, ∀ p ∈ b.2, OwnedC S J cs b.1 p

theorem batchesOwnedC_nil (S : ℝ) (J : List ℕ) (cs : List Cond) :
    BatchesOwnedC S J cs [] := by
  intro b hb
  simp at hb

theorem batchesOwnedC_cons_mono {S : ℝ} {J : List ℕ}
    {cs oldCs : List Cond} {o : ℕ} {ps : List (ℕ × ℕ)}
    {bs : List OwnedBatch} (hp : ∀ p ∈ ps, OwnedC S J oldCs o p)
    (hsub : ∀ c ∈ oldCs, c ∈ cs) (hb : BatchesOwnedC S J cs bs) :
    BatchesOwnedC S J cs ((o, ps) :: bs) := by
  intro b h p hmem
  rcases List.mem_cons.mp h with rfl | h
  · exact (hp p hmem).mono hsub
  · exact hb b h p hmem

theorem trianglesValidC_sound {S : ℝ} {J : List ℕ} {cs : List Cond}
    {o : ℕ} {bs : List OwnedBatch} {ts : List Tri}
    (hb : BatchesOwnedC S J cs bs)
    (hc : trianglesValidB J o bs ts = true) :
    ∀ t ∈ ts, t.ValidC S J cs o := by
  intro t ht
  have h := List.all_eq_true.mp hc t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hJ, hne⟩, hback⟩, hok⟩ := h
  obtain ⟨b, hmem, hcorners⟩ := List.any_eq_true.mp hback
  have corners := of_decide_eq_true hcorners
  obtain ⟨heq, ha, hb', hc'⟩ := corners
  refine ⟨hJ, hne, ?_, ?_, ?_, hok⟩
  · rw [← heq]; exact hb b hmem _ ha
  · rw [← heq]; exact hb b hmem _ hb'
  · rw [← heq]; exact hb b hmem _ hc'

#print axioms trianglesValidC_sound
end SquarePacking.S11Opt.Split.U2P
