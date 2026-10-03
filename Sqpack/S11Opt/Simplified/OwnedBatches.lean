import Sqpack.S11Opt.Split.U2P.Rules

/-! A single finite ownership check replaces one proof branch per triangle.
The certificate records previously established batches of owned points. The
checker verifies all three corners against those batches; triangle convexity
and strict ownership retain exactly their existing meanings. -/
namespace SquarePacking.S11Opt.Split.U2P

abbrev OwnedBatch := ℕ × List (ℕ × ℕ)

def BatchesOwned (S : ℝ) (J : List ℕ) (bs : List OwnedBatch) : Prop :=
  ∀ b ∈ bs, ∀ p ∈ b.2, Owned S J b.1 p

theorem batchesOwned_nil (S : ℝ) (J : List ℕ) : BatchesOwned S J [] := by
  intro b hb
  simp at hb

theorem batchesOwned_cons {S : ℝ} {J : List ℕ} {o : ℕ}
    {ps : List (ℕ × ℕ)} {bs : List OwnedBatch}
    (hp : ∀ p ∈ ps, Owned S J o p) (hb : BatchesOwned S J bs) :
    BatchesOwned S J ((o, ps) :: bs) := by
  intro b h p hmem
  rcases List.mem_cons.mp h with rfl | h
  · exact hp p hmem
  · exact hb b h p hmem

def Tri.backedB (bs : List OwnedBatch) (t : Tri) : Bool :=
  bs.any fun b => decide
    (b.1 = t.1 ∧ t.2.1 ∈ b.2 ∧ t.2.2.1 ∈ b.2 ∧ t.2.2.2.1 ∈ b.2)

def trianglesValidB (J : List ℕ) (o : ℕ) (bs : List OwnedBatch)
    (ts : List Tri) : Bool :=
  ts.all fun t => decide (t.1 ∈ J ∧ t.1 ≠ o) && t.backedB bs && t.ok

theorem trianglesValidB_sound {S : ℝ} {J : List ℕ} {o : ℕ}
    {bs : List OwnedBatch} {ts : List Tri} (hb : BatchesOwned S J bs)
    (hc : trianglesValidB J o bs ts = true) :
    ∀ t ∈ ts, t.Valid S J o := by
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

#print axioms trianglesValidB_sound
end SquarePacking.S11Opt.Split.U2P
