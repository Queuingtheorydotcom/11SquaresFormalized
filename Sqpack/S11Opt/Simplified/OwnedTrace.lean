import Sqpack.S11Opt.Simplified.OwnedBatches

/-! A complete ownership trace is one induction over certified promotion data.
Each cover proof retains its original geometric meaning. Only the repeated
ownership bookkeeping is interpreted by a shared finite checker. -/
namespace SquarePacking.S11Opt.Simplified.OwnedTrace
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P

structure Promotion where
  owner : ℕ
  triangles : List Tri
  targets : List (ℕ × ℕ)
  cover : CovF G.Q G.M G.R (hpsC owner) (stepOpts triangles targets)
    0 G.M 0 G.M 0 G.R

structure Terminal where
  owner : ℕ
  triangles : List Tri
  cover : CovF G.Q G.M G.R (hpsC owner) (triOpts triangles)
    0 G.M 0 G.M 0 G.R

def validB (J : List ℕ) (bs : List OwnedBatch) (o : ℕ) (ts : List Tri) : Bool :=
  decide (o ∈ J ∧ o < 16) && trianglesValidB J o bs ts

def check (J : List ℕ) (terminal : Terminal) : List OwnedBatch → List Promotion → Bool
  | bs, [] => validB J bs terminal.owner terminal.triangles
  | bs, p :: ps => validB J bs p.owner p.triangles &&
      check J terminal ((p.owner, p.targets) :: bs) ps

/-- The exact cover certificates plus a finite dependency check exclude a case.
No intermediate owned-point theorem needs to be generated for each stage. -/
theorem check_sound {S : ℝ} (hS : S ≤ Ux) (hS0 : 0 ≤ S)
    {J : List ℕ} (terminal : Terminal) (program : List Promotion)
    {bs : List OwnedBatch} (hb : BatchesOwned S J bs)
    (hc : check J terminal bs program = true) : ¬ RealizesIn S J := by
  induction program generalizing bs with
  | nil =>
      simp only [check, validB, Bool.and_eq_true, decide_eq_true_eq] at hc
      exact excluded_of_tris hS hS0 hc.1.1 hc.1.2
        (trianglesValidB_sound hb hc.2) terminal.cover
  | cons p ps ih =>
      simp only [check, Bool.and_eq_true] at hc
      have hv := hc.1
      simp only [validB, Bool.and_eq_true, decide_eq_true_eq] at hv
      have hp : ∀ q ∈ p.targets, Owned S J p.owner q :=
        owned_all_of_tris hS hS0 hv.1.1 hv.1.2
          (trianglesValidB_sound hb hv.2) p.cover
      exact ih (batchesOwned_cons hp hb) hc.2

end SquarePacking.S11Opt.Simplified.OwnedTrace
#print axioms SquarePacking.S11Opt.Simplified.OwnedTrace.check_sound
