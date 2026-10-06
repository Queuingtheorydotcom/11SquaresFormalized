import Sqpack.S11Opt.Simplified.ConditionalOwnedBatches
import Sqpack.S11Opt.Simplified.OwnedTrace

/-! Conditional ownership programs are interpreted by one induction. Every
promotion carries its original geometric coverage theorem; branch conditions
are part of the type, so a cover cannot be used under unrelated hypotheses. -/
namespace SquarePacking.S11Opt.Simplified.ConditionalOwnedTrace
open FieldTree SquarePacking.S11Opt.Split SquarePacking.S11Opt.Split.U2P

structure Promotion (cs : List Cond) where
  owner : ℕ
  triangles : List Tri
  targets : List (ℕ × ℕ)
  dependencies : List ℕ
  cover : CovF G.Q G.M G.R (hpsC owner ++ condsOf cs owner)
    (stepOpts triangles targets) 0 G.M 0 G.M 0 G.R

structure Terminal (cs : List Cond) where
  owner : ℕ
  triangles : List Tri
  dependencies : List ℕ
  cover : CovF G.Q G.M G.R (hpsC owner ++ condsOf cs owner)
    (triOpts triangles) 0 G.M 0 G.M 0 G.R

inductive Program : List Cond → Type
  | stop {cs : List Cond} (t : Terminal cs) : Program cs
  | promote {cs : List Cond} (p : Promotion cs) (next : Program cs) : Program cs
  | split {cs : List Cond} (o : ℕ) (A B C : ℤ)
      (left : Program ((o, (A, B, C)) :: cs))
      (right : Program ((o, (-A, -B, -C)) :: cs)) : Program cs

/-- Invalid indices contribute no batch, and therefore confer no ownership. -/
def select (bs : List OwnedBatch) (is : List ℕ) : List OwnedBatch :=
  is.filterMap (fun i => bs[i]?)

theorem select_owned {S : ℝ} {J : List ℕ} {cs : List Cond}
    {bs : List OwnedBatch} (hb : BatchesOwnedC S J cs bs) (is : List ℕ) :
    BatchesOwnedC S J cs (select bs is) := by
  intro b h
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp h
  exact hb b (List.mem_of_getElem? hi)

theorem transport_owned {S : ℝ} {J : List ℕ} {cs : List Cond}
    {bs : List OwnedBatch} (hb : BatchesOwnedC S J cs bs) (d : Cond) :
    BatchesOwnedC S J (d :: cs) bs := by
  intro b h p hp
  exact (hb b h p hp).mono (fun c hc => List.mem_cons_of_mem d hc)

def check (J : List ℕ) : {cs : List Cond} → List OwnedBatch → Program cs → Bool
  | _, bs, .stop t =>
    OwnedTrace.validB J (select bs t.dependencies) t.owner t.triangles
  | _, bs, .promote p next =>
    OwnedTrace.validB J (select bs p.dependencies) p.owner p.triangles &&
      check J ((p.owner, p.targets) :: bs) next
  | _, bs, .split _ _ _ _ left right =>
    check J bs left && check J bs right

/-- Promotions preserve strict ownership, and complementary closed half-planes
cover every center, including a center on the splitting line. -/
theorem check_sound {S : ℝ} (hS : S ≤ Ux) (hS0 : 0 ≤ S) {J : List ℕ} :
    {cs : List Cond} → (program : Program cs) → {bs : List OwnedBatch} →
    BatchesOwnedC S J cs bs → check J bs program = true → Excl S J cs
  | _, .stop t, _, hb, hc => by
    simp only [check, OwnedTrace.validB, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact excluded_of_trisC hS hS0 hc.1.1 hc.1.2
      (trianglesValidC_sound (select_owned hb t.dependencies) hc.2) t.cover
  | _, .promote p next, _, hb, hc => by
    simp only [check, Bool.and_eq_true] at hc
    have hv := hc.1
    simp only [OwnedTrace.validB, Bool.and_eq_true, decide_eq_true_eq] at hv
    have hp := owned_all_of_trisC hS hS0 hv.1.1 hv.1.2
      (trianglesValidC_sound (select_owned hb p.dependencies) hv.2) p.cover
    exact check_sound hS hS0 next
      (batchesOwnedC_cons_mono hp (fun _ h => h) hb) hc.2
  | _, .split o A B C left right, _, hb, hc => by
    simp only [check, Bool.and_eq_true] at hc
    exact split_excl o A B C
      (check_sound hS hS0 left (transport_owned hb _) hc.1)
      (check_sound hS hS0 right (transport_owned hb _) hc.2)

end SquarePacking.S11Opt.Simplified.ConditionalOwnedTrace
#print axioms SquarePacking.S11Opt.Simplified.ConditionalOwnedTrace.check_sound
