import ElevenSquare.Pending.S07_PropagationCore

/-! A small kernel-evaluated search replaces generated node transport proofs.
The Boolean checker has a fixed fuel bound; false or exhausted checks prove
nothing. Each successful split uses the original sound child-domain rule. -/
namespace ElevenSquare.Simplified.FiniteRefutation
open ElevenSquare.Pending.Propagation

def shortest : Domains → ℕ × List ℕ
  | [] => (0, [])
  | [entry] => entry
  | entry :: next :: rest =>
      let best := shortest (next :: rest)
      if entry.2.length ≤ best.2.length then entry else best

def check (compatible supports : ℕ → ℕ → Bool) : ℕ → Domains → List ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, D, T =>
      if T.isEmpty then true else
      let entry := shortest D
      decide (entry ∈ D) && entry.2.all (fun r =>
        check compatible supports fuel
          (childDomains compatible supports D T entry.1 r)
          (childTargets supports T r))

theorem sound (compatible supports : ℕ → ℕ → Bool)
    (fuel : ℕ) (D : Domains) (T : List ℕ)
    (h : check compatible supports fuel D T = true) :
    ¬ Sat compatible supports D T := by
  induction fuel generalizing D T with
  | zero => simp [check] at h
  | succ fuel ih =>
      simp only [check] at h
      split at h
      · have ht : T = [] := List.isEmpty_iff.mp ‹T.isEmpty = true›
        subst T
        exact refute_no_targets compatible supports D
      · simp only [Bool.and_eq_true] at h
        obtain ⟨hm, hc⟩ := h
        apply refute_split compatible supports D T (shortest D).1 (shortest D).2
          (of_decide_eq_true hm)
        intro r hr
        exact ih _ _ (List.all_eq_true.mp hc r hr)

end ElevenSquare.Simplified.FiniteRefutation

#print axioms ElevenSquare.Simplified.FiniteRefutation.sound
