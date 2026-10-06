import Mathlib.Data.List.Basic

/-! Soundness of finite-domain propagation and branching. Concrete overlay data
and every refutation node must be checked separately. -/
namespace ElevenSquare.Pending.Propagation

abbrev Domains := List (ℕ × List ℕ)

-- Variables, values and target tuples are finite IDs. This predicate is purely finite.
def Witness (compatible supports : ℕ → ℕ → Bool) (D : Domains) (T : List ℕ)
    (f : ℕ → ℕ) (t : ℕ) : Prop :=
  t ∈ T ∧
  (∀ v options, (v, options) ∈ D → f v ∈ options ∧ supports t (f v) = true) ∧
  (∀ u left, (u, left) ∈ D → ∀ v right, (v, right) ∈ D → u ≠ v →
    compatible (f u) (f v) = true)

def Sat (compatible supports : ℕ → ℕ → Bool) (D : Domains) (T : List ℕ) : Prop :=
  ∃ f t, Witness compatible supports D T f t

theorem Witness.restrict {compatible supports : ℕ → ℕ → Bool}
    {D E : Domains} {T U : List ℕ} {f : ℕ → ℕ} {t : ℕ}
    (h : Witness compatible supports D T f t) (ht : t ∈ U)
    (he : ∀ v options, (v, options) ∈ E →
      ∃ old, (v, old) ∈ D ∧ f v ∈ options) :
    Witness compatible supports E U f t := by
  refine ⟨ht, ?_, ?_⟩
  · intro v options hv
    obtain ⟨old, hold, hmem⟩ := he v options hv
    exact ⟨hmem, (h.2.1 v old hold).2⟩
  · intro u left hu v right hv hne
    obtain ⟨left', hu', _⟩ := he u left hu
    obtain ⟨right', hv', _⟩ := he v right hv
    exact h.2.2 u left' hu' v right' hv' hne

def prune (supports : ℕ → ℕ → Bool) (D : Domains) (T : List ℕ) : Domains :=
  D.map (fun entry => (entry.1,
    entry.2.filter (fun r => T.any (fun t => supports t r))))

theorem Witness.prune {compatible supports : ℕ → ℕ → Bool}
    {D : Domains} {T : List ℕ} {f : ℕ → ℕ} {t : ℕ}
    (h : Witness compatible supports D T f t) :
    Witness compatible supports (prune supports D T) T f t := by
  apply h.restrict h.1
  intro v options hv
  obtain ⟨⟨u, old⟩, hu, he⟩ := List.mem_map.mp hv
  cases he
  refine ⟨old, hu, List.mem_filter.mpr ⟨(h.2.1 u old hu).1, ?_⟩⟩
  exact List.any_eq_true.mpr ⟨t, h.1, (h.2.1 u old hu).2⟩

def childTargets (supports : ℕ → ℕ → Bool) (T : List ℕ) (r : ℕ) : List ℕ :=
  T.filter (fun t => supports t r)

def childRaw (compatible : ℕ → ℕ → Bool) (D : Domains) (v r : ℕ) : Domains :=
  (D.filter (fun entry => decide (entry.1 ≠ v))).map
    (fun entry => (entry.1, entry.2.filter (fun s => compatible s r)))

def childDomains (compatible supports : ℕ → ℕ → Bool)
    (D : Domains) (T : List ℕ) (v r : ℕ) : Domains :=
  prune supports (childRaw compatible D v r) (childTargets supports T r)

theorem Witness.child {compatible supports : ℕ → ℕ → Bool}
    {D : Domains} {T : List ℕ} {f : ℕ → ℕ} {t v : ℕ} {options : List ℕ}
    (h : Witness compatible supports D T f t) (hv : (v, options) ∈ D) :
    Witness compatible supports (childDomains compatible supports D T v (f v))
      (childTargets supports T (f v)) f t := by
  apply Witness.prune
  apply h.restrict
  · exact List.mem_filter.mpr ⟨h.1, (h.2.1 v options hv).2⟩
  · intro u opts hu
    obtain ⟨⟨w, old⟩, hw, he⟩ := List.mem_map.mp hu
    cases he
    obtain ⟨hw, hne⟩ := List.mem_filter.mp hw
    have hne' : w ≠ v := of_decide_eq_true hne
    exact ⟨old, hw, List.mem_filter.mpr
      ⟨(h.2.1 w old hw).1, h.2.2 w old hw v options hv hne'⟩⟩

theorem refute_split (compatible supports : ℕ → ℕ → Bool)
    (D : Domains) (T : List ℕ) (v : ℕ) (options : List ℕ)
    (hv : (v, options) ∈ D)
    (children : ∀ r ∈ options,
      ¬ Sat compatible supports (childDomains compatible supports D T v r)
        (childTargets supports T r)) : ¬ Sat compatible supports D T := by
  rintro ⟨f, t, h⟩
  exact children (f v) (h.2.1 v options hv).1 ⟨f, t, h.child hv⟩

theorem refute_pruned (compatible supports : ℕ → ℕ → Bool) (D : Domains) (T : List ℕ)
    (h : ¬ Sat compatible supports (prune supports D T) T) :
    ¬ Sat compatible supports D T := by
  rintro ⟨f, t, hf⟩
  exact h ⟨f, t, hf.prune⟩

theorem refute_empty_domain (compatible supports : ℕ → ℕ → Bool)
    (D : Domains) (T : List ℕ) (v : ℕ) (hv : (v, []) ∈ D) :
    ¬ Sat compatible supports D T := by
  rintro ⟨f, t, h⟩
  exact List.not_mem_nil (h.2.1 v [] hv).1

theorem refute_no_targets (compatible supports : ℕ → ℕ → Bool) (D : Domains) :
    ¬ Sat compatible supports D [] := by
  rintro ⟨f, t, h⟩
  exact List.not_mem_nil h.1

end ElevenSquare.Pending.Propagation
#print axioms ElevenSquare.Pending.Propagation.refute_split
#print axioms ElevenSquare.Pending.Propagation.refute_pruned
#print axioms ElevenSquare.Pending.Propagation.refute_empty_domain
#print axioms ElevenSquare.Pending.Propagation.refute_no_targets
