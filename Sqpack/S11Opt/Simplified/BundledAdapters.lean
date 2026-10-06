import Sqpack.S11Opt.FieldGen

/-! Shared adapters for the bundled field certificates. The geometric and finite
certificate premises are unchanged; only their repeated composition is shared. -/
namespace SquarePacking.S11Opt

/-- An option either satisfies every selected atom or contains an owned point. -/
theorem field_option_cases {Q : ℕ} {A : Set (ℝ × ℝ)}
    {atoms : List (List (List (ℕ × ℕ)))} {sets : List (List ℕ)}
    {used : List (ℕ × (ℕ × ℕ))}
    (h : ∃ o ∈ sets.map (fun S => S.flatMap (fun a => atoms.getD a [])) ++
      used.map (fun e => [[e.2]]), AtomSat Q A o) :
    (∃ S ∈ sets, ∀ a ∈ S, AtomSat Q A (atoms.getD a [])) ∨
      ∃ e ∈ used, ptQ Q e.2 ∈ A := by
  obtain ⟨o, ho, hg⟩ := h
  simp only [List.mem_append, List.mem_map] at ho
  rcases ho with ⟨S, hS, rfl⟩ | ⟨e, he, rfl⟩
  · exact Or.inl ⟨S, hS, fun a ha g hg' => hg g (List.mem_flatMap.mpr ⟨a, ha, hg'⟩)⟩
  · obtain ⟨p, hp, hm⟩ := hg _ (List.mem_singleton_self _)
    simp only [List.mem_singleton] at hp
    subst hp
    exact Or.inr ⟨e, he, hm⟩

/-- Compose the existing barycentric checker with majority capacity once. -/
theorem checked_maj_capacity {Q k : ℕ} {sites : List (ℕ × ℕ)}
    {subs : List (List ℕ)} {groups : List (List (ℕ × ℕ))}
    {barys : List (List (List ℕ))}
    (hb : baryAll sites subs groups barys = true)
    (hn : sites.length + 1 = 2 * k) (hc : SubsComplete sites.length k subs)
    {A B : Set (ℝ × ℝ)} (hAc : Convex ℝ A) (hAo : IsOpen A)
    (hBc : Convex ℝ B) (hBo : IsOpen B) (hAB : Disjoint A B)
    (hA : AtomSat Q A groups) (hB : AtomSat Q B groups) : False :=
  maj_capacity hn hc (baryAll_spec hb).1 (baryAll_spec hb).2
    hAc hAo hBc hBo hAB hA hB

end SquarePacking.S11Opt
