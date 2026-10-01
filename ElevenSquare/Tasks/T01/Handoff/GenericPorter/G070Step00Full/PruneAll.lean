import ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full.Source
import ElevenSquare.Tasks.T01.FinitePruning

namespace ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full
open ElevenSquare.Pending ElevenSquare.Tasks.T01
open ElevenSquare.Tasks.T01.Handoff.SharedGenericRoots
noncomputable section

/-- The six fixed facets provide a compact source for each unchanged angle
interval. The checked source implication is independent of its wall margin. -/
def sourceRow (k : Fin 32) : PoseRow :=
  {slabRow 32 (5 : Fin 16) k with centers := sourceLiteral}

theorem source_row_contains (k : Fin 32) (q : UnitSquare)
    (hq : (slabRow 32 (5 : Fin 16) k).contains q) :
    (sourceRow k).contains q := by
  obtain ⟨hc, t, ht0, ht1, hlo, hhi, ha⟩ := hq
  exact ⟨literal_contains_of_root_row k q.center hc,
    t, ht0, ht1, hlo, hhi, ha⟩

def outputRows (cert : Fin 32 → RowPruningCertificate) : List PoseRow :=
  (List.finRange 32).flatMap (fun k => (cert k).keptRows (sourceRow k))

theorem output_rows_eq_kept_rows
    (cert : Fin 32 → RowPruningCertificate) (kept : Fin 32 → PoseRow)
    (hkept : ∀ k, (cert k).keptRows (sourceRow k) = [kept k]) :
    outputRows cert = (List.finRange 32).map kept := by
  have hbind (ks : List (Fin 32)) :
      ks.flatMap (fun k => (cert k).keptRows (sourceRow k)) =
        ks.map kept := by
    induction ks with
    | nil => rfl
    | cons k tail ih =>
      simp only [List.flatMap_cons, List.map_cons, hkept k,
        List.singleton_append, ih]
  exact hbind (List.finRange 32)

/-- A family of 32 exact row certificates prunes the actual initial owner
without replacing its root by an assumed archived polygon. -/
theorem prune_all (s : PoseState)
    (cert : Fin 32 → RowPruningCertificate)
    (hrows : s.rows (3 : Owner) = slabRows 32 (5 : Fin 16))
    (hcheck : ∀ k, (cert k).Check s (3 : Owner) (sourceRow k)) :
    VerifiedStep s (replaceRows s (3 : Owner) (outputRows cert)) := by
  apply VerifiedStep.prunePosewise
  intro q hq
  obtain ⟨r, hr, hcontains⟩ := hq
  rw [hrows] at hr
  unfold slabRows at hr
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
  rcases row_pruning_sound s (3 : Owner) (sourceRow k) (cert k)
      (hcheck k) q (source_row_contains k q hcontains) with hkeep | hbad
  · left
    obtain ⟨out, hout, hcontains'⟩ := hkeep
    exact ⟨out, List.mem_flatMap.mpr ⟨k, hk, hout⟩, hcontains'⟩
  · exact Or.inr hbad

#print axioms prune_all
#print axioms output_rows_eq_kept_rows

end
end ElevenSquare.Tasks.T01.Handoff.GenericPorter.G070Step00Full
