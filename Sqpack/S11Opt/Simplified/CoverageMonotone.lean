import Sqpack.S11Opt.FieldTree

/-! Reuse a geometric cover when the requested capture alternatives are weaker.
This includes arbitrary permutations and duplicate removal at all three finite
list levels, without assuming that geometric point lists have a fixed order. -/
namespace SquarePacking.S11Opt.FieldTree

abbrev CaptureOptions := List (List (List (ℕ × ℕ)))

def optionsWeakenB (strong weak : CaptureOptions) : Bool :=
  strong.all fun o => weak.any fun p =>
    p.all fun g => o.any fun f => f.all fun x => decide (x ∈ g)

theorem Good.weaken {Q : ℕ} {strong weak : CaptureOptions}
    (h : optionsWeakenB strong weak = true) {c : ℝ × ℝ} {θ : ℝ}
    (hc : Good Q strong c θ) : Good Q weak c θ := by
  obtain ⟨o, ho, hc⟩ := hc
  have hw := List.all_eq_true.mp h o ho
  obtain ⟨p, hp, hgroups⟩ := List.any_eq_true.mp hw
  refine ⟨p, hp, ?_⟩
  intro g hg
  obtain ⟨f, hf, hsub⟩ := List.any_eq_true.mp (List.all_eq_true.mp hgroups g hg)
  obtain ⟨x, hx, hin⟩ := hc f hf
  exact ⟨x, of_decide_eq_true (List.all_eq_true.mp hsub x hx), hin⟩

theorem CovF.weaken {Q M R : ℕ} {hps : List (ℤ × ℤ × ℤ)}
    {strong weak : CaptureOptions} {x0 x1 y0 y1 u0 u1 : ℕ}
    (hc : CovF Q M R hps strong x0 x1 y0 y1 u0 u1)
    (h : optionsWeakenB strong weak = true) :
    CovF Q M R hps weak x0 x1 y0 y1 u0 u1 := by
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin
  exact (hc c u hx0 hx1 hy0 hy1 hu0 hu1 hsub hin).weaken h

#print axioms CovF.weaken
end SquarePacking.S11Opt.FieldTree
