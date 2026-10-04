import Sqpack.S11Opt.Simplified.BundledAdapters
import Sqpack.S11Opt.F02.Data

namespace SquarePacking.S11Opt
open FieldTree
open F02

-- The same generated option and bridge application used by Bundled.F02.cover1.
example {hps : List (ℤ × ℤ × ℤ)} {Q M R : ℕ} {s U : ℝ}
    (hQ : 0 < Q) (hR : 0 < R) (hc : CovF Q M R hps opts1 0 M 0 M 0 R)
    (hs0 : 0 < s) (hs1 : s < 1) (hUM : U / s ≤ (M : ℝ) / Q)
    {c : ℝ × ℝ} {θ : ℝ} (hin : sq c θ 1 ⊆ box U)
    (hcell : ∀ h ∈ hps, InHP Q h (c.1 / s, c.2 / s)) :
    (∃ S ∈ optSets1, ∀ a ∈ S, AtomSat Q (ScSq s c θ) (atoms.getD a [])) ∨
      ∃ e ∈ used1, ptQ Q e.2 ∈ ScSq s c θ := by
  exact field_option_cases (atoms := atoms) (sets := optSets1) (used := used1)
    (bridge hQ hR hc hs0 hs1 hUM hin hcell)

example {Q : ℕ} {A B : Set (ℝ × ℝ)}
    (hAc : Convex ℝ A) (hAo : IsOpen A) (hBc : Convex ℝ B) (hBo : IsOpen B)
    (hAB : Disjoint A B) (hA : AtomSat Q A [[(0, 0)]])
    (hB : AtomSat Q B [[(0, 0)]]) : False := by
  exact checked_maj_capacity (k := 1) (sites := [(0, 0)]) (subs := [[0]])
    (barys := [[[1]]]) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hAc hAo hBc hBo hAB hA hB

end SquarePacking.S11Opt
