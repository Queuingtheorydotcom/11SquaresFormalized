import Sqpack.S11Opt.Split.U2Rules
import Sqpack.S11Opt.Split.U4Local

/-!
# U5 — case 438 has no packing below `T` (PROOF.md §8)

Owner: (unassigned; after U2Rules and U4).  Inputs: `research/candidate-capture/` (589 MB:
`near-refined1024-240.json`, `root-self-240.json`, `far13-collision-180.json`, …), checker
`candidate-capture/audit_complete_capture438.py`, `results/candidate-replay/`.
Steps: the root induction (Phase-2 residual kernel); the four closed branches `y₁₅ ≤ 5/4`,
`t₁₃ ≤ 147/512`, `t₂ ≤ 183/512`, rest; contradictions in the first three; the final near state
(136 angle rows, 1,542 centre vertices) inside the focused rectangle through the chart
`Q⁻¹(p − (Ux/2, Ux/2)) + (T/2, T/2)` (quarter turn, `U`-to-`T` translation, `t ↦ (t−1)/(t+1)`
near `t = 1`, `2 arctan` derivative bounds); then U4 and the span `T` of Trump's packing.
Weight: heavy (the author's replay 3,732 s + 461 s; ≈ 800–1,500 hand-written lines + U2 data).
-/

namespace SquarePacking.S11Opt.Split

/-- **U5.** -/
theorem case438 {S : ℝ} (hS : S < T) : ¬ RealizesIn S J438 := by
  sorry

end SquarePacking.S11Opt.Split
