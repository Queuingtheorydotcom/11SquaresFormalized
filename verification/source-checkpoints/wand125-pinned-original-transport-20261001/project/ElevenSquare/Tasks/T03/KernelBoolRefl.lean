import Lean.Elab.Tactic

/- Construct the ordinary proof term `Eq.refl true` without a preliminary
   elaborator reduction of the goal. Lean's declaration kernel still checks
   the complete Boolean computation when validating the theorem body. -/
open Lean Meta Elab Tactic in
elab "t03_bool_refl" : tactic => withMainContext do
  let goal ← getMainGoal
  goal.assign (← mkEqRefl (mkConst ``Bool.true))
  replaceMainGoal []
