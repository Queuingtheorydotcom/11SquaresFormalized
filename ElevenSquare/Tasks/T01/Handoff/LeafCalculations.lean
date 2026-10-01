import ElevenSquare.Tasks.T01.Handoff.PlanData
namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending
noncomputable section
/-- The terminal-leaf requirement for an optional native plan family: empty rows,
collisions, or majority witnesses. No inhabitant is asserted. -/
def LeafCalculations (plans : PlanData) : Prop :=
  ∀ (g : Group), ReducedCoverage.Selected g →
    ∀ (k : Fin 2184), k.val ∈ groupCases g →
      (plans g k).LeafChecks (rootData g k)

end
end ElevenSquare.Tasks.T01.Handoff
