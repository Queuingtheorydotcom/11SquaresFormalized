import ElevenSquare.Tasks.T01.Handoff.PlanData
namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending
noncomputable section
/-- The program-check requirement for an optional native plan family: exact core,
wall, cover, ownership, row-identity, and predecessor checks. No inhabitant is asserted. -/
def ProgramCalculations (plans : PlanData) : Prop :=
  ∀ (g : Group), ReducedCoverage.Selected g →
    ∀ (k : Fin 2184), k.val ∈ groupCases g →
      (plans g k).ProgramChecks (rootData g k)

end
end ElevenSquare.Tasks.T01.Handoff
