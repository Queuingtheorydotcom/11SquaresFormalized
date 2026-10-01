import ElevenSquare.Tasks.T01.Handoff.RootData
import ElevenSquare.Tasks.T01.Handoff.ReducedCoverage.Data
namespace ElevenSquare.Tasks.T01.Handoff
open ElevenSquare.Pending
noncomputable section
/-- Optional native ancestry/branch-program data for the selected groups.
The baseline dispatcher now uses the published exclusion family instead.
This type retains the retired route's data requirement; no data is asserted. -/
abbrev PlanData := Group → Fin 2184 → Plan

end
end ElevenSquare.Tasks.T01.Handoff
