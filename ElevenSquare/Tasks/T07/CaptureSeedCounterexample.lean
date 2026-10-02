import ElevenSquare.Tasks.T07.CaptureSeedGeometry
import Mathlib.Tactic.NormNum

/-! A physically contained square shows why the nonempty phase-2 owned hull
cannot be promoted directly from an occupied-cell seed. The archived owned
point becomes valid only after further pose restrictions. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def seedCounterSquare : UnitSquare where
  center := (7/10, 7/10)
  axis := (3/5, 4/5)
  axis_unit := by norm_num [normSq, dot]

def firstRootOwned0 : QPoint := (1813417/25000000, 5421223/6250000)

theorem seedCounterSquare_chart :
    seedCounterSquare.axis = chartAxis (1/2) := by
  norm_num [seedCounterSquare, chartAxis]

theorem seedCounterSquare_contained :
    ∀ p, ClosedSquare seedCounterSquare p → InContainer coverCap p := by
  have hw : halfWidth seedCounterSquare = 7/10 := by
    norm_num [halfWidth, seedCounterSquare,
      abs_of_nonneg (show (0 : ℝ) ≤ 3/5 by norm_num),
      abs_of_nonneg (show (0 : ℝ) ≤ 4/5 by norm_num)]
  apply contained_of_center_bounds seedCounterSquare coverCap
  all_goals rw [hw] <;> norm_num [seedCounterSquare, coverCap]

theorem seedCounterSquare_cell :
    ClosedCell (0 : Fin 16) (normalizeCenter seedCounterSquare.center) := by
  unfold ClosedCell InUnitBox
  constructor
  · norm_num [normalizeCenter, seedCounterSquare, coverCap]
  · intro j
    fin_cases j <;> norm_num [coordinateDistanceSq, normalizeCenter,
      seedCounterSquare, coverSite, coverCap]

theorem seedCounterSquare_field_cell :
    toField seedCounterSquare.center ∈
      (seedFieldCellPolygon (0 : Fin 16)).carrier :=
  seedFieldCellPolygon_sound (0 : Fin 16) _ seedCounterSquare_cell

/-- The first archived owner-0 point misses this legitimate occupied square.
The gap is exact and strict: its local Y coordinate exceeds one half. -/
theorem firstRootOwned0_not_uniform :
    ¬ OpenSquare seedCounterSquare
      ((realPoint firstRootOwned0).1/fieldScale,
        (realPoint firstRootOwned0).2/fieldScale) := by
  intro h
  have hy := h.2
  norm_num [OpenSquare, localY, dot, perp, seedCounterSquare,
    firstRootOwned0, realPoint, fieldScale, coverCap] at hy

end
end ElevenSquare.Tasks.T07
