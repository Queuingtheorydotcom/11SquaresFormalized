import ElevenSquare.Geometry

/-! Shared geometric names, extracted unchanged from Types to keep SAT imports small. -/
namespace ElevenSquare.Pending

abbrev Owner := Fin 11

abbrev Displacement := Fin 33 → ℝ

def SquaresDisjoint (q r : UnitSquare) : Prop :=
  ∀ p, ¬ (OpenSquare q p ∧ OpenSquare r p)

end ElevenSquare.Pending
