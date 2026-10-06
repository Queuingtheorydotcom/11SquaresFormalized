import ElevenSquare.Pending.GeometryTypes
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Fin.VecNotation

namespace ElevenSquare.Pending
noncomputable section

def coordinate (i : Owner) (k : Fin 3) : Fin 33 := ⟨3*i.val+k.val, by
  have hi : i.val ≤ 10 := Nat.le_of_lt_succ i.isLt
  have hm : 3*i.val ≤ 30 := Nat.mul_le_mul_left 3 hi
  exact Nat.add_lt_add_of_le_of_lt hm k.isLt⟩

def perturbedCenter (q₀ : Owner → UnitSquare) (h : Displacement) (i : Owner) : Point :=
  (q₀ i).center + (h (coordinate i 0), h (coordinate i 1))

def perturbedAxis (q₀ : Owner → UnitSquare) (h : Displacement) (i : Owner) : Point :=
  let a := (q₀ i).axis
  let θ := h (coordinate i 2)
  (Real.cos θ*a.1-Real.sin θ*a.2, Real.sin θ*a.1+Real.cos θ*a.2)

-- Source packing.py order: bottom-left, bottom-right, top-right, top-left.
def cornerSigns (v : Fin 4) : Point := (![(-1,-1),(1,-1),(1,1),(-1,1)] : Fin 4 → Point) v

def perturbedCorner (q₀ : Owner → UnitSquare) (h : Displacement)
    (i : Owner) (v : Fin 4) : Point :=
  let a := perturbedAxis q₀ h i
  let s := cornerSigns v
  perturbedCenter q₀ h i + (s.1/2) • a + (s.2/2) • perp a

structure SeparationFeature where
  owner : Owner
  other : Owner
  distinct : owner ≠ other
  perpendicular : Bool
  reverse : Bool

def featureGap (q₀ : Owner → UnitSquare) (f : SeparationFeature)
    (v : Fin 4) (h : Displacement) : ℝ :=
  let a := perturbedAxis q₀ h f.owner
  let n := if f.perpendicular then perp a else a
  (if f.reverse then (-1 : ℝ) else 1) *
    dot (perturbedCorner q₀ h f.other v-perturbedCenter q₀ h f.owner) n - 1/2

inductive Gap
  | pair (f : SeparationFeature) (corner : Fin 4)
  | wall (owner : Owner) (corner : Fin 4) (wall : Fin 4)

def gapValue (S : ℝ) (q₀ : Owner → UnitSquare) : Gap → Displacement → ℝ
  | .pair f v, h => featureGap q₀ f v h
  | .wall i v w, h =>
      let p := perturbedCorner q₀ h i v
      (![p.1, S-p.1, p.2, S-p.2] : Fin 4 → ℝ) w

def LocalFeasible (S : ℝ) (q₀ : Owner → UnitSquare) (h : Displacement) : Prop :=
  ∃ P : Packing 11 S, ∀ i,
    (P.squares i).center = perturbedCenter q₀ h i ∧
    (P.squares i).axis = perturbedAxis q₀ h i


end
end ElevenSquare.Pending
