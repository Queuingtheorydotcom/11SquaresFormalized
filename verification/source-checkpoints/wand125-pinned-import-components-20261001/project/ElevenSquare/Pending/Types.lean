import ElevenSquare.Pending.GeometryTypes
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega
import ElevenSquare.Geometry
import ElevenSquare.CoverData

/-! UNFINISHED FORMALIZATION OBLIGATIONS. See handoffs/Types.md.
Every `sorry` in this file is an explicit outstanding proof, not verified evidence. -/

namespace ElevenSquare.Pending
noncomputable section

abbrev QPoint := ℚ × ℚ

def realPoint (p : QPoint) : Point := (p.1, p.2)

structure Halfplane where
  a : ℚ
  b : ℚ
  c : ℚ
  deriving DecidableEq

def Halfplane.contains (l : Halfplane) (p : Point) : Prop :=
  (l.a : ℝ) * p.1 + (l.b : ℝ) * p.2 ≤ (l.c : ℝ)

abbrev Polygon := List Halfplane

def Polygon.carrier (P : Polygon) : Set Point :=
  {p | ∀ l ∈ P, l.contains p}

def rationalHull (vs : List QPoint) : Set Point :=
  convexHull ℝ {p | ∃ v ∈ vs, p = realPoint v}

def chartAxis (t : ℝ) : Point := ((1-t^2)/(1+t^2), 2*t/(1+t^2))

-- Relabeling changes owner indices, never the actual collection of squares.
def relabelPacking {S : ℝ} (P : Packing 11 S) (perm : Equiv.Perm Owner) : Packing 11 S where
  squares := fun i => P.squares (perm i)
  side_nonneg := P.side_nonneg
  contained := fun i p hp => P.contained (perm i) p hp
  interior_disjoint := by
    intro i j hij p hp
    exact P.interior_disjoint (perm i) (perm j) (fun h => hij (perm.injective h)) p hp

def IsCharted {S : ℝ} (P : Packing 11 S) : Prop :=
  ∀ i, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (P.squares i).axis = chartAxis t

structure PoseRow where
  lo : ℚ
  hi : ℚ
  centers : Polygon

def PoseRow.contains (r : PoseRow) (q : UnitSquare) : Prop :=
  q.center ∈ r.centers.carrier ∧ ∃ t : ℝ,
    0 ≤ t ∧ t ≤ 1 ∧ (r.lo : ℝ) ≤ t ∧ t ≤ (r.hi : ℝ) ∧ q.axis = chartAxis t

def RowsContain (rows : List PoseRow) (q : UnitSquare) : Prop :=
  ∃ r ∈ rows, r.contains q

structure PoseState where
  rows : Owner → List PoseRow
  owned : Owner → List QPoint

def OuterCovers {S : ℝ} (P : Packing 11 S) (s : PoseState) : Prop :=
  ∀ i, RowsContain (s.rows i) (P.squares i)

def OwnsHulls {S : ℝ} (P : Packing 11 S) (s : PoseState) : Prop :=
  ∀ i, rationalHull (s.owned i) ⊆ {p | OpenSquare (P.squares i) p}

def StateHolds {S : ℝ} (P : Packing 11 S) (s : PoseState) : Prop :=
  OuterCovers P s ∧ OwnsHulls P s

def CoreFits (Q : Set Point) (q : UnitSquare) : Prop :=
  ∀ v ∈ Q, OpenSquare q (q.center + v)

def forbiddenCenters (K Q : Set Point) : Set Point :=
  {c | ∃ k ∈ K, ∃ v ∈ Q, c = k - v}

def replaceRows (s : PoseState) (i : Owner) (rs : List PoseRow) : PoseState :=
  {s with rows := Function.update s.rows i rs}

def replaceHull (s : PoseState) (i : Owner) (vs : List QPoint) : PoseState :=
  {s with owned := Function.update s.owned i vs}

-- Used by all finite and analytic modules. Touching remains legal.


def InRectangle (r : Fin 33 → ℝ) (h : Displacement) : Prop :=
  ∀ j, |h j| ≤ r j

def LinearForm (a h : Fin 33 → ℝ) : ℝ := ∑ j, a j * h j

def Quadratic (a b c t : ℝ) : ℝ := a*t^2+b*t+c


end
end ElevenSquare.Pending
