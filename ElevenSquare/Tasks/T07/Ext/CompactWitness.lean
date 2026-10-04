import ElevenSquare.Tasks.T07.Ext.CTreeChain

/-! Reconstruct exact planar Farkas witnesses from their supporting facets.

The data supplied here are choices of one or two facets, not claims that these
choices work. Every resulting ordinary `CTree` is still consumed by the existing
`CTree.check`. Degenerate or unsuitable choices therefore do not prove anything.
The literal fallback preserves witnesses that are not reconstructed exactly.
-/
namespace ElevenSquare.Tasks.T07.Ext.CompactWitness
open ElevenSquare.Pending

inductive Support where
  | zero
  | one (facet : Nat)
  | two (first second : Nat)
  | literal (weights : List ℚ)

/-- Cramer's rule in dimension two; all divisions use total rational arithmetic. -/
def Support.weights (P : Polygon) (g : Halfplane) : Support → List ℚ
  | .zero => List.replicate P.length 0
  | .one k =>
      let h := P.getD k ⟨0, 0, 0⟩
      let w := if h.a = 0 then g.b / h.b else g.a / h.a
      (List.range P.length).map fun j => if j = k then w else 0
  | .two k l =>
      let h := P.getD k ⟨0, 0, 0⟩
      let z := P.getD l ⟨0, 0, 0⟩
      let det := h.a * z.b - h.b * z.a
      let u := (g.a * z.b - g.b * z.a) / det
      let v := (h.a * g.b - h.b * g.a) / det
      (List.range P.length).map fun j =>
        (if j = k then u else 0) + (if j = l then v else 0)
  | .literal weights => weights

def witnesses (P K : Polygon) (supports : List Support) : List (List ℚ) :=
  supports.mapIdx fun k support => support.weights P (K.getD k ⟨0, 0, 0⟩)

/-- A context-dependent constructor, with no additional proof or checker rule. -/
abbrev Recipe := Ctx → Polygon → CTree

def raw (tree : CTree) : Recipe := fun _ _ => tree

def keep (m : Nat) (supports : List Support) : Recipe := fun C P =>
  .keep m (witnesses P (C.rs.getD m ⟨0, 0, []⟩).centers supports)

def forbidHull (owner : Nat) (corners : List (Nat × Nat))
    (supports : List Support) : Recipe := fun C P =>
  .forbidHull owner corners
    (witnesses P (edgesF (diffs (ownedOf C.s owner) C.core corners)) supports)

def collide (region : Nat) (supports : List Support) : Recipe := fun C P =>
  .collide region (witnesses P
    (edgesF ((C.regs.getD region ⟨0, [], []⟩).verts.map toQ)) supports)

def split (plane : Halfplane) (left right : Recipe) : Recipe := fun C P =>
  .split plane (left C (plane :: P)) (right C (negH plane :: P))

inductive Cut where
  | left (plane : Halfplane) (side : Recipe)
  | right (plane : Halfplane) (side : Recipe)

/-- Preserve both closed branches and the original order of all constraints. -/
def chain : List Cut → Recipe → Recipe
  | [], last => last
  | .left plane side :: cuts, last => split plane (chain cuts last) side
  | .right plane side :: cuts, last => split plane side (chain cuts last)

/-- Attach a recipe to the original sub-row data and original input row. -/
def sub (s : PoseState) (i : Owner) (rs : List PoseRow) (row : Nat)
    (a b : ℚ) (cuts : List SelfCut) (wall : ℚ) (core : List QPoint)
    (ccore : List ZPoint) (regs : List CReg) (recipe : Recipe) : Sub :=
  let u : Sub := ⟨a, b, cuts, wall, core, ccore, regs, .empty []⟩
  let context : Ctx := ⟨s, i, rs, core, a, b, regs⟩
  let polygon := subPoly ((s.rows i).getD row ⟨0, 0, []⟩) u
  {u with tree := recipe context polygon}

end ElevenSquare.Tasks.T07.Ext.CompactWitness
