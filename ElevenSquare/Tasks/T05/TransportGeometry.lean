import ElevenSquare.Cover
import ElevenSquare.Pending.S07_LabelData

namespace ElevenSquare.Pending.T05Transport
noncomputable section

/-- The eight signed-coordinate symmetries of the entire container. -/
def mapPoint (S : ℝ) (g : Fin 4) (flip : Bool) (p : Point) : Point :=
  let z := (![p, (S-p.1,p.2), (S-p.2,p.1), (p.2,p.1)] : Fin 4 → Point) g
  if flip then (S-z.1,S-z.2) else z

/-- The linear part acts on a square's unit axis. -/
def mapAxis (g : Fin 4) (flip : Bool) (v : Point) : Point :=
  mapPoint 0 g flip v

theorem mapPoint_sub (S : ℝ) (g : Fin 4) (flip : Bool) (p c : Point) :
    mapPoint S g flip p - mapPoint S g flip c = mapAxis g flip (p-c) := by
  fin_cases g <;> cases flip <;> ext <;> simp [mapPoint, mapAxis] <;> ring

theorem mapAxis_normSq (g : Fin 4) (flip : Bool) (v : Point) :
    normSq (mapAxis g flip v) = normSq v := by
  fin_cases g <;> cases flip <;> simp [mapAxis, mapPoint, normSq, dot] <;> ring

theorem mapAxis_dot (g : Fin 4) (flip : Bool) (v a : Point) :
    dot (mapAxis g flip v) (mapAxis g flip a) = dot v a := by
  fin_cases g <;> cases flip <;> simp [mapAxis, mapPoint, dot] <;> ring

theorem mapAxis_abs_perp_dot (g : Fin 4) (flip : Bool) (v a : Point) :
    |dot (mapAxis g flip v) (perp (mapAxis g flip a))| = |dot v (perp a)| := by
  apply (sq_eq_sq_iff_abs_eq_abs _ _).mp
  fin_cases g <;> cases flip <;> simp [mapAxis, mapPoint, dot, perp] <;> ring

theorem mapPoint_surjective (S : ℝ) (g : Fin 4) (flip : Bool) :
    Function.Surjective (mapPoint S g flip) := by
  intro p
  refine ⟨mapPoint S g (if g = 2 then !flip else flip) p, ?_⟩
  fin_cases g <;> cases flip <;> ext <;> simp [mapPoint] <;> ring

theorem mapPoint_container (S : ℝ) (g : Fin 4) (flip : Bool) (p : Point)
    (hp : InContainer S p) : InContainer S (mapPoint S g flip p) := by
  rcases hp with ⟨hx0,hx1,hy0,hy1⟩
  fin_cases g <;> cases flip <;> dsimp [mapPoint, InContainer, Matrix.vecHead, Matrix.vecTail]
  all_goals exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- This is definitionally the target's physicalSymmetry, below that target's import boundary. -/
def physicalMap (g : Fin 4) (flip : Bool) (p : Point) : Point :=
  let z := (if flip then halfTurn else id) (view g (normalizeCenter p))
  ((coverCap-1)*z.1+1/2, (coverCap-1)*z.2+1/2)

theorem physicalMap_eq_mapPoint (g : Fin 4) (flip : Bool) (p : Point) :
    physicalMap g flip p = mapPoint coverCap g flip p := by
  have hu : coverCap-1 ≠ 0 := ne_of_gt (sub_pos.mpr coverCap_gt_one)
  fin_cases g <;> cases flip <;> ext <;>
    dsimp [physicalMap, view, halfTurn, mapPoint, normalizeCenter, id] <;>
    field_simp [hu] <;> ring

theorem normalize_physicalMap (g : Fin 4) (flip : Bool) (p : Point) :
    normalizeCenter (physicalMap g flip p) =
      (if flip then halfTurn else id) (view g (normalizeCenter p)) := by
  have hu : coverCap-1 ≠ 0 := ne_of_gt (sub_pos.mpr coverCap_gt_one)
  let z := (if flip then halfTurn else id) (view g (normalizeCenter p))
  change normalizeCenter ((coverCap-1)*z.1+1/2, (coverCap-1)*z.2+1/2) = z
  ext <;> dsimp [normalizeCenter] <;> field_simp [hu] <;> ring

end
end ElevenSquare.Pending.T05Transport
#print axioms ElevenSquare.Pending.T05Transport.physicalMap_eq_mapPoint
#print axioms ElevenSquare.Pending.T05Transport.normalize_physicalMap
