import ElevenSquare.Tasks.T04.Completeness.Support
import ElevenSquare.Simplified.FourCollisionFinite

/-! Four exact collision bounds from closed-cell halfplanes. Each overlay is
enclosed in a small rational rectangle by nonnegative combinations of two
original halfplanes. This keeps all boundary ties and avoids reconstructing
eight polygon hulls or enumerating distances between their vertices. -/
namespace ElevenSquare.Simplified.FourCollision
open ElevenSquare.Pending ElevenSquare.Pending.T04Completeness
noncomputable section

private structure BoundCertificate where
  firstView : Fin 4
  firstPlane : Fin 20
  secondView : Fin 4
  secondPlane : Fin 20
  firstWeight : ℕ
  secondWeight : ℕ
  scale : ℕ

private def BoundCertificate.combined (c : BoundCertificate) (r : Fin 220) : IntegerPlane :=
  (sourcePlane c.firstView (overlayLabels r c.firstView) c.firstPlane).combine
    (sourcePlane c.secondView (overlayLabels r c.secondView) c.secondPlane)
    c.firstWeight c.secondWeight

private def BoundCertificate.check (c : BoundCertificate) (r : Fin 220)
    (target : IntegerPlane) : Bool :=
  let l := c.combined r
  decide (0 < c.scale ∧ l.a = c.scale * target.a ∧
    l.b = c.scale * target.b ∧ l.c ≤ c.scale * target.c)

private theorem bound_sound (r : Fin 220) (p : Point)
    (hp : ∀ g, ClosedCell (overlayLabels r g) (view g p))
    (target : IntegerPlane) (c : BoundCertificate) (hc : c.check r target = true) :
    target.rational.contains p := by
  have checked := of_decide_eq_true hc
  have hs : (c.combined r).rational.contains p :=
    IntegerPlane.combine_sound _ _ c.firstWeight c.secondWeight
      (by exact_mod_cast Nat.zero_le c.firstWeight)
      (by exact_mod_cast Nat.zero_le c.secondWeight) p
      (sourcePlane_sound _ _ _ p (hp c.firstView))
      (sourcePlane_sound _ _ _ p (hp c.secondView))
  have hscale : (0 : ℝ) < c.scale := by exact_mod_cast checked.1
  have ha : ((c.combined r).a : ℝ) = (c.scale : ℝ) * target.a := by
    exact_mod_cast checked.2.1
  have hb : ((c.combined r).b : ℝ) = (c.scale : ℝ) * target.b := by
    exact_mod_cast checked.2.2.1
  have hh : ((c.combined r).c : ℝ) ≤ (c.scale : ℝ) * target.c := by
    exact_mod_cast checked.2.2.2
  change ((c.combined r).a : ℝ) * p.1 + ((c.combined r).b : ℝ) * p.2 ≤
    ((c.combined r).c : ℝ) at hs
  rw [ha, hb] at hs
  change (target.a : ℝ) * p.1 + (target.b : ℝ) * p.2 ≤ (target.c : ℝ)
  apply (mul_le_mul_iff_right₀ hscale).mp
  nlinarith only [hs, hh]

private theorem square_le_of_bounds {z d : ℝ} (hlo : -d ≤ z) (hhi : z ≤ d) :
    z^2 ≤ d^2 := by
  have hprod := mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ d + z by linarith)
  nlinarith only [hprod]

private theorem collision_of_deltas (p q : Point) {dx dy : ℝ}
    (hxlo : -dx ≤ p.1 - q.1) (hxhi : p.1 - q.1 ≤ dx)
    (hylo : -dy ≤ p.2 - q.2) (hyhi : p.2 - q.2 ≤ dy)
    (hbudget : dx^2 + dy^2 ≤ 221/2500) :
    (coverCap - 1)^2 * normSq (p - q) < 1 := by
  have hx := square_le_of_bounds hxlo hxhi
  have hy := square_le_of_bounds hylo hyhi
  have hn : normSq (p - q) ≤ 221/2500 := by
    dsimp [normSq, dot]
    nlinarith only [hx, hy, hbudget]
  calc
    (coverCap - 1)^2 * normSq (p - q) ≤ (coverCap - 1)^2 * (221/2500) :=
      mul_le_mul_of_nonneg_left hn (sq_nonneg _)
    _ < 1 := by norm_num [coverCap]

private theorem box_13 (p : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 13 g) (view g p)) :
    (23 / 50 : ℝ) ≤ p.1 ∧ p.1 ≤ 27 / 50 ∧
      (0 : ℝ) ≤ p.2 ∧ p.2 ≤ 11 / 100 := by
  have h0 := bound_sound 13 p hp ⟨-50, 0, -23⟩ ⟨0, 2, 2, 11, 48252000000, 1, 42255200000⟩ (by decide +kernel)
  have h1 := bound_sound 13 p hp ⟨50, 0, 27⟩ ⟨0, 2, 3, 12, 48252000000, 1, 42255200000⟩ (by decide +kernel)
  have h2 := bound_sound 13 p hp ⟨0, -1, 0⟩ ⟨0, 0, 0, 2, 0, 1, 1⟩ (by decide +kernel)
  have h3 := bound_sound 13 p hp ⟨0, 100, 11⟩ ⟨0, 6, 1, 6, 1, 1, 14920480000⟩ (by decide +kernel)
  norm_num [IntegerPlane.rational, Halfplane.contains] at h0 h1 h2 h3
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem box_26 (p : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 26 g) (view g p)) :
    (11 / 25 : ℝ) ≤ p.1 ∧ p.1 ≤ 14 / 25 ∧
      (23 / 100 : ℝ) ≤ p.2 ∧ p.2 ≤ 7 / 25 := by
  have h0 := bound_sound 26 p hp ⟨-25, 0, -11⟩ ⟨0, 9, 1, 6, 1, 1, 167978240000⟩ (by decide +kernel)
  have h1 := bound_sound 26 p hp ⟨25, 0, 14⟩ ⟨2, 14, 3, 8, 11629, 285, 991888293760000⟩ (by decide +kernel)
  have h2 := bound_sound 26 p hp ⟨0, -100, -23⟩ ⟨0, 9, 2, 15, 367197, 524932, 5871399860880000⟩ (by decide +kernel)
  have h3 := bound_sound 26 p hp ⟨0, 25, 7⟩ ⟨0, 10, 3, 8, 367197, 3271, 32305779735360000⟩ (by decide +kernel)
  norm_num [IntegerPlane.rational, Halfplane.contains] at h0 h1 h2 h3
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem box_92 (p : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 92 g) (view g p)) :
    (18 / 25 : ℝ) ≤ p.1 ∧ p.1 ≤ 77 / 100 ∧
      (11 / 25 : ℝ) ≤ p.2 ∧ p.2 ≤ 14 / 25 := by
  have h0 := bound_sound 92 p hp ⟨-25, 0, -18⟩ ⟨1, 8, 2, 13, 3271, 367197, 32305779735360000⟩ (by decide +kernel)
  have h1 := bound_sound 92 p hp ⟨100, 0, 77⟩ ⟨0, 15, 2, 14, 524932, 367197, 5871399860880000⟩ (by decide +kernel)
  have h2 := bound_sound 92 p hp ⟨0, -25, -11⟩ ⟨2, 14, 3, 17, 1, 1, 167978240000⟩ (by decide +kernel)
  have h3 := bound_sound 92 p hp ⟨0, 25, 14⟩ ⟨0, 14, 1, 8, 11629, 285, 991888293760000⟩ (by decide +kernel)
  norm_num [IntegerPlane.rational, Halfplane.contains] at h0 h1 h2 h3
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem box_172 (p : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 172 g) (view g p)) :
    (89 / 100 : ℝ) ≤ p.1 ∧ p.1 ≤ 1 ∧
      (23 / 50 : ℝ) ≤ p.2 ∧ p.2 ≤ 27 / 50 := by
  have h0 := bound_sound 172 p hp ⟨-100, 0, -89⟩ ⟨2, 17, 3, 17, 1, 1, 14920480000⟩ (by decide +kernel)
  have h1 := bound_sound 172 p hp ⟨1, 0, 1⟩ ⟨0, 1, 0, 2, 1, 0, 1⟩ (by decide +kernel)
  have h2 := bound_sound 172 p hp ⟨0, -50, -23⟩ ⟨0, 1, 0, 11, 48252000000, 1, 42255200000⟩ (by decide +kernel)
  have h3 := bound_sound 172 p hp ⟨0, 50, 27⟩ ⟨0, 1, 1, 12, 48252000000, 1, 42255200000⟩ (by decide +kernel)
  norm_num [IntegerPlane.rational, Halfplane.contains] at h0 h1 h2 h3
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem box_193 (p : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 193 g) (view g p)) :
    (11 / 25 : ℝ) ≤ p.1 ∧ p.1 ≤ 14 / 25 ∧
      (18 / 25 : ℝ) ≤ p.2 ∧ p.2 ≤ 77 / 100 := by
  have h0 := bound_sound 193 p hp ⟨-25, 0, -11⟩ ⟨2, 9, 3, 15, 11629, 285, 991888293760000⟩ (by decide +kernel)
  have h1 := bound_sound 193 p hp ⟨25, 0, 14⟩ ⟨0, 14, 1, 17, 1, 1, 167978240000⟩ (by decide +kernel)
  have h2 := bound_sound 193 p hp ⟨0, -25, -18⟩ ⟨0, 13, 2, 12, 160993, 3271, 14016585389920000⟩ (by decide +kernel)
  have h3 := bound_sound 193 p hp ⟨0, 100, 77⟩ ⟨0, 14, 2, 8, 367197, 524932, 5871399860880000⟩ (by decide +kernel)
  norm_num [IntegerPlane.rational, Halfplane.contains] at h0 h1 h2 h3
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem box_206 (p : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 206 g) (view g p)) :
    (23 / 50 : ℝ) ≤ p.1 ∧ p.1 ≤ 27 / 50 ∧
      (89 / 100 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 := by
  have h0 := bound_sound 206 p hp ⟨-50, 0, -23⟩ ⟨0, 3, 3, 11, 48252000000, 1, 42255200000⟩ (by decide +kernel)
  have h1 := bound_sound 206 p hp ⟨50, 0, 27⟩ ⟨0, 3, 2, 12, 48252000000, 1, 42255200000⟩ (by decide +kernel)
  have h2 := bound_sound 206 p hp ⟨0, -100, -89⟩ ⟨0, 17, 1, 17, 1, 1, 14920480000⟩ (by decide +kernel)
  have h3 := bound_sound 206 p hp ⟨0, 1, 1⟩ ⟨0, 0, 0, 3, 0, 1, 1⟩ (by decide +kernel)
  norm_num [IntegerPlane.rational, Halfplane.contains] at h0 h1 h2 h3
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem box_47 (p : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 47 g) (view g p)) :
    (0 : ℝ) ≤ p.1 ∧ p.1 ≤ 11 / 100 ∧
      (23 / 50 : ℝ) ≤ p.2 ∧ p.2 ≤ 27 / 50 := by
  have h0 := bound_sound 47 p hp ⟨-1, 0, 0⟩ ⟨0, 0, 0, 2, 1, 0, 1⟩ (by decide +kernel)
  have h1 := bound_sound 47 p hp ⟨100, 0, 11⟩ ⟨2, 6, 3, 6, 1, 1, 14920480000⟩ (by decide +kernel)
  have h2 := bound_sound 47 p hp ⟨0, -50, -23⟩ ⟨0, 0, 1, 11, 48252000000, 1, 42255200000⟩ (by decide +kernel)
  have h3 := bound_sound 47 p hp ⟨0, 50, 27⟩ ⟨0, 0, 0, 12, 48252000000, 1, 42255200000⟩ (by decide +kernel)
  norm_num [IntegerPlane.rational, Halfplane.contains] at h0 h1 h2 h3
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem box_127 (p : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 127 g) (view g p)) :
    (23 / 100 : ℝ) ≤ p.1 ∧ p.1 ≤ 7 / 25 ∧
      (11 / 25 : ℝ) ≤ p.2 ∧ p.2 ≤ 14 / 25 := by
  have h0 := bound_sound 127 p hp ⟨-100, 0, -23⟩ ⟨0, 8, 2, 9, 524932, 367197, 5871399860880000⟩ (by decide +kernel)
  have h1 := bound_sound 127 p hp ⟨25, 0, 7⟩ ⟨2, 5, 2, 10, 3271, 520839, 46113976329760000⟩ (by decide +kernel)
  have h2 := bound_sound 127 p hp ⟨0, -25, -11⟩ ⟨0, 9, 1, 15, 11629, 285, 991888293760000⟩ (by decide +kernel)
  have h3 := bound_sound 127 p hp ⟨0, 25, 14⟩ ⟨2, 9, 3, 6, 1, 1, 167978240000⟩ (by decide +kernel)
  norm_num [IntegerPlane.rational, Halfplane.contains] at h0 h1 h2 h3
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem distance_13_26 (p q : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 13 g) (view g p))
    (hq : ∀ g, ClosedCell (overlayLabels 26 g) (view g q)) :
    (coverCap - 1)^2 * normSq (p - q) < 1 := by
  obtain ⟨hpx0, hpx1, hpy0, hpy1⟩ := box_13 p hp
  obtain ⟨hqx0, hqx1, hqy0, hqy1⟩ := box_26 q hq
  exact collision_of_deltas p q (dx := 1/10) (dy := 7/25)
    (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num)

theorem distance_92_172 (p q : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 92 g) (view g p))
    (hq : ∀ g, ClosedCell (overlayLabels 172 g) (view g q)) :
    (coverCap - 1)^2 * normSq (p - q) < 1 := by
  obtain ⟨hpx0, hpx1, hpy0, hpy1⟩ := box_92 p hp
  obtain ⟨hqx0, hqx1, hqy0, hqy1⟩ := box_172 q hq
  exact collision_of_deltas p q (dx := 7/25) (dy := 1/10)
    (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num)

theorem distance_193_206 (p q : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 193 g) (view g p))
    (hq : ∀ g, ClosedCell (overlayLabels 206 g) (view g q)) :
    (coverCap - 1)^2 * normSq (p - q) < 1 := by
  obtain ⟨hpx0, hpx1, hpy0, hpy1⟩ := box_193 p hp
  obtain ⟨hqx0, hqx1, hqy0, hqy1⟩ := box_206 q hq
  exact collision_of_deltas p q (dx := 1/10) (dy := 7/25)
    (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num)

theorem distance_47_127 (p q : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 47 g) (view g p))
    (hq : ∀ g, ClosedCell (overlayLabels 127 g) (view g q)) :
    (coverCap - 1)^2 * normSq (p - q) < 1 := by
  obtain ⟨hpx0, hpx1, hpy0, hpy1⟩ := box_47 p hp
  obtain ⟨hqx0, hqx1, hqy0, hqy1⟩ := box_127 q hq
  exact collision_of_deltas p q (dx := 7/25) (dy := 1/10)
    (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num)

theorem blocked_distance (r s : Fin 220) (p q : Point)
    (hr : ∀ g, ClosedCell (overlayLabels r g) (view g p))
    (hs : ∀ g, ClosedCell (overlayLabels s g) (view g q))
    (hb : blocked r.val s.val = true) :
    (coverCap - 1)^2 * normSq (p - q) < 1 := by
  have h : (r.val = 13 ∧ s.val = 26) ∨ (r.val = 26 ∧ s.val = 13) ∨
      (r.val = 92 ∧ s.val = 172) ∨ (r.val = 172 ∧ s.val = 92) ∨
      (r.val = 193 ∧ s.val = 206) ∨ (r.val = 206 ∧ s.val = 193) ∨
      (r.val = 47 ∧ s.val = 127) ∨ (r.val = 127 ∧ s.val = 47) :=
    of_decide_eq_true hb
  have hsym (p q : Point) : normSq (q - p) = normSq (p - q) := by
    dsimp [normSq, dot]
    ring
  rcases h with h | h | h | h | h | h | h | h
  · have er : r = 13 := Fin.ext h.1
    have es : s = 26 := Fin.ext h.2
    subst r
    subst s
    exact distance_13_26 p q hr hs
  · have er : r = 26 := Fin.ext h.1
    have es : s = 13 := Fin.ext h.2
    subst r
    subst s
    simpa only [hsym q p] using distance_13_26 q p hs hr
  · have er : r = 92 := Fin.ext h.1
    have es : s = 172 := Fin.ext h.2
    subst r
    subst s
    exact distance_92_172 p q hr hs
  · have er : r = 172 := Fin.ext h.1
    have es : s = 92 := Fin.ext h.2
    subst r
    subst s
    simpa only [hsym q p] using distance_92_172 q p hs hr
  · have er : r = 193 := Fin.ext h.1
    have es : s = 206 := Fin.ext h.2
    subst r
    subst s
    exact distance_193_206 p q hr hs
  · have er : r = 206 := Fin.ext h.1
    have es : s = 193 := Fin.ext h.2
    subst r
    subst s
    simpa only [hsym q p] using distance_193_206 q p hs hr
  · have er : r = 47 := Fin.ext h.1
    have es : s = 127 := Fin.ext h.2
    subst r
    subst s
    exact distance_47_127 p q hr hs
  · have er : r = 127 := Fin.ext h.1
    have es : s = 47 := Fin.ext h.2
    subst r
    subst s
    simpa only [hsym q p] using distance_47_127 q p hs hr

theorem no_blocked_pair (P : Packing 11 coverCap) (f : Owner → Fin 220)
    (hf : ∀ i g, ClosedCell (overlayLabels (f i) g)
      (view g (normalizeCenter (P.squares i).center)))
    (i j : Owner) (hij : i ≠ j) : blocked (f i).val (f j).val = false := by
  cases hb : blocked (f i).val (f j).val with
  | false => rfl
  | true =>
    have hs := P.center_separation i j hij
    rw [normSq_sub_eq_distance, normalized_distance] at hs
    have hd := blocked_distance (f i) (f j)
      (normalizeCenter (P.squares i).center) (normalizeCenter (P.squares j).center)
      (hf i) (hf j) hb
    rw [normSq_sub_eq_distance] at hd
    exact False.elim ((not_lt_of_ge hs) hd)

end
end ElevenSquare.Simplified.FourCollision

#print axioms ElevenSquare.Simplified.FourCollision.distance_13_26
#print axioms ElevenSquare.Simplified.FourCollision.distance_92_172
#print axioms ElevenSquare.Simplified.FourCollision.distance_193_206
#print axioms ElevenSquare.Simplified.FourCollision.distance_47_127
#print axioms ElevenSquare.Simplified.FourCollision.no_blocked_pair
