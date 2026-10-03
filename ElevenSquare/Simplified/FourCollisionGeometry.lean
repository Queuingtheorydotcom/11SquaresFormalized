import ElevenSquare.Pending.S07_OverlayReverseRow13
import ElevenSquare.Pending.S07_OverlayReverseRow26
import ElevenSquare.Pending.S07_OverlayReverseRow47
import ElevenSquare.Pending.S07_OverlayReverseRow92
import ElevenSquare.Pending.S07_OverlayReverseRow127
import ElevenSquare.Pending.S07_OverlayReverseRow172
import ElevenSquare.Pending.S07_OverlayReverseRow193
import ElevenSquare.Pending.S07_OverlayReverseRow206
import ElevenSquare.Pending.S07_GridChecks
import ElevenSquare.Tasks.T04.LabelLookup
import ElevenSquare.Simplified.FourCollisionFinite

/-! Four symmetry-related overlay collisions replace1,572distance certificates.
We reuse only their eight exact closed polygon certificates and strict distance
checks. Every other overlay remains a label tuple, without a hull proof. -/
namespace ElevenSquare.Simplified.FourCollision
open ElevenSquare.Pending
open ElevenSquare.Pending.GridDistance
open ElevenSquare.Pending.OverlayVertexChecks
noncomputable section

theorem distance_13_26 (p q : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 13 g) (view g p))
    (hq : ∀ g, ClosedCell (overlayLabels 26 g) (view g q)) :
    (coverCap - 1)^2 * normSq (p - q) < 1 := by
  have hp' := overlay_in_hull13 p
    (by simpa only [T04LabelLookup.label_row13] using hp)
  have hq' := overlay_in_hull26 q
    (by simpa only [T04LabelLookup.label_row26] using hq)
  exact hulls_strict rationalRow13 rationalRow26
    (rows_bound _ _ gridRow13 gridRow26
      (rowCheck_sound _ _ (by decide +kernel))
      (rowCheck_sound _ _ (by decide +kernel))
      (pairCheck_sound _ _ (by decide))) p hp' q hq'

theorem distance_92_172 (p q : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 92 g) (view g p))
    (hq : ∀ g, ClosedCell (overlayLabels 172 g) (view g q)) :
    (coverCap - 1)^2 * normSq (p - q) < 1 := by
  have hp' := overlay_in_hull92 p
    (by simpa only [T04LabelLookup.label_row92] using hp)
  have hq' := overlay_in_hull172 q
    (by simpa only [T04LabelLookup.label_row172] using hq)
  exact hulls_strict rationalRow92 rationalRow172
    (rows_bound _ _ gridRow92 gridRow172
      (rowCheck_sound _ _ (by decide +kernel))
      (rowCheck_sound _ _ (by decide +kernel))
      (pairCheck_sound _ _ (by decide))) p hp' q hq'

theorem distance_193_206 (p q : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 193 g) (view g p))
    (hq : ∀ g, ClosedCell (overlayLabels 206 g) (view g q)) :
    (coverCap - 1)^2 * normSq (p - q) < 1 := by
  have hp' := overlay_in_hull193 p
    (by simpa only [T04LabelLookup.label_row193] using hp)
  have hq' := overlay_in_hull206 q
    (by simpa only [T04LabelLookup.label_row206] using hq)
  exact hulls_strict rationalRow193 rationalRow206
    (rows_bound _ _ gridRow193 gridRow206
      (rowCheck_sound _ _ (by decide +kernel))
      (rowCheck_sound _ _ (by decide +kernel))
      (pairCheck_sound _ _ (by decide))) p hp' q hq'

theorem distance_47_127 (p q : Point)
    (hp : ∀ g, ClosedCell (overlayLabels 47 g) (view g p))
    (hq : ∀ g, ClosedCell (overlayLabels 127 g) (view g q)) :
    (coverCap - 1)^2 * normSq (p - q) < 1 := by
  have hp' := overlay_in_hull47 p
    (by simpa only [T04LabelLookup.label_row47] using hp)
  have hq' := overlay_in_hull127 q
    (by simpa only [T04LabelLookup.label_row127] using hq)
  exact hulls_strict rationalRow47 rationalRow127
    (rows_bound _ _ gridRow47 gridRow127
      (rowCheck_sound _ _ (by decide +kernel))
      (rowCheck_sound _ _ (by decide +kernel))
      (pairCheck_sound _ _ (by decide))) p hp' q hq'

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
