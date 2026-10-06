import ElevenSquare.Simplified.FiniteRefutation
import Mathlib.Tactic.FinCases
import ElevenSquare.Pending.S07_EncodedInitial
import ElevenSquare.Pending.S07_EncodedMasks
import ElevenSquare.Pending.S07_EncodedLabelProofs0
import ElevenSquare.Pending.S07_EncodedLabelProofs1
import ElevenSquare.Pending.S07_EncodedLabelProofs2
import ElevenSquare.Pending.S07_EncodedLabelProofs3
import ElevenSquare.Pending.S07_EncodedLabelProofs4
import ElevenSquare.Pending.S07_EncodedLabelProofs5
import ElevenSquare.Pending.S07_EncodedLabelProofs6
import ElevenSquare.Pending.S07_EncodedLabelProofs7
import ElevenSquare.Pending.S07_EncodedLabelProofs8
import ElevenSquare.Pending.S07_EncodedLabelProofs9
import ElevenSquare.Pending.S07_EncodedLabelProofs10
import ElevenSquare.Pending.S07_EncodedLabelProofs11
import ElevenSquare.Pending.S07_EncodedLabelProofs12
import ElevenSquare.Pending.S07_EncodedLabelProofs13

/-! Four quarter-turn-related distance exclusions suffice for the
finite symmetry bridge. Closed-cell label ties remain independent. -/
namespace ElevenSquare.Simplified.FourCollision
open ElevenSquare.Pending
open ElevenSquare.Pending.Propagation
open ElevenSquare.Pending.EncodedSearch

private theorem all_labels : AllRange LabelGood 0 220 :=
  (((((((((((((labels_range0.append labels_range1).append labels_range2).append labels_range3).append labels_range4).append labels_range5).append labels_range6).append labels_range7).append labels_range8).append labels_range9).append labels_range10).append labels_range11).append labels_range12).append labels_range13)

theorem labels_correct (r : Fin 220) (g : Fin 4) :
    label r.val g.val = (overlayLabels r g).val :=
  all_labels r.val (Nat.zero_le _) r.isLt g

def blocked (r s : ℕ) : Bool :=
  decide ((r = 13 ∧ s = 26) ∨ (r = 26 ∧ s = 13) ∨
    (r = 92 ∧ s = 172) ∨ (r = 172 ∧ s = 92) ∨
    (r = 193 ∧ s = 206) ∨ (r = 206 ∧ s = 193) ∨
    (r = 47 ∧ s = 127) ∨ (r = 127 ∧ s = 47))

def compatible (r s : ℕ) : Bool :=
  decide (label r 0 ≠ label s 0 ∧ label r 1 ≠ label s 1 ∧
    label r 2 ≠ label s 2 ∧ label r 3 ≠ label s 3) && !blocked r s

def Assignment (f : Owner → Fin 220) : Prop :=
  (∀ g : Fin 4, Function.Injective (fun i => overlayLabels (f i) g)) ∧
  (∀ g : Fin 4, Finset.univ.image (fun i => overlayLabels (f i) g) ∈ otherRawMasks) ∧
  (∀ i j : Owner, i ≠ j → blocked (f i).val (f j).val = false)

theorem compatible_of_assignment (r s : Fin 220)
    (hlabels : ∀ g : Fin 4, overlayLabels r g ≠ overlayLabels s g)
    (hban : blocked r.val s.val = false) : compatible r.val s.val = true := by
  have hd (g : Fin 4) : label r.val g.val ≠ label s.val g.val := by
    rw [labels_correct, labels_correct]
    intro he
    exact hlabels g (Fin.ext he)
  simp only [compatible, Bool.and_eq_true]
  exact ⟨decide_eq_true_iff.mpr ⟨hd 0, hd 1, hd 2, hd 3⟩, by rw [hban]; rfl⟩

theorem target_digits (a b c : Fin 6) :
    36*a.val+6*b.val+c.val < 216 ∧
    (36*a.val+6*b.val+c.val)/36 = a.val ∧
    ((36*a.val+6*b.val+c.val)/6)%6 = b.val ∧
    (36*a.val+6*b.val+c.val)%6 = c.val := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  omega

theorem supports_of_masks (a b c : Fin 6) (r : Fin 220)
    (h1 : label r.val 1 ∈ mask a.val)
    (h2 : label r.val 2 ∈ mask b.val)
    (h3 : label r.val 3 ∈ mask c.val) :
    supports (36*a.val+6*b.val+c.val) r.val = true := by
  obtain ⟨_, ha, hb, hc⟩ := target_digits a b c
  simp only [supports, ha, hb, hc, List.contains, List.elem_eq_mem]
  simp [h1, h2, h3]

theorem initial_mem {k v : ℕ} {options : List ℕ}
    (h : (v,options) ∈ initialDomains k) :
    v ∈ mask k ∧ options = (List.range 220).filter (fun r => decide (label r 0 = v)) := by
  obtain ⟨u, hu, he⟩ := List.mem_map.mp h
  have huv : u = v := congrArg Prod.fst he
  subst u
  exact ⟨hu, (congrArg Prod.snd he).symm⟩

theorem assignment_encoded (f : Owner → Fin 220) (hf : Assignment f) :
    ∃ k : Fin 6, Sat compatible supports (initialDomains k.val) (List.range 216) := by
  classical
  let M := fun g : Fin 4 => Finset.univ.image (fun i => overlayLabels (f i) g)
  obtain ⟨k0, hk0⟩ := other_mask_rep (M 0) (hf.2.1 0)
  obtain ⟨k1, hk1⟩ := other_mask_rep (M 1) (hf.2.1 1)
  obtain ⟨k2, hk2⟩ := other_mask_rep (M 2) (hf.2.1 2)
  obtain ⟨k3, hk3⟩ := other_mask_rep (M 3) (hf.2.1 3)
  let first := fun i : Owner => (overlayLabels (f i) 0).val
  let owner := Function.invFun first
  have howner (v : ℕ) (hv : v ∈ mask k0.val) : first (owner v) = v := by
    apply Function.invFun_eq
    have hv16 := mask_bounded k0 v hv
    have hm : (⟨v,hv16⟩ : Fin 16) ∈ M 0 := (hk0 ⟨v,hv16⟩).mpr hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    exact ⟨i, congrArg Fin.val hi⟩
  have hmem (g : Fin 4) (i : Owner) : overlayLabels (f i) g ∈ M g :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let assignment := fun v => (f (owner v)).val
  let t := 36*k1.val+6*k2.val+k3.val
  refine ⟨k0, assignment, t, List.mem_range.mpr (target_digits k1 k2 k3).1, ?_, ?_⟩
  · intro v options hv
    obtain ⟨hvMask, rfl⟩ := initial_mem hv
    refine ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (f (owner v)).isLt, ?_⟩, ?_⟩
    · apply decide_eq_true
      exact (labels_correct (f (owner v)) 0).trans (howner v hvMask)
    · apply supports_of_masks k1 k2 k3 (f (owner v))
      · rw [show label (assignment v) 1 = (overlayLabels (f (owner v)) 1).val from labels_correct _ 1]
        exact (hk1 _).mp (hmem 1 (owner v))
      · rw [show label (assignment v) 2 = (overlayLabels (f (owner v)) 2).val from labels_correct _ 2]
        exact (hk2 _).mp (hmem 2 (owner v))
      · rw [show label (assignment v) 3 = (overlayLabels (f (owner v)) 3).val from labels_correct _ 3]
        exact (hk3 _).mp (hmem 3 (owner v))
  · intro u left hu v right hv hne
    have huv : owner u ≠ owner v := by
      intro he
      apply hne
      exact (howner u (initial_mem hu).1).symm.trans
        ((congrArg first he).trans (howner v (initial_mem hv).1))
    apply compatible_of_assignment (f (owner u)) (f (owner v))
    · intro g he
      exact huv (hf.1 g he)
    · exact hf.2.2 _ _ huv

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem root_rejected0 :
    ¬ Sat compatible supports (initialDomains 0) (List.range 216) :=
  FiniteRefutation.sound compatible supports 12 _ _ (by decide)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem root_rejected1 :
    ¬ Sat compatible supports (initialDomains 1) (List.range 216) :=
  FiniteRefutation.sound compatible supports 12 _ _ (by decide)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem root_rejected2 :
    ¬ Sat compatible supports (initialDomains 2) (List.range 216) :=
  FiniteRefutation.sound compatible supports 12 _ _ (by decide)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem root_rejected3 :
    ¬ Sat compatible supports (initialDomains 3) (List.range 216) :=
  FiniteRefutation.sound compatible supports 12 _ _ (by decide)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem root_rejected4 :
    ¬ Sat compatible supports (initialDomains 4) (List.range 216) :=
  FiniteRefutation.sound compatible supports 12 _ _ (by decide)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem root_rejected5 :
    ¬ Sat compatible supports (initialDomains 5) (List.range 216) :=
  FiniteRefutation.sound compatible supports 12 _ _ (by decide)

theorem no_assignment : ¬ ∃ f : Owner → Fin 220, Assignment f := by
  rintro ⟨f, hf⟩
  obtain ⟨k, hk⟩ := assignment_encoded f hf
  fin_cases k
  · exact root_rejected0 hk
  · exact root_rejected1 hk
  · exact root_rejected2 hk
  · exact root_rejected3 hk
  · exact root_rejected4 hk
  · exact root_rejected5 hk

end ElevenSquare.Simplified.FourCollision

#print axioms ElevenSquare.Simplified.FourCollision.assignment_encoded
#print axioms ElevenSquare.Simplified.FourCollision.no_assignment
