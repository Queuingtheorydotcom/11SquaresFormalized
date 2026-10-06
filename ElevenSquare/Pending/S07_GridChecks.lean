import ElevenSquare.Pending.S07_GridGeometry
import Mathlib.Data.List.Forall2

namespace ElevenSquare.Pending.GridDistance

def zipCheck {α β : Type*} (check : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => check a b && zipCheck check as bs
  | _, _ => false

theorem zipCheck_sound {α β : Type*} {R : α → β → Prop} {check : α → β → Bool}
    (hc : ∀ a b, check a b = true → R a b) :
    ∀ as bs, zipCheck check as bs = true → List.Forall₂ R as bs
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: as, b :: bs, h => by
    simp only [zipCheck, Bool.and_eq_true] at h
    exact .cons (hc a b h.1) (zipCheck_sound hc as bs h.2)

def pointCheck (p : QPoint) (g : GridPoint) : Bool :=
  decide ((g.1 : ℚ) ≤ scale*p.1 ∧ scale*p.1 ≤ (g.1 : ℚ)+1 ∧
    (g.2 : ℚ) ≤ scale*p.2 ∧ scale*p.2 ≤ (g.2 : ℚ)+1)

theorem pointCheck_sound (p : QPoint) (g : GridPoint) (h : pointCheck p g = true) :
    Contains g (realPoint p) := by
  have hq := of_decide_eq_true h
  dsimp [Contains, realPoint]
  exact_mod_cast hq

def Row (ps : List QPoint) (gs : List GridPoint) : Prop :=
  List.Forall₂ (fun p g => Contains g (realPoint p)) ps gs

def rowCheck : List QPoint → List GridPoint → Bool := zipCheck pointCheck

theorem rowCheck_sound (ps : List QPoint) (gs : List GridPoint)
    (h : rowCheck ps gs = true) : Row ps gs :=
  zipCheck_sound pointCheck_sound ps gs h

def closeCheck (a b : GridPoint) : Bool :=
  decide (2500 * ((delta a.1 b.1)^2 + (delta a.2 b.2)^2) ≤ 301 * (scale : ℤ)^2)

def pairCheck (as bs : List GridPoint) : Bool :=
  as.all (fun a => bs.all (fun b => closeCheck a b))

theorem pairCheck_sound (as bs : List GridPoint) (h : pairCheck as bs = true) :
    ∀ a ∈ as, ∀ b ∈ bs, Close a b := by
  simpa only [pairCheck, closeCheck, List.all_eq_true, decide_eq_true_eq, Close] using h

theorem related_mem {α β : Type*} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) : ∀ a ∈ as, ∃ b ∈ bs, R a b := by
  induction h with
  | nil => simp
  | @cons a b as bs hab habs ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, hab⟩
    · obtain ⟨y, hy, hxy⟩ := ih x hx
      exact ⟨y, List.mem_cons_of_mem b hy, hxy⟩

theorem rows_bound (ps qs : List QPoint) (as bs : List GridPoint)
    (hp : Row ps as) (hq : Row qs bs)
    (hc : ∀ a ∈ as, ∀ b ∈ bs, Close a b) :
    ∀ p ∈ ps, ∀ q ∈ qs, normSq (realPoint p-realPoint q) ≤ (301/2500 : ℝ) := by
  intro p hpm q hqm
  obtain ⟨a, ha, hap⟩ := related_mem hp p hpm
  obtain ⟨b, hb, hbq⟩ := related_mem hq q hqm
  exact close_bounds_points a b (realPoint p) (realPoint q) hap hbq (hc a ha b hb)

-- Array alignment preserves the original record order, including degenerate regions.
def ArrayAligned {α β : Type*} (R : α → β → Prop) (xs : Array α) (ys : Array β) : Prop :=
  List.Forall₂ R xs.toList ys.toList

theorem ArrayAligned.append {α β : Type*} {R : α → β → Prop}
    {xs xs' : Array α} {ys ys' : Array β}
    (h : ArrayAligned R xs ys) (h' : ArrayAligned R xs' ys') :
    ArrayAligned R (xs ++ xs') (ys ++ ys') := by
  simp only [ArrayAligned, Array.toList_append]
  exact List.rel_append h h'

theorem ArrayAligned.get! {α β : Type*} [Inhabited α] [Inhabited β]
    {R : α → β → Prop} {xs : Array α} {ys : Array β}
    (h : ArrayAligned R xs ys) (i : ℕ) (hi : i < xs.size) : R xs[i]! ys[i]! := by
  have hj : i < ys.size := by
    have hs : xs.size = ys.size := List.Forall₂.length_eq h
    rwa [← hs]
  rw [getElem!_pos xs i hi, getElem!_pos ys i hj]
  exact List.Forall₂.get h hi hj

end ElevenSquare.Pending.GridDistance
#print axioms ElevenSquare.Pending.GridDistance.rows_bound
#print axioms ElevenSquare.Pending.GridDistance.ArrayAligned.get!
