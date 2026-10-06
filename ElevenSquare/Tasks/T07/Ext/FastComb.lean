import ElevenSquare.Tasks.T07.Ext.Check

/-! An optional prototype for sparse Farkas computations. Zero coefficients
skip rational multiplications and additions. The original checker remains
unchanged; the equalities below cover every input, including unequal lengths. -/
namespace ElevenSquare.Tasks.T07.Ext.FastComb
open ElevenSquare.Pending

def combFast : List Halfplane → List ℚ → Halfplane
  | l :: P, m :: mu =>
      if m = 0 then combFast P mu
      else
        let tail := combFast P mu
        ⟨m * l.a + tail.a, m * l.b + tail.b, m * l.c + tail.c⟩
  | _, _ => ⟨0, 0, 0⟩

theorem combFast_eq_comb (P : List Halfplane) (mu : List ℚ) :
    combFast P mu = comb P mu := by
  induction P generalizing mu with
  | nil => cases mu <;> rfl
  | cons l P ih =>
    cases mu with
    | nil => rfl
    | cons m mu =>
      by_cases hm : m = 0
      · simp [combFast, comb, hm, ih]
      · simp [combFast, comb, hm, ih]

def impliesFastB (P : Polygon) (mu : List ℚ) (g : Halfplane) : Bool :=
  (mu.all fun m => decide (0 ≤ m)) && decide ((combFast P mu).a = g.a) &&
    decide ((combFast P mu).b = g.b) && decide ((combFast P mu).c ≤ g.c)

theorem impliesFastB_eq_impliesB (P : Polygon) (mu : List ℚ) (g : Halfplane) :
    impliesFastB P mu g = impliesB P mu g := by
  simp only [impliesFastB, impliesB, combFast_eq_comb]

theorem impliesFastB_sound {P : Polygon} {mu : List ℚ} {g : Halfplane}
    (h : impliesFastB P mu g = true) {p : Point} (hp : p ∈ P.carrier) :
    g.contains p := by
  exact impliesB_sound (by simpa only [impliesFastB_eq_impliesB] using h) hp

def emptyFastB (P : Polygon) (mu : List ℚ) : Bool :=
  (mu.all fun m => decide (0 ≤ m)) && decide ((combFast P mu).a = 0) &&
    decide ((combFast P mu).b = 0) && decide ((combFast P mu).c < 0)

theorem emptyFastB_eq_emptyB (P : Polygon) (mu : List ℚ) :
    emptyFastB P mu = emptyB P mu := by
  simp only [emptyFastB, emptyB, combFast_eq_comb]

theorem emptyFastB_sound {P : Polygon} {mu : List ℚ}
    (h : emptyFastB P mu = true) (p : Point) : p ∉ P.carrier := by
  exact emptyB_sound (by simpa only [emptyFastB_eq_emptyB] using h) p

end ElevenSquare.Tasks.T07.Ext.FastComb

#print axioms ElevenSquare.Tasks.T07.Ext.FastComb.combFast_eq_comb
#print axioms ElevenSquare.Tasks.T07.Ext.FastComb.impliesFastB_sound
#print axioms ElevenSquare.Tasks.T07.Ext.FastComb.emptyFastB_sound
