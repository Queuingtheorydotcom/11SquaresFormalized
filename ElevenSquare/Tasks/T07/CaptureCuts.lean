import ElevenSquare.Tasks.T07.CaptureRoot
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Cast.Order

/-! Semantic introduction of closed center and half-angle cuts. These lemmas
keep equality in both adjoining branches, as required by the capture tree. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem chartAxis_injective_of_nonneg {t u : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) (heq : chartAxis t = chartAxis u) : t = u := by
  have hd₁ : 1 + t^2 ≠ 0 := by positivity
  have hd₂ : 1 + u^2 ≠ 0 := by positivity
  have hx := congrArg Prod.fst heq
  dsimp [chartAxis] at hx
  field_simp [hd₁, hd₂] at hx
  have hs : t^2 = u^2 := by nlinarith
  have hp : (t-u)*(t+u) = 0 := by nlinarith [hs]
  rcases mul_eq_zero.mp hp with h | h <;> linarith

theorem chartAxis_parameter_unique {q : UnitSquare} {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) (ha : q.axis = chartAxis t₀) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → q.axis = chartAxis t → t = t₀ := by
  intro t ht _ htaxis
  exact chartAxis_injective_of_nonneg ht ht₀ (htaxis.symm.trans ha)

def clipAngleUpper (r : PoseRow) (a : ℚ) : PoseRow :=
  { r with hi := min r.hi a }

def clipAngleLower (r : PoseRow) (a : ℚ) : PoseRow :=
  { r with lo := max r.lo a }

theorem clipAngleUpper_contains {r : PoseRow} {q : UnitSquare} {a : ℚ}
    (h : r.contains q)
    (hcut : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → q.axis = chartAxis t → t ≤ (a : ℝ)) :
    (clipAngleUpper r a).contains q := by
  obtain ⟨hc, t, ht0, ht1, hlo, hhi, ha⟩ := h
  refine ⟨hc, t, ht0, ht1, hlo, ?_, ha⟩
  change t ≤ ((min r.hi a : ℚ) : ℝ)
  rw [Rat.cast_min]
  exact le_min hhi (hcut t ht0 ht1 ha)

theorem clipAngleLower_contains {r : PoseRow} {q : UnitSquare} {a : ℚ}
    (h : r.contains q)
    (hcut : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → q.axis = chartAxis t → (a : ℝ) ≤ t) :
    (clipAngleLower r a).contains q := by
  obtain ⟨hc, t, ht0, ht1, hlo, hhi, ha⟩ := h
  refine ⟨hc, t, ht0, ht1, ?_, hhi, ha⟩
  change ((max r.lo a : ℚ) : ℝ) ≤ t
  rw [Rat.cast_max]
  exact max_le hlo (hcut t ht0 ht1 ha)

def clipYUpper (r : PoseRow) (b : ℚ) : PoseRow :=
  { r with centers := { a := 0, b := 1, c := b } :: r.centers }

def clipYLower (r : PoseRow) (b : ℚ) : PoseRow :=
  { r with centers := { a := 0, b := -1, c := -b } :: r.centers }

theorem clipYUpper_contains {r : PoseRow} {q : UnitSquare} {b : ℚ}
    (h : r.contains q) (hcut : q.center.2 ≤ (b : ℝ)) :
    (clipYUpper r b).contains q := by
  obtain ⟨hc, ht⟩ := h
  refine ⟨?_, ht⟩
  intro l hl
  rcases List.mem_cons.mp hl with he | he
  · subst l
    simpa [Halfplane.contains] using hcut
  · exact hc l he

theorem clipYLower_contains {r : PoseRow} {q : UnitSquare} {b : ℚ}
    (h : r.contains q) (hcut : (b : ℝ) ≤ q.center.2) :
    (clipYLower r b).contains q := by
  obtain ⟨hc, ht⟩ := h
  refine ⟨?_, ht⟩
  intro l hl
  rcases List.mem_cons.mp hl with he | he
  · subst l
    simp only [Halfplane.contains]
    norm_num
    linarith
  · exact hc l he

def cutAngleUpper (s : PoseState) (i : Owner) (a : ℚ) : PoseState :=
  replaceRows s i ((s.rows i).map (fun r => clipAngleUpper r a))

def cutAngleLower (s : PoseState) (i : Owner) (a : ℚ) : PoseState :=
  replaceRows s i ((s.rows i).map (fun r => clipAngleLower r a))

def cutYUpper (s : PoseState) (i : Owner) (b : ℚ) : PoseState :=
  replaceRows s i ((s.rows i).map (fun r => clipYUpper r b))

def cutYLower (s : PoseState) (i : Owner) (b : ℚ) : PoseState :=
  replaceRows s i ((s.rows i).map (fun r => clipYLower r b))

private theorem rows_map_contains {S : ℝ} {s : PoseState} {i : Owner}
    {P : Packing 11 S}
    (hs : StateHolds P s) {f : PoseRow → PoseRow}
    (hf : ∀ r, r.contains (P.squares i) → (f r).contains (P.squares i)) :
    StateHolds P (replaceRows s i ((s.rows i).map f)) := by
  refine ⟨?_, hs.2⟩
  intro k
  by_cases hki : k = i
  · subst k
    obtain ⟨r, hr, hqr⟩ := hs.1 i
    have hrow : RowsContain ((s.rows i).map f) (P.squares i) :=
      ⟨f r, List.mem_map.mpr ⟨r, hr, rfl⟩, hf r hqr⟩
    simpa only [replaceRows, Function.update_self] using hrow
  · simpa only [replaceRows, Function.update_of_ne hki] using hs.1 k

theorem cutAngleUpper_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i : Owner) (a : ℚ) (hs : StateHolds P s)
    (hcut : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (P.squares i).axis = chartAxis t → t ≤ (a : ℝ)) :
    StateHolds P (cutAngleUpper s i a) := by
  exact rows_map_contains hs (fun r h => clipAngleUpper_contains h hcut)

theorem cutAngleUpper_from_parameter {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i : Owner) (a : ℚ) (hs : StateHolds P s) (t₀ : ℝ)
    (ht₀ : 0 ≤ t₀) (ha : (P.squares i).axis = chartAxis t₀)
    (hcut : t₀ ≤ (a : ℝ)) : StateHolds P (cutAngleUpper s i a) := by
  apply cutAngleUpper_sound P s i a hs
  intro t ht0 ht1 haxis
  rw [chartAxis_parameter_unique ht₀ ha t ht0 ht1 haxis]
  exact hcut

theorem cutAngleLower_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i : Owner) (a : ℚ) (hs : StateHolds P s)
    (hcut : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (P.squares i).axis = chartAxis t → (a : ℝ) ≤ t) :
    StateHolds P (cutAngleLower s i a) := by
  exact rows_map_contains hs (fun r h => clipAngleLower_contains h hcut)

theorem cutAngleLower_from_parameter {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i : Owner) (a : ℚ) (hs : StateHolds P s) (t₀ : ℝ)
    (ht₀ : 0 ≤ t₀) (ha : (P.squares i).axis = chartAxis t₀)
    (hcut : (a : ℝ) ≤ t₀) : StateHolds P (cutAngleLower s i a) := by
  apply cutAngleLower_sound P s i a hs
  intro t ht0 ht1 haxis
  rw [chartAxis_parameter_unique ht₀ ha t ht0 ht1 haxis]
  exact hcut

theorem cutYUpper_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i : Owner) (b : ℚ) (hs : StateHolds P s)
    (hcut : (P.squares i).center.2 ≤ (b : ℝ)) :
    StateHolds P (cutYUpper s i b) := by
  exact rows_map_contains hs (fun r h => clipYUpper_contains h hcut)

theorem cutYLower_sound {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (i : Owner) (b : ℚ) (hs : StateHolds P s)
    (hcut : (b : ℝ) ≤ (P.squares i).center.2) :
    StateHolds P (cutYLower s i b) := by
  exact rows_map_contains hs (fun r h => clipYLower_contains h hcut)

end
end ElevenSquare.Tasks.T07
