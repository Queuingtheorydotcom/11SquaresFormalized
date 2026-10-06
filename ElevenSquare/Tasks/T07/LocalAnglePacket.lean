import ElevenSquare.Tasks.T07.LocalAngles
import ElevenSquare.Tasks.T07.LocalRadii
import ElevenSquare.Tasks.T07.NearFinalPacket

/-! The live near rows have eleven aggregate closed angle intervals. These
rational checks turn each interval into the corresponding focused radian
radius, including both quarter-turn-equivalent axis branches. -/

namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def axisLowMax : Owner → ℚ :=
  ![Rat.divInt 9 7936, Rat.divInt 7 7936, Rat.divInt 9 7936,
    Rat.divInt 3 3968, Rat.divInt 1 992, Rat.divInt 3 3968, 0, 0, 0, 0, 0]

def axisHighMin : Owner → ℚ :=
  ![Rat.divInt 496 497, Rat.divInt 1985 1988, Rat.divInt 1985 1988,
    Rat.divInt 3971 3976, Rat.divInt 1985 1988, Rat.divInt 3971 3976,
    0, 0, 0, 0, 0]

def tiltedLo : Owner → ℚ :=
  ![0, 0, 0, 0, 0, 0,
    Rat.divInt 291702449627 800000000000,
    Rat.divInt 5820333817507 16000000000000,
    Rat.divInt 5838620717551 16000000000000,
    Rat.divInt 363485130781 1000000000000,
    Rat.divInt 579110130781 1600000000000]

def tiltedHi : Owner → ℚ :=
  ![0, 0, 0, 0, 0, 0,
    Rat.divInt 5884337967661 16000000000000,
    Rat.divInt 117595324853 320000000000,
    Rat.divInt 1171381523519 3200000000000,
    Rat.divInt 2930739671303 8000000000000,
    Rat.divInt 117595324853 320000000000]

def localAngleRadius : Owner → ℝ :=
  ![5670363/2500000000, 1764113/1000000000, 5670363/2500000000,
    1890121/1250000000, 20161291/10000000000, 1890121/1250000000,
    35312013/10000000000, 8824483/2500000000, 7549783/5000000000,
    40352153/10000000000, 67647473/10000000000]

theorem localAngleRadius_eq_focused (i : Owner) :
    localAngleRadius i = focusedRadii (coordinate i 2) := by
  fin_cases i <;> rfl

theorem axis_radius_checks (i : Owner) (hi : i.val < 6) :
    2*(axisLowMax i : ℝ) ≤ localAngleRadius i ∧
    2*(1-(axisHighMin i : ℝ))/(1+(axisHighMin i : ℝ)^2) ≤
      localAngleRadius i ∧ 1/2 < (axisHighMin i : ℝ) := by
  fin_cases i <;> first
    | (exfalso; revert hi; decide)
    | norm_num [axisLowMax, axisHighMin, localAngleRadius, Rat.divInt] at hi ⊢

theorem tilted_radius_checks (i : Owner) (hi : 6 ≤ i.val) :
    0 ≤ (tiltedLo i : ℝ) ∧
    2*(rootHi-(tiltedLo i : ℝ))/(1+(tiltedLo i : ℝ)^2) ≤
      localAngleRadius i ∧
    2*((tiltedHi i : ℝ)-rootLo)/(1+rootLo^2) ≤
      localAngleRadius i := by
  fin_cases i <;> first
    | (exfalso; revert hi; decide)
    | norm_num [tiltedLo, tiltedHi, localAngleRadius, rootLo, rootHi, Rat.divInt] at hi ⊢

theorem nearRows_angle_extrema (i : Owner) :
    List.Forall (fun r : NearPoseRow =>
      if i.val < 6 then
        (r.hi ≤ Rat.divInt 1 2 → r.hi ≤ axisLowMax i) ∧
        (Rat.divInt 1 2 ≤ r.lo → axisHighMin i ≤ r.lo)
      else tiltedLo i ≤ r.lo ∧ r.hi ≤ tiltedHi i) (nearRows i) := by
  fin_cases i
  · simpa [nearRows, axisLowMax, axisHighMin] using nearRows0_angle_extrema
  · simpa [nearRows, axisLowMax, axisHighMin] using nearRows1_angle_extrema
  · simpa [nearRows, axisLowMax, axisHighMin] using nearRows2_angle_extrema
  · simpa [nearRows, axisLowMax, axisHighMin] using nearRows3_angle_extrema
  · simpa [nearRows, axisLowMax, axisHighMin] using nearRows4_angle_extrema
  · simpa [nearRows, axisLowMax, axisHighMin] using nearRows5_angle_extrema
  · simpa [nearRows, tiltedLo, tiltedHi] using nearRows6_angle_extrema
  · simpa [nearRows, tiltedLo, tiltedHi] using nearRows7_angle_extrema
  · simpa [nearRows, tiltedLo, tiltedHi] using nearRows8_angle_extrema
  · simpa [nearRows, tiltedLo, tiltedHi] using nearRows9_angle_extrema
  · simpa [nearRows, tiltedLo, tiltedHi] using nearRows10_angle_extrema

/-- The angle representative selected after the case-438 quarter-turn. For
axis roles the two closed half-angle branches differ by one quarter turn of
the same physical square. -/
def nearAngleDisplacement (i : Owner) (t : ℝ) : ℝ :=
  if i.val < 6 then
    if t ≤ 1/2 then 2*Real.arctan t else 2*Real.arctan t-Real.pi/2
  else 2*Real.arctan t-2*Real.arctan u

theorem near_angle_in_focused_radius (i : Owner) (t : ℝ)
    (hrow : ∃ r ∈ nearRows i, (r.lo : ℝ) ≤ t ∧ t ≤ (r.hi : ℝ)) :
    |nearAngleDisplacement i t| ≤ focusedRadii (coordinate i 2) := by
  rw [← localAngleRadius_eq_focused i]
  obtain ⟨r, hr, hlo, hhi⟩ := hrow
  have hv := (List.forall_iff_forall_mem.mp (nearRows_valid i)) r hr
  have he := (List.forall_iff_forall_mem.mp (nearRows_angle_extrema i)) r hr
  obtain ⟨hzero, _, hone, hsplit, _⟩ := hv
  by_cases hi : i.val < 6
  · have hsplit' : r.hi ≤ Rat.divInt 1 2 ∨ Rat.divInt 1 2 ≤ r.lo := by
      simpa [nearAxis, hi] using hsplit
    have he' :
        (r.hi ≤ Rat.divInt 1 2 → r.hi ≤ axisLowMax i) ∧
        (Rat.divInt 1 2 ≤ r.lo → axisHighMin i ≤ r.lo) := by
      simpa [hi] using he
    rcases hsplit' with hlow | hhigh
    · have ht : t ≤ 1/2 := by
        have hq : (r.hi : ℝ) ≤ (Rat.divInt 1 2 : ℝ) := by
          exact_mod_cast hlow
        have hhalf : (Rat.divInt 1 2 : ℝ) = 1/2 := by
          norm_num [Rat.divInt]
        rw [hhalf] at hq
        exact hhi.trans hq
      have h0 : 0 ≤ t :=
        (show (0 : ℝ) ≤ (r.lo : ℝ) by exact_mod_cast hzero).trans hlo
      have hmax : t ≤ (axisLowMax i : ℝ) :=
        hhi.trans (by exact_mod_cast he'.1 hlow)
      change |(if i.val < 6 then
        (if t ≤ 1/2 then 2*Real.arctan t else 2*Real.arctan t-Real.pi/2)
        else 2*Real.arctan t-2*Real.arctan u)| ≤ localAngleRadius i
      rw [if_pos hi, if_pos ht]
      exact angle_near_zero h0 hmax (axis_radius_checks i hi).1
    · have hmin : (axisHighMin i : ℝ) ≤ t :=
        (show (axisHighMin i : ℝ) ≤ (r.lo : ℝ) by
          exact_mod_cast he'.2 hhigh).trans hlo
      have ht : ¬ t ≤ 1/2 := by
        linarith [(axis_radius_checks i hi).2.2]
      have h1 : t ≤ 1 :=
        hhi.trans (by exact_mod_cast hone)
      change |(if i.val < 6 then
        (if t ≤ 1/2 then 2*Real.arctan t else 2*Real.arctan t-Real.pi/2)
        else 2*Real.arctan t-2*Real.arctan u)| ≤ localAngleRadius i
      rw [if_pos hi, if_neg ht]
      exact angle_near_quarter (le_of_lt (by
        linarith [(axis_radius_checks i hi).2.2]))
        hmin h1 (axis_radius_checks i hi).2.1
  · have he' : tiltedLo i ≤ r.lo ∧ r.hi ≤ tiltedHi i := by
      simpa [hi] using he
    have hlow : (tiltedLo i : ℝ) ≤ t :=
      (show (tiltedLo i : ℝ) ≤ (r.lo : ℝ) by exact_mod_cast he'.1).trans hlo
    have hhigh : t ≤ (tiltedHi i : ℝ) :=
      hhi.trans (by exact_mod_cast he'.2)
    have hn := tilted_radius_checks i (Nat.le_of_not_lt hi)
    simpa [nearAngleDisplacement, hi] using
      angle_near_tilted hn.1 (by norm_num [rootLo])
        hlow hhigh u_bounds.1.le u_bounds.2.le hn.2.1 hn.2.2

end
end ElevenSquare.Tasks.T07
