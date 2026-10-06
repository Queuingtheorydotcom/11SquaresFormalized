import ElevenSquare.Tasks.T07.NearCaptureRectangle
import ElevenSquare.Pending.S05_Trace

/-! A native `PoseState` interface for the frozen final near domains. Its rows
retain each exact source angular interval and enlarge every residual center
polygon to its kernel-checked rational enclosing box. This enlargement is
sufficient for the focused rectangle, and permits trace composition through
`StateHolds` without assuming convex-polygon membership from box membership. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def nearScaleQ : ℚ :=
  Rat.divInt 382000000000000000000 387708359002281417731

theorem nearScaleQ_cast : (nearScaleQ : ℝ) = fieldScale := by
  norm_num [nearScaleQ, fieldScale, coverCap, Rat.divInt]

def nearBoxPlanes (b : NearRatRect) : Polygon :=
  [{a := -nearScaleQ, b := 0, c := -b.lx},
   {a := nearScaleQ, b := 0, c := b.hx},
   {a := 0, b := -nearScaleQ, c := -b.ly},
   {a := 0, b := nearScaleQ, c := b.hy}]

theorem nearBoxPlanes_iff (b : NearRatRect) (p : Point) :
    p ∈ (nearBoxPlanes b).carrier ↔
      inRect (b.lx : ℝ) (b.hx : ℝ) (b.ly : ℝ) (b.hy : ℝ) (toField p) := by
  simp only [Polygon.carrier, Set.mem_setOf_eq, nearBoxPlanes, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Halfplane.contains]
  simp only [Rat.cast_neg, Rat.cast_zero, nearScaleQ_cast, zero_mul, add_zero,
    zero_add, toField, inRect]
  constructor
  · rintro ⟨hxl, hxh, hyl, hyh⟩
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨hxl, hxh, hyl, hyh⟩
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

def nearOuterRow (i : Owner) (r : NearPoseRow) : PoseRow :=
  { lo := r.lo, hi := r.hi, centers := nearBoxPlanes (nearFieldBox i) }

def nearOuterState : PoseState where
  rows i := (nearRows i).map (nearOuterRow i)
  owned _ := []

def FinalNearBoxRowsHold (Q : Packing 11 coverCap) : Prop :=
  ∀ i : Owner, ∃ r ∈ nearRows i, ∃ t : ℝ,
    0 ≤ t ∧ t ≤ 1 ∧ (r.lo : ℝ) ≤ t ∧ t ≤ (r.hi : ℝ) ∧
    (Q.squares i).axis = chartAxis t ∧
    inRect ((nearFieldBox i).lx : ℝ) ((nearFieldBox i).hx : ℝ)
      ((nearFieldBox i).ly : ℝ) ((nearFieldBox i).hy : ℝ)
      (toField (Q.squares i).center)

theorem finalNearRows_to_boxRows (Q : Packing 11 coverCap)
    (hfinal : FinalNearRowsHold Q) : FinalNearBoxRowsHold Q := by
  intro i
  obtain ⟨r, hr, t, ht0, ht1, htlo, hthi, haxis, P, hP, hpoly⟩ := hfinal i
  exact ⟨r, hr, t, ht0, ht1, htlo, hthi, haxis,
    finalNear_center_field_enclosure i _ ⟨r, hr, P, hP, hpoly⟩⟩

theorem nearOuterState_iff (Q : Packing 11 coverCap) :
    StateHolds Q nearOuterState ↔ FinalNearBoxRowsHold Q := by
  constructor
  · intro hs i
    obtain ⟨r, hr, hcontains⟩ := hs.1 i
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    obtain ⟨hcenter, t, ht0, ht1, htlo, hthi, haxis⟩ := hcontains
    exact ⟨r', hr', t, ht0, ht1, htlo, hthi, haxis,
      (nearBoxPlanes_iff (nearFieldBox i) (Q.squares i).center).mp hcenter⟩
  · intro hbox
    constructor
    · intro i
      obtain ⟨r, hr, t, ht0, ht1, htlo, hthi, haxis, hc⟩ := hbox i
      refine ⟨nearOuterRow i r, List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
      exact ⟨(nearBoxPlanes_iff (nearFieldBox i) (Q.squares i).center).mpr hc,
        t, ht0, ht1, htlo, hthi, haxis⟩
    · intro i
      simp [nearOuterState, rationalHull]

theorem finalNearRows_to_outerState (Q : Packing 11 coverCap)
    (hfinal : FinalNearRowsHold Q) : StateHolds Q nearOuterState :=
  (nearOuterState_iff Q).mpr (finalNearRows_to_boxRows Q hfinal)

/-- A source trace may retain its promoted owned hulls. Only outer row
inclusion is needed to hand it to the near packet. The concrete final-state
rows can be checked against this relation independently of ownership. -/
def NearRowsSubsumed (s : PoseState) : Prop :=
  ∀ i : Owner, ∀ q : UnitSquare,
    RowsContain (s.rows i) q → RowsContain (nearOuterState.rows i) q

theorem stateHolds_nearOuterState_of_subsumed (Q : Packing 11 coverCap)
    (s : PoseState) (hs : StateHolds Q s) (hsub : NearRowsSubsumed s) :
    StateHolds Q nearOuterState := by
  constructor
  · intro i
    exact hsub i (Q.squares i) (hs.1 i)
  · intro i
    simp [nearOuterState, rationalHull]

theorem nearOuterState_rows_subsumed (s : PoseState)
    (hrows : ∀ i, s.rows i = nearOuterState.rows i) :
    NearRowsSubsumed s := by
  intro i q hq
  simpa only [hrows i] using hq

/-- A row-wise finite check suitable for an independently generated trace
state. Source rows may split angular intervals; their entire center carriers
must lie in the appropriate rational field box. -/
def NearFiniteRowEnclosure (s : PoseState) : Prop :=
  ∀ i : Owner, ∀ r ∈ s.rows i,
    ∃ nr ∈ nearRows i,
      (nr.lo : ℝ) ≤ (r.lo : ℝ) ∧ (r.hi : ℝ) ≤ (nr.hi : ℝ) ∧
      ∀ p ∈ r.centers.carrier,
        inRect ((nearFieldBox i).lx : ℝ) ((nearFieldBox i).hx : ℝ)
          ((nearFieldBox i).ly : ℝ) ((nearFieldBox i).hy : ℝ) (toField p)

theorem nearFiniteRowEnclosure_subsumed (s : PoseState)
    (hrows : NearFiniteRowEnclosure s) : NearRowsSubsumed s := by
  intro i q hq
  obtain ⟨r, hr, hcenter, t, ht0, ht1, htlo, hthi, haxis⟩ := hq
  obtain ⟨nr, hnr, hlo, hhi, hc⟩ := hrows i r hr
  refine ⟨nearOuterRow i nr, List.mem_map.mpr ⟨nr, hnr, rfl⟩, ?_⟩
  exact ⟨(nearBoxPlanes_iff (nearFieldBox i) q.center).mpr (hc q.center hcenter),
    t, ht0, ht1, le_trans hlo htlo, le_trans hthi hhi, haxis⟩

theorem nearOuterState_finiteRowEnclosure :
    NearFiniteRowEnclosure nearOuterState := by
  intro i r hr
  obtain ⟨nr, hnr, rfl⟩ := List.mem_map.mp hr
  refine ⟨nr, hnr, le_refl _, le_refl _, ?_⟩
  intro p hp
  exact (nearBoxPlanes_iff (nearFieldBox i) p).mp hp

/-- The final source's rational outer boxes alone suffice for all 22 center
bounds. This stronger interface can consume a native trace state whose center
rows use halfplanes, without requiring an exact convex polygon membership. -/
theorem nearBox_center_in_focused_radii (i : Owner) (p : Point)
    (hp : inRect ((nearFieldBox i).lx : ℝ) ((nearFieldBox i).hx : ℝ)
      ((nearFieldBox i).ly : ℝ) ((nearFieldBox i).hy : ℝ) p) :
    |(fieldToLocal p).1-(constructionCenter i).1| ≤
      focusedRadii (coordinate i (0 : Fin 3)) ∧
    |(fieldToLocal p).2-(constructionCenter i).2| ≤
      focusedRadii (coordinate i (1 : Fin 3)) := by
  fin_cases i
  · have hb : inRect (nearBox0.lx : ℝ) (nearBox0.hx : ℝ)
        (nearBox0.ly : ℝ) (nearBox0.hy : ℝ) p := by
      simpa [nearFieldBox] using hp
    rcases nearCenterBox0_numeric with ⟨hxl, hxr, hyl, hyr⟩
    exact ⟨field_rectangle_local_x hb nearCenter00_bounds hxl hxr,
      field_rectangle_local_y hb nearCenter01_bounds hyl hyr⟩
  · have hb : inRect (nearBox1.lx : ℝ) (nearBox1.hx : ℝ)
        (nearBox1.ly : ℝ) (nearBox1.hy : ℝ) p := by
      simpa [nearFieldBox] using hp
    rcases nearCenterBox1_numeric with ⟨hxl, hxr, hyl, hyr⟩
    exact ⟨field_rectangle_local_x hb nearCenter10_bounds hxl hxr,
      field_rectangle_local_y hb nearCenter11_bounds hyl hyr⟩
  · have hb : inRect (nearBox2.lx : ℝ) (nearBox2.hx : ℝ)
        (nearBox2.ly : ℝ) (nearBox2.hy : ℝ) p := by
      simpa [nearFieldBox] using hp
    rcases nearCenterBox2_numeric with ⟨hxl, hxr, hyl, hyr⟩
    exact ⟨field_rectangle_local_x hb nearCenter20_bounds hxl hxr,
      field_rectangle_local_y hb nearCenter21_bounds hyl hyr⟩
  · have hb : inRect (nearBox3.lx : ℝ) (nearBox3.hx : ℝ)
        (nearBox3.ly : ℝ) (nearBox3.hy : ℝ) p := by
      simpa [nearFieldBox] using hp
    rcases nearCenterBox3_numeric with ⟨hxl, hxr, hyl, hyr⟩
    exact ⟨field_rectangle_local_x hb nearCenter30_bounds hxl hxr,
      field_rectangle_local_y hb nearCenter31_bounds hyl hyr⟩
  · have hb : inRect (nearBox4.lx : ℝ) (nearBox4.hx : ℝ)
        (nearBox4.ly : ℝ) (nearBox4.hy : ℝ) p := by
      simpa [nearFieldBox] using hp
    rcases nearCenterBox4_numeric with ⟨hxl, hxr, hyl, hyr⟩
    exact ⟨field_rectangle_local_x hb nearCenter40_bounds hxl hxr,
      field_rectangle_local_y hb nearCenter41_bounds hyl hyr⟩
  · have hb : inRect (nearBox5.lx : ℝ) (nearBox5.hx : ℝ)
        (nearBox5.ly : ℝ) (nearBox5.hy : ℝ) p := by
      simpa [nearFieldBox] using hp
    rcases nearCenterBox5_numeric with ⟨hxl, hxr, hyl, hyr⟩
    exact ⟨field_rectangle_local_x hb nearCenter50_bounds hxl hxr,
      field_rectangle_local_y hb nearCenter51_bounds hyl hyr⟩
  · have hb : inRect (nearBox6.lx : ℝ) (nearBox6.hx : ℝ)
        (nearBox6.ly : ℝ) (nearBox6.hy : ℝ) p := by
      simpa [nearFieldBox] using hp
    rcases nearCenterBox6_numeric with ⟨hxl, hxr, hyl, hyr⟩
    exact ⟨field_rectangle_local_x hb nearCenter60_bounds hxl hxr,
      field_rectangle_local_y hb nearCenter61_bounds hyl hyr⟩
  · have hb : inRect (nearBox7.lx : ℝ) (nearBox7.hx : ℝ)
        (nearBox7.ly : ℝ) (nearBox7.hy : ℝ) p := by
      simpa [nearFieldBox] using hp
    rcases nearCenterBox7_numeric with ⟨hxl, hxr, hyl, hyr⟩
    exact ⟨field_rectangle_local_x hb nearCenter70_bounds hxl hxr,
      field_rectangle_local_y hb nearCenter71_bounds hyl hyr⟩
  · have hb : inRect (nearBox8.lx : ℝ) (nearBox8.hx : ℝ)
        (nearBox8.ly : ℝ) (nearBox8.hy : ℝ) p := by
      simpa [nearFieldBox] using hp
    rcases nearCenterBox8_numeric with ⟨hxl, hxr, hyl, hyr⟩
    exact ⟨field_rectangle_local_x hb nearCenter80_bounds hxl hxr,
      field_rectangle_local_y hb nearCenter81_bounds hyl hyr⟩
  · have hb : inRect (nearBox9.lx : ℝ) (nearBox9.hx : ℝ)
        (nearBox9.ly : ℝ) (nearBox9.hy : ℝ) p := by
      simpa [nearFieldBox] using hp
    rcases nearCenterBox9_numeric with ⟨hxl, hxr, hyl, hyr⟩
    exact ⟨field_rectangle_local_x hb nearCenter90_bounds hxl hxr,
      field_rectangle_local_y hb nearCenter91_bounds hyl hyr⟩
  · have hb : inRect (nearBox10.lx : ℝ) (nearBox10.hx : ℝ)
        (nearBox10.ly : ℝ) (nearBox10.hy : ℝ) p := by
      simpa [nearFieldBox] using hp
    rcases nearCenterBox10_numeric with ⟨hxl, hxr, hyl, hyr⟩
    exact ⟨field_rectangle_local_x hb nearCenter100_bounds hxl hxr,
      field_rectangle_local_y hb nearCenter101_bounds hyl hyr⟩

end
end ElevenSquare.Tasks.T07
