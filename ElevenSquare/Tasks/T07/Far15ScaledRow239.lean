import ElevenSquare.Tasks.T07.Far15ScaledData

/-! Correct field-scale certificate for far-y step-7 row 239. The slanted
halfplane retains the x-y correlation lost by an axis-aligned rectangle. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section
set_option maxHeartbeats 0

def far15Row239Vertices : List QPoint :=
  [ (Rat.divInt 55626251 100000000, Rat.divInt 248727911 100000000),
    (Rat.divInt 55626251 100000000, Rat.divInt 125900371 50000000),
    (Rat.divInt 24945327 50000000, Rat.divInt 257536339 100000000),
    (Rat.divInt 49890653 100000000, Rat.divInt 128768169 50000000),
    (Rat.divInt 49890653 100000000, Rat.divInt 61646807 25000000),
    (Rat.divInt 4993497 10000000, Rat.divInt 246542911 100000000),
    (Rat.divInt 53441251 100000000, Rat.divInt 246542911 100000000) ]

private theorem fieldScale_gt_985 : (985/1000 : ℝ) < fieldScale := by
  norm_num [fieldScale, coverCap]

private theorem far15_row239_slanted_vertices :
    ∀ v ∈ far15Row239Vertices,
      (v.1/80+v.2 : ℚ) ≤
        far15Owner9Witness.1/80 + far15Owner9Witness.2 + 4925/10000 := by
  intro v hv
  simp only [far15Row239Vertices, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [far15Owner9Witness, Rat.divInt]

private theorem far15_row239_slanted_hull {p : Point}
    (hp : p ∈ rationalHull far15Row239Vertices) :
    p.1/80+p.2 ≤
      (far15Owner9Witness.1 : ℝ)/80 +
      (far15Owner9Witness.2 : ℝ) + 4925/10000 := by
  let L : Point → ℝ := fun p => p.1/80+p.2
  have hlin : IsLinearMap ℝ L := by
    constructor
    · intro x y
      dsimp [L]
      ring
    · intro a x
      dsimp [L]
      ring
  let H : Set Point := {p | L p ≤
    (far15Owner9Witness.1 : ℝ)/80 +
    (far15Owner9Witness.2 : ℝ) + 4925/10000}
  have hconv : Convex ℝ H := convex_halfSpace_le hlin _
  have hbase : {p : Point | ∃ v ∈ far15Row239Vertices,
      p = realPoint v} ⊆ H := by
    rintro p ⟨v, hv, rfl⟩
    have h := far15_row239_slanted_vertices v hv
    have h' : (((v.1/80+v.2 : ℚ) : ℝ)) ≤
        (((far15Owner9Witness.1/80 + far15Owner9Witness.2 +
          4925/10000 : ℚ) : ℝ)) := by exact_mod_cast h
    change (v.1 : ℝ)/80+(v.2 : ℝ) ≤
      (far15Owner9Witness.1 : ℝ)/80 +
      (far15Owner9Witness.2 : ℝ) + 4925/10000
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using h'
  exact convexHull_min hbase hconv hp

private theorem far15_row239_box_vertices :
    ∀ v ∈ far15Row239Vertices,
      (498/1000 : ℚ) ≤ v.1 ∧ v.1 ≤ 557/1000 ∧
      (2465/1000 : ℚ) ≤ v.2 ∧ v.2 ≤ 2576/1000 := by
  intro v hv
  simp only [far15Row239Vertices, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [Rat.divInt]

private theorem far15_row239_box_hull {p : Point}
    (hp : p ∈ rationalHull far15Row239Vertices) :
    (498/1000 : ℝ) ≤ p.1 ∧ p.1 ≤ 557/1000 ∧
    (2465/1000 : ℝ) ≤ p.2 ∧ p.2 ≤ 2576/1000 := by
  let box : Set Point := {p |
    (498/1000 : ℝ) ≤ p.1 ∧ p.1 ≤ 557/1000 ∧
    (2465/1000 : ℝ) ≤ p.2 ∧ p.2 ≤ 2576/1000}
  have hconv : Convex ℝ box := by
    have hs : box = (Set.Icc (498/1000 : ℝ) (557/1000) ×ˢ
        Set.Icc (2465/1000 : ℝ) (2576/1000)) := by
      ext p
      simp only [box, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc]
      tauto
    rw [hs]
    exact (convex_Icc _ _).prod (convex_Icc _ _)
  have hbase : {p : Point | ∃ v ∈ far15Row239Vertices,
      p = realPoint v} ⊆ box := by
    rintro p ⟨v, hv, rfl⟩
    obtain ⟨h1,h2,h3,h4⟩ := far15_row239_box_vertices v hv
    have h1' : (((498/1000 : ℚ) : ℝ)) ≤ (v.1 : ℝ) := by exact_mod_cast h1
    have h2' : (v.1 : ℝ) ≤ (((557/1000 : ℚ) : ℝ)) := by exact_mod_cast h2
    have h3' : (((2465/1000 : ℚ) : ℝ)) ≤ (v.2 : ℝ) := by exact_mod_cast h3
    have h4' : (v.2 : ℝ) ≤ (((2576/1000 : ℚ) : ℝ)) := by exact_mod_cast h4
    change (498/1000 : ℝ) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) ≤ 557/1000 ∧
      (2465/1000 : ℝ) ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) ≤ 2576/1000
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (show (((498/1000 : ℚ) : ℝ)) ≤ (v.1 : ℝ) ∧
        (v.1 : ℝ) ≤ (((557/1000 : ℚ) : ℝ)) ∧
        (((2465/1000 : ℚ) : ℝ)) ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) ≤ (((2576/1000 : ℚ) : ℝ)) from
        ⟨h1',h2',h3',h4'⟩)
  exact convexHull_min hbase hconv hp

theorem far15_scaled_row239_collision (q : UnitSquare) (pField : Point)
    (hc : pField ∈ rationalHull far15Row239Vertices)
    (hcenter : q.center = (pField.1/fieldScale,pField.2/fieldScale))
    (ha : ∃ t : ℝ, (63/64 : ℝ) ≤ t ∧
      t ≤ 125613/127232 ∧ q.axis = chartAxis t) :
    OpenSquare q far15PhysicalWitness := by
  obtain ⟨hlx,hhx,hly,hhy⟩ := far15_row239_box_hull hc
  have hslant := far15_row239_slanted_hull hc
  obtain ⟨t,htlo,hthi,haxis⟩ := ha
  let dx : ℝ := (far15Owner9Witness.1 : ℝ) - pField.1
  let d : ℝ := pField.2 - (far15Owner9Witness.2 : ℝ)
  let c : ℝ := (chartAxis t).1
  let s : ℝ := (chartAxis t).2
  have hden : 0 < 1+t^2 := by positivity
  have htloSq : (63/64 : ℝ)^2 ≤ t^2 := by
    nlinarith [mul_nonneg (show 0 ≤ t-63/64 by linarith)
      (show 0 ≤ t+63/64 by linarith)]
  have hthiSq : t^2 ≤ (125613/127232 : ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 125613/127232-t by linarith)
      (show 0 ≤ 125613/127232+t by linarith)]
  have hc0 : 0 ≤ c := by
    dsimp [c,chartAxis]
    exact div_nonneg (by nlinarith) (le_of_lt hden)
  have hcLo : (1/80 : ℝ) ≤ c := by
    dsimp [c,chartAxis]
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hcHi : c ≤ 1/50 := by
    dsimp [c,chartAxis]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hs0 : 0 ≤ s := by
    dsimp [s,chartAxis]
    exact div_nonneg (by linarith) (le_of_lt hden)
  have hsHi : s ≤ 1 := by
    dsimp [s,chartAxis]
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg (t-1)]
  have hdx : 0 ≤ dx ∧ dx ≤ 43/100 := by
    dsimp [dx,far15Owner9Witness]
    norm_num at hlx hhx ⊢
    constructor <;> linarith
  have hd : 0 ≤ d ∧ d ≤ 499/1000 := by
    dsimp [d,far15Owner9Witness]
    norm_num at hly hhy ⊢
    constructor <;> linarith
  have hslant' : d-dx/80 ≤ (4925/10000 : ℝ) := by
    dsimp [d,dx]
    linarith [hslant]
  have hdxCLo : dx/80 ≤ dx*c := by
    have h := mul_le_mul_of_nonneg_left hcLo hdx.1
    convert h using 1 <;> ring
  have hdxCHi : dx*c ≤ (43/100 : ℝ)*(1/50) :=
    mul_le_mul hdx.2 hcHi hc0 (by norm_num)
  have hds0 : 0 ≤ d*s := mul_nonneg hd.1 hs0
  have hdsHi : d*s ≤ d := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hsHi hd.1
  have hxs0 : 0 ≤ dx*s := mul_nonneg hdx.1 hs0
  have hxsHi : dx*s ≤ (43/100 : ℝ)*1 :=
    mul_le_mul hdx.2 hsHi hs0 (by norm_num)
  have hdc0 : 0 ≤ d*c := mul_nonneg hd.1 hc0
  have hdcHi : d*c ≤ (499/1000 : ℝ)*(1/50) :=
    mul_le_mul hd.2 hcHi hc0 (by norm_num)
  have hx : |dx*c-d*s| < fieldScale/2 := by
    apply abs_lt.mpr
    have hlo : -(fieldScale/2) < -(4925/10000 : ℝ) := by
      linarith [fieldScale_gt_985]
    have hbound : -(4925/10000 : ℝ) ≤ dx*c-d*s := by
      have h₁ : -(4925/10000 : ℝ) ≤ dx/80-d := by linarith [hslant']
      have h₂ : dx/80-d ≤ dx*c-d*s := sub_le_sub hdxCLo hdsHi
      exact le_trans h₁ h₂
    have hright : dx*c-d*s ≤ dx*c := by
      simpa only [sub_eq_add_neg, add_zero] using
        (add_le_add le_rfl (neg_nonpos.mpr hds0))
    refine ⟨lt_of_lt_of_le hlo hbound, lt_of_le_of_lt hright ?_⟩
    exact lt_of_le_of_lt hdxCHi (by linarith [fieldScale_gt_985])
  have hy : |dx*(-s)-d*c| < fieldScale/2 := by
    have hsum0 : 0 ≤ dx*s+d*c := add_nonneg hxs0 hdc0
    have hsum : dx*s+d*c < fieldScale/2 :=
      lt_of_le_of_lt (add_le_add hxsHi hdcHi)
        (by linarith [fieldScale_gt_985])
    calc
      |dx*(-s)-d*c| = |-(dx*s+d*c)| := by congr 1; ring
      _ = |dx*s+d*c| := abs_neg _
      _ < fieldScale/2 := by rwa [abs_of_nonneg hsum0]
  have hlocalX : localX q far15PhysicalWitness =
      (dx*c-d*s)/fieldScale := by
    dsimp [localX,dot,far15PhysicalWitness]
    rw [hcenter,haxis]
    dsimp [dx,d,c,s]
    field_simp [fieldScale_ne_zero] <;> ring
  have hlocalY : localY q far15PhysicalWitness =
      (dx*(-s)-d*c)/fieldScale := by
    dsimp [localY,dot,perp,far15PhysicalWitness]
    rw [hcenter,haxis]
    dsimp [dx,d,c,s]
    field_simp [fieldScale_ne_zero] <;> ring
  rw [OpenSquare,hlocalX,hlocalY]
  constructor
  · rw [abs_div,abs_of_pos fieldScale_pos]
    exact (div_lt_iff₀ fieldScale_pos).mpr (by linarith [hx])
  · rw [abs_div,abs_of_pos fieldScale_pos]
    exact (div_lt_iff₀ fieldScale_pos).mpr (by linarith [hy])

theorem far15_scaled_row239_excluded {S : ℝ} (P : Packing 11 S)
    (st : PoseState) (hstate : StateHolds P st)
    (howned : far15PhysicalWitness ∈
      rationalHull (st.owned ⟨6, by decide⟩))
    (pField : Point) (hc : pField ∈ rationalHull far15Row239Vertices)
    (hcenter : (P.squares ⟨5, by decide⟩).center =
      (pField.1/fieldScale,pField.2/fieldScale))
    (ha : ∃ t : ℝ, (63/64 : ℝ) ≤ t ∧ t ≤ 125613/127232 ∧
      (P.squares ⟨5, by decide⟩).axis = chartAxis t) : False := by
  have hother := hstate.2 ⟨6, by decide⟩ howned
  have htarget := far15_scaled_row239_collision
    (P.squares ⟨5, by decide⟩) pField hc hcenter ha
  exact P.interior_disjoint ⟨5, by decide⟩ ⟨6, by decide⟩
    (by decide) far15PhysicalWitness ⟨htarget,hother⟩

end
end ElevenSquare.Tasks.T07
