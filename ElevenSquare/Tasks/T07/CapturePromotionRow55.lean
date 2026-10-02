import ElevenSquare.Tasks.T07.CaptureAxisBounds
import ElevenSquare.Tasks.T07.CapturePolygon
import ElevenSquare.Tasks.T07.CoordinateBridge
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Cast.Order

/-! One exact finite inequality for all fifteen vertices of the first
surviving owner-9 pose row in far15 step 5. It is a candidate input to
a full promotion proof, not a trace certificate by itself. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def step5Row55Vertices : List QPoint :=
  [
    (4221228680984950801937156171062608452142453132603504257968006968966330859625493837900518112611/2694452797142927235742160115865636559931371563218922887884673461749935743035369428000000000000, 2624072379171026168766324106604827901746651603483700015561842966752067275539567510822266396213/1347226398571463617871080057932818279965685781609461443942336730874967871517684714000000000000),
    (976511017461869923973142247100346354441346756526478265563960505359727824762181109562473397/628006866885279797576629736594677039652116255927682002283045717858139555730346000000000000, 383981680897203077735573724481998023071064065707273778840640615007959113677573758098171203957/195310135601322017046331848080944559331808155593509102710027218253881401832137606000000000000),
    (67049976970055597428396430845292904366591468420705116670553899798592119241321704510465151718017581880015710857641291456746131/42817150002579274273349627600697859127360536738417476016524945512436464395394246714462993548214203560226634301158000000000000, 83380383265338187649266292059220428827919672561509717108553472349963162196106189152997349488034588927622176740536555335794611/42817150002579274273349627600697859127360536738417476016524945512436464395394246714462993548214203560226634301158000000000000),
    (13434738208023024510375043908260923871661824413690750722495076893956940897257872625441329361429629073919336088446972712446647/8563236141337264546536964260458038111442626960505155075879907565122269906181303334721235781611316982193386517550000000000000, 83166625392343868734940077281632952787492552621024922556883594060418272463639977749526779779523869640451581177802998013873331/42816180706686322732684821302290190557213134802525775379399537825611349530906516673606178908056584910966932587750000000000000),
    (384599818087879185371327750590385828190786664154031726594225297455005108851964078363781746697/245009072907229805353222694586333339406935362671783481462232566732573623820947964000000000000, 238016848376618484907102510974351337728395849250122657388534720195108481302821452909328164927/122504536453614902676611347293166669703467681335891740731116283366286811910473982000000000000),
    (4221228680984950801937156171062608452142453132603504257968006968966330859625493837900518112611/2694452797142927235742160115865636559931371563218922887884673461749935743035369428000000000000, 2624072379171026168766324106604827901746651603483700015561842966752067275539567510822266396213/1347226398571463617871080057932818279965685781609461443942336730874967871517684714000000000000),
    (67049976970055597428396430845292904366591468420705116670553899798592119241321704510465151718017581880015710857641291456746131/42817150002579274273349627600697859127360536738417476016524945512436464395394246714462993548214203560226634301158000000000000, 83380383265338187649266292059220428827919672561509717108553472349963162196106189152997349488034588927622176740536555335794611/42817150002579274273349627600697859127360536738417476016524945512436464395394246714462993548214203560226634301158000000000000),
    (3183496450653355933818667504361049783254302767958533580188507355841981795746693/2028385337535946152198449563675411897358088541649926995470373287754000000000000, 3937941874428409811819346655848203648668330025137799437919490338697714080293307/2028385337535946152198449563675411897358088541649926995470373287754000000000000),
    (69728995930754320182005683386042958392851319206283/44386663454519776788536543472597340586000000000000, 86107708465617117122241346745965621572438773153717/44386663454519776788536543472597340586000000000000),
    (694831374268949418809459940602515692450486813661147217497/442160135959138735410046464984541523080889374000000000000, 857903313777612485154300604440348961837717076943873913969/442160135959138735410046464984541523080889374000000000000),
    (384599818087879185371327750590385828190786664154031726594225297455005108851964078363781746697/245009072907229805353222694586333339406935362671783481462232566732573623820947964000000000000, 238016848376618484907102510974351337728395849250122657388534720195108481302821452909328164927/122504536453614902676611347293166669703467681335891740731116283366286811910473982000000000000),
    (13434738208023024510375043908260923871661824413690750722495076893956940897257872625441329361429629073919336088446972712446647/8563236141337264546536964260458038111442626960505155075879907565122269906181303334721235781611316982193386517550000000000000, 83166625392343868734940077281632952787492552621024922556883594060418272463639977749526779779523869640451581177802998013873331/42816180706686322732684821302290190557213134802525775379399537825611349530906516673606178908056584910966932587750000000000000),
    (69728995930754320182005683386042958392851319206283/44386663454519776788536543472597340586000000000000, 86107708465617117122241346745965621572438773153717/44386663454519776788536543472597340586000000000000),
    (344919323682028881631224531327089046002231832767/219289159364081328052461998865622510000000000000, 424980850052912046876029069510356073193520767233/219289159364081328052461998865622510000000000000),
    (694831374268949418809459940602515692450486813661147217497/442160135959138735410046464984541523080889374000000000000, 857903313777612485154300604440348961837717076943873913969/442160135959138735410046464984541523080889374000000000000)
  ]

def step5Owner9Witness : QPoint :=
  (45936839/50000000, 103898071/50000000)

def step5Row55C : ℚ :=
  (1-(35/128 : ℚ)^2)/(1+(35/128 : ℚ)^2)

def step5Row55S : ℚ :=
  (2*(35/128 : ℚ))/(1+(35/128 : ℚ)^2)

/-- Half the side of a unit square expressed in archived field coordinates. -/
def step5FieldHalf : ℚ :=
  191000000000000000000 / 387708359002281417731

theorem step5FieldHalf_eq : (step5FieldHalf : ℝ) = fieldScale/2 := by
  norm_num [step5FieldHalf, fieldScale, coverCap]

/-- The active local-X inequality has a strict margin at every source vertex;
linearity then extends this part of the bound to the entire convex polygon. -/
theorem step5_row55_vertices_strict :
    ∀ v ∈ step5Row55Vertices,
      (v.1-step5Owner9Witness.1)*step5Row55C -
        (step5Owner9Witness.2-v.2)*step5Row55S < step5FieldHalf := by
  intro v hv
  simp only [step5Row55Vertices, List.mem_cons, List.not_mem_nil,
    or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [step5Owner9Witness, step5Row55C, step5Row55S, step5FieldHalf]

theorem step5_row55_hull_strict {p : Point}
    (hp : p ∈ rationalHull step5Row55Vertices) :
    (p.1-(realPoint step5Owner9Witness).1)*(step5Row55C : ℝ) -
      ((realPoint step5Owner9Witness).2-p.2)*(step5Row55S : ℝ) < fieldScale/2 := by
  let c : ℝ := step5Row55C
  let s : ℝ := step5Row55S
  let w : Point := realPoint step5Owner9Witness
  let f : Point → ℝ := fun p => c*p.1+s*p.2
  have hf : IsLinearMap ℝ f := by
    constructor
    · intro x y
      dsimp [f, Prod.fst_add, Prod.snd_add]
      ring
    · intro a x
      rcases x with ⟨x, y⟩
      change c*(a*x)+s*(a*y) = a*(c*x+s*y)
      ring
  let C : Set Point := {p | f p < fieldScale/2+c*w.1+s*w.2}
  have hconv : Convex ℝ C := convex_halfSpace_lt hf _
  have hbase : {p : Point | ∃ v ∈ step5Row55Vertices,
      p = realPoint v} ⊆ C := by
    rintro p ⟨v, hv, rfl⟩
    have h := step5_row55_vertices_strict v hv
    have hreal :
        (((v.1-step5Owner9Witness.1)*step5Row55C -
          (step5Owner9Witness.2-v.2)*step5Row55S : ℚ) : ℝ) <
          (step5FieldHalf : ℝ) := Rat.cast_lt.mpr h
    push_cast at hreal
    rw [step5FieldHalf_eq] at hreal
    dsimp [C, f, c, s, w, realPoint]
    linarith
  have hresult := (convexHull_min hbase hconv) hp
  dsimp [C, f, c, s, w] at hresult
  linarith

theorem step5_row55_vertices_box :
    ∀ v ∈ step5Row55Vertices,
      (155/100 : ℚ) ≤ v.1 ∧ v.1 ≤ 158/100 ∧
      (193/100 : ℚ) ≤ v.2 ∧ v.2 ≤ 197/100 := by
  intro v hv
  simp only [step5Row55Vertices, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num

/-- A genuine continuous source-domain fact for one retained far15 row:
every center in the complete convex hull and every angle in its closed
interval owns the new grid witness. -/
theorem step5_row55_witness_inside (q : UnitSquare)
    (hc : toField q.center ∈ rationalHull step5Row55Vertices)
    (ht : ∃ t : ℝ, 35/128 ≤ t ∧ t ≤ 71/256 ∧ q.axis = chartAxis t) :
    OpenSquare q
      ((realPoint step5Owner9Witness).1/fieldScale,
        (realPoint step5Owner9Witness).2/fieldScale) := by
  obtain ⟨t, htlo, hthi, haxis⟩ := ht
  let w : Point := realPoint step5Owner9Witness
  let dx : ℝ := (toField q.center).1-w.1
  let dy : ℝ := w.2-(toField q.center).2
  let c : ℝ := (chartAxis t).1
  let s : ℝ := (chartAxis t).2
  have hbox := hull_coordinate_bounds step5Row55Vertices
    (155/100) (158/100) (193/100) (197/100)
    step5_row55_vertices_box hc
  have hdx0 : 0 ≤ dx := by
    dsimp [dx, w, realPoint, step5Owner9Witness]
    norm_num at hbox ⊢
    linarith
  have hdy0 : 0 ≤ dy := by
    dsimp [dy, w, realPoint, step5Owner9Witness]
    norm_num at hbox ⊢
    linarith
  have hdx : dx ≤ 67/100 := by
    dsimp [dx, w, realPoint, step5Owner9Witness]
    norm_num at hbox ⊢
    linarith
  have hdy : dy ≤ 15/100 := by
    dsimp [dy, w, realPoint, step5Owner9Witness]
    norm_num at hbox ⊢
    linarith
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by linarith
  have hc0 : 0 ≤ c := by
    have h := chartAxis_first_antitone ht0 hthi
    dsimp [c] at *
    nlinarith only [h,
      show 0 ≤ (chartAxis (71/256 : ℝ)).1 by norm_num [chartAxis]]
  have hs0 : 0 ≤ s := by
    have h := chartAxis_second_monotone (by norm_num : (0:ℝ) ≤ 0) ht0 ht1
    simpa [s, chartAxis] using h
  have hcub : c ≤ 87/100 := by
    have h := chartAxis_first_antitone (by norm_num : (0:ℝ) ≤ 35/128) htlo
    exact (show c ≤ (chartAxis (35/128 : ℝ)).1 from h).trans
      (by norm_num [chartAxis])
  have hsub : s ≤ 13/25 := by
    have h := chartAxis_second_monotone ht0 hthi
      (by norm_num : (71/256 : ℝ) ≤ 1)
    exact (show s ≤ (chartAxis (71/256 : ℝ)).2 from h).trans
      (by norm_num [chartAxis])
  have hcl : c ≤ (chartAxis (35/128 : ℝ)).1 :=
    chartAxis_first_antitone (by norm_num) htlo
  have hsl : (chartAxis (35/128 : ℝ)).2 ≤ s :=
    chartAxis_second_monotone (by norm_num) htlo ht1
  have hsource := step5_row55_hull_strict hc
  have hcdef : (step5Row55C : ℝ) = (chartAxis (35/128 : ℝ)).1 := by
    norm_num [step5Row55C, chartAxis]
  have hsdef : (step5Row55S : ℝ) = (chartAxis (35/128 : ℝ)).2 := by
    norm_num [step5Row55S, chartAxis]
  rw [hcdef, hsdef] at hsource
  change dx*(chartAxis (35/128 : ℝ)).1 -
    dy*(chartAxis (35/128 : ℝ)).2 < fieldScale/2 at hsource
  have hneg : dx*c-dy*s < fieldScale/2 := by
    have hx := mul_le_mul_of_nonneg_left hcl hdx0
    have hy := mul_le_mul_of_nonneg_left hsl hdy0
    nlinarith only [hx, hy, hsource]
  have hxs : dx*s ≤ (67/100 : ℝ)*(13/25) :=
    mul_le_mul hdx hsub hs0 (by norm_num)
  have hyc : dy*c ≤ (15/100 : ℝ)*(87/100) :=
    mul_le_mul hdy hcub hc0 (by norm_num)
  have hys : dy*s ≤ (15/100 : ℝ)*(13/25) :=
    mul_le_mul hdy hsub hs0 (by norm_num)
  have hx : |-dx*c+dy*s| < fieldScale/2 := by
    apply abs_lt.mpr
    constructor
    · nlinarith only [hneg]
    · have hbound : dy*s < fieldScale/2 := by
        nlinarith only [hys, show (15/100 : ℝ)*(13/25) < fieldScale/2 by
          norm_num [fieldScale, coverCap]]
      have hle : -dx*c+dy*s ≤ dy*s := by
        nlinarith only [mul_nonneg hdx0 hc0]
      exact lt_of_le_of_lt hle hbound
  have hy : |dx*s+dy*c| < fieldScale/2 := by
    apply abs_lt.mpr
    constructor
    · have hsum : 0 ≤ dx*s+dy*c :=
        add_nonneg (mul_nonneg hdx0 hs0) (mul_nonneg hdy0 hc0)
      have hscale : 0 < fieldScale/2 := half_pos fieldScale_pos
      exact lt_of_lt_of_le (by linarith only [hscale]) hsum
    · nlinarith only [hxs, hyc,
        show (67/100 : ℝ)*(13/25)+(15/100)*(87/100) < fieldScale/2 by
          norm_num [fieldScale, coverCap]]
  have hscl : 0 < fieldScale := fieldScale_pos
  have ex : localX q (w.1/fieldScale,w.2/fieldScale) =
      (-dx*c+dy*s)/fieldScale := by
    dsimp only [localX, dot]
    rw [haxis]
    dsimp [dx, dy, c, s, toField]
    field_simp [fieldScale_ne_zero] <;> ring
  have ey : localY q (w.1/fieldScale,w.2/fieldScale) =
      (dx*s+dy*c)/fieldScale := by
    dsimp only [localY, dot, perp]
    rw [haxis]
    dsimp [dx, dy, c, s, toField]
    field_simp [fieldScale_ne_zero] <;> ring
  dsimp only [OpenSquare]
  rw [ex, ey]
  constructor <;> rw [abs_div, abs_of_pos hscl]
  · calc
      |-dx*c+dy*s| / fieldScale < (fieldScale/2)/fieldScale :=
        div_lt_div_of_pos_right hx hscl
      _ = 1/2 := by field_simp [fieldScale_ne_zero]
  · calc
      |dx*s+dy*c| / fieldScale < (fieldScale/2)/fieldScale :=
        div_lt_div_of_pos_right hy hscl
      _ = 1/2 := by field_simp [fieldScale_ne_zero]

end
end ElevenSquare.Tasks.T07
