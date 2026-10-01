import ElevenSquare.Tasks.T07.Ext.Trace
import Mathlib.Analysis.Convex.Combination

/-! A Boolean checker for one `ExtStep.pruneOwned` step and its soundness.

The emitter is untrusted.  For every old row of the owner it supplies a list of
angular sub-rows covering the row's closed angle interval.  A sub-row `[a, b]`
carries
* necessary *self cuts* `n · c ≤ min_v n · v + M/2`, `-n · c ≤ -max_v n · v + M/2`
  from the owner's own owned hull (valid when `|n · axis| + |n · perp axis| ≤ M`
  on `[a, b]`),
* necessary *wall cuts* `h ≤ c.1 ≤ coverCap - h` (and for `c.2`), valid when the
  half width is at least `h` on `[a, b]`,
* a core polygon (vertices strictly inside every square of the sub-row), and
* a split tree over the row centres and the cuts, whose leaves are empty
  (Farkas), kept in a new row, or inside a triangle of the forbidden centres of
  another owner (explicit barycentric coordinates).
All comparisons are exact rational arithmetic, evaluated by the kernel. -/
namespace ElevenSquare.Tasks.T07.Ext
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07
noncomputable section

/-! ## Quadratics on an interval -/

/-- `c0 + c1 t + c2 t²`. -/
def qv (c0 c1 c2 t : ℚ) : ℚ := c0 + c1 * t + c2 * t * t

/-- Strict positivity on `[a, b]`. -/
def posQ (c0 c1 c2 a b : ℚ) : Bool :=
  decide (0 < qv c0 c1 c2 a ∧ 0 < qv c0 c1 c2 b ∧
    ((0 < c2 ∧ c1 + 2 * c2 * a < 0 ∧ 0 < c1 + 2 * c2 * b) → 0 < 4 * c0 * c2 - c1 * c1))

/-- Non-negativity on `[a, b]`. -/
def nnQ (c0 c1 c2 a b : ℚ) : Bool :=
  decide (0 ≤ qv c0 c1 c2 a ∧ 0 ≤ qv c0 c1 c2 b ∧
    ((0 < c2 ∧ c1 + 2 * c2 * a < 0 ∧ 0 < c1 + 2 * c2 * b) → 0 ≤ 4 * c0 * c2 - c1 * c1))

lemma quad_split (c0 c1 c2 t : ℝ) (hc2 : 0 < c2) :
    c0 + c1 * t + c2 * t * t = c2 * (t + c1 / (2 * c2)) ^ 2 + (4 * c0 * c2 - c1 * c1) / (4 * c2) := by
  field_simp; ring

/-- A quadratic is at least its values at the ends of an interval, unless its
minimum lies strictly inside; then it is at least `(4 c0 c2 - c1²)/(4 c2)`. -/
lemma quad_lower (c0 c1 c2 a b t : ℝ) (ha : a ≤ t) (hb : t ≤ b) :
    (min (c0 + c1 * a + c2 * a * a) (c0 + c1 * b + c2 * b * b) ≤ c0 + c1 * t + c2 * t * t) ∨
      (0 < c2 ∧ c1 + 2 * c2 * a < 0 ∧ 0 < c1 + 2 * c2 * b ∧
        (4 * c0 * c2 - c1 * c1) / (4 * c2) ≤ c0 + c1 * t + c2 * t * t) := by
  by_cases hc2 : 0 < c2
  · by_cases hin : c1 + 2 * c2 * a < 0 ∧ 0 < c1 + 2 * c2 * b
    · right
      refine ⟨hc2, hin.1, hin.2, ?_⟩
      rw [quad_split c0 c1 c2 t hc2]
      have : 0 ≤ c2 * (t + c1 / (2 * c2)) ^ 2 := by positivity
      linarith
    · left
      push Not at hin
      by_cases h1 : 0 ≤ c1 + 2 * c2 * a
      · -- increasing on [a, b]
        have e : (c0 + c1 * t + c2 * t * t) - (c0 + c1 * a + c2 * a * a)
            = (t - a) * (c1 + c2 * (t + a)) := by ring
        have hp : 0 ≤ c1 + c2 * (t + a) := by nlinarith
        have : c0 + c1 * a + c2 * a * a ≤ c0 + c1 * t + c2 * t * t := by
          nlinarith [mul_nonneg (sub_nonneg.mpr ha) hp]
        exact le_trans (min_le_left _ _) this
      · have h2 := hin (lt_of_not_ge h1)
        -- decreasing on [a, b]
        have e : (c0 + c1 * t + c2 * t * t) - (c0 + c1 * b + c2 * b * b)
            = (b - t) * (-(c1 + c2 * (t + b))) := by ring
        have hp : 0 ≤ -(c1 + c2 * (t + b)) := by nlinarith
        have : c0 + c1 * b + c2 * b * b ≤ c0 + c1 * t + c2 * t * t := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hb) hp]
        exact le_trans (min_le_right _ _) this
  · left
    push Not at hc2
    -- concave: above the chord
    rcases eq_or_lt_of_le (le_trans ha hb) with hab | hab
    · have h1 : t = a := le_antisymm (hab ▸ hb) ha
      subst h1; exact min_le_left _ _
    · have hw : c0 + c1 * t + c2 * t * t ≥
          ((b - t) * (c0 + c1 * a + c2 * a * a) + (t - a) * (c0 + c1 * b + c2 * b * b)) / (b - a) := by
        rw [ge_iff_le, div_le_iff₀ (by linarith)]
        have e : (c0 + c1 * t + c2 * t * t) * (b - a)
            - ((b - t) * (c0 + c1 * a + c2 * a * a) + (t - a) * (c0 + c1 * b + c2 * b * b))
            = (-c2) * ((t - a) * (b - t)) * (b - a) := by ring
        have : 0 ≤ (-c2) * ((t - a) * (b - t)) * (b - a) :=
          mul_nonneg (mul_nonneg (by linarith) (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)))
            (by linarith)
        linarith
      have hm := min_le_left (c0 + c1 * a + c2 * a * a) (c0 + c1 * b + c2 * b * b)
      have hm' := min_le_right (c0 + c1 * a + c2 * a * a) (c0 + c1 * b + c2 * b * b)
      refine le_trans ?_ (ge_iff_le.mp hw)
      rw [le_div_iff₀ (by linarith)]
      nlinarith [sub_nonneg.mpr ha, sub_nonneg.mpr hb]

theorem posQ_sound {c0 c1 c2 a b : ℚ} (h : posQ c0 c1 c2 a b = true) {t : ℝ}
    (ha : (a : ℝ) ≤ t) (hb : t ≤ b) : 0 < (c0 : ℝ) + c1 * t + c2 * t * t := by
  obtain ⟨h0, h1, h2⟩ := of_decide_eq_true h
  simp only [qv] at h0 h1
  have h0' : (0 : ℝ) < c0 + c1 * a + c2 * a * a := by exact_mod_cast h0
  have h1' : (0 : ℝ) < c0 + c1 * b + c2 * b * b := by exact_mod_cast h1
  rcases quad_lower c0 c1 c2 a b t ha hb with hl | ⟨hc2, hA, hB, hl⟩
  · exact lt_of_lt_of_le (lt_min h0' h1') hl
  · have hd : (0 : ℝ) < 4 * c0 * c2 - c1 * c1 := by
      exact_mod_cast h2 ⟨by exact_mod_cast hc2, by exact_mod_cast hA, by exact_mod_cast hB⟩
    exact lt_of_lt_of_le (div_pos hd (by linarith)) hl

theorem nnQ_sound {c0 c1 c2 a b : ℚ} (h : nnQ c0 c1 c2 a b = true) {t : ℝ}
    (ha : (a : ℝ) ≤ t) (hb : t ≤ b) : 0 ≤ (c0 : ℝ) + c1 * t + c2 * t * t := by
  obtain ⟨h0, h1, h2⟩ := of_decide_eq_true h
  simp only [qv] at h0 h1
  have h0' : (0 : ℝ) ≤ c0 + c1 * a + c2 * a * a := by exact_mod_cast h0
  have h1' : (0 : ℝ) ≤ c0 + c1 * b + c2 * b * b := by exact_mod_cast h1
  rcases quad_lower c0 c1 c2 a b t ha hb with hl | ⟨hc2, hA, hB, hl⟩
  · exact le_trans (le_min h0' h1') hl
  · have hd : (0 : ℝ) ≤ 4 * c0 * c2 - c1 * c1 := by
      exact_mod_cast h2 ⟨by exact_mod_cast hc2, by exact_mod_cast hA, by exact_mod_cast hB⟩
    exact le_trans (div_nonneg hd (by linarith)) hl

/-! ## Farkas certificates for rational half-planes -/

/-- The non-negative combination `∑ μ_k l_k` of half-planes. -/
def comb : List Halfplane → List ℚ → Halfplane
  | l :: P, m :: mu => ⟨m * l.a + (comb P mu).a, m * l.b + (comb P mu).b, m * l.c + (comb P mu).c⟩
  | _, _ => ⟨0, 0, 0⟩

theorem comb_contains : ∀ (P : Polygon) (mu : List ℚ), (∀ m ∈ mu, 0 ≤ m) →
    ∀ p : Point, p ∈ P.carrier → (comb P mu).contains p
  | l :: P, m :: mu, hnn, p, hp => by
    have hl : l.contains p := hp l List.mem_cons_self
    have hP : p ∈ Polygon.carrier P := fun l' hl' => hp l' (List.mem_cons_of_mem _ hl')
    have ih := comb_contains P mu (fun x hx => hnn x (List.mem_cons_of_mem _ hx)) p hP
    have hm : (0 : ℝ) ≤ m := by exact_mod_cast hnn m List.mem_cons_self
    unfold Halfplane.contains at hl ih ⊢
    simp only [comb]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hl hm]
  | [], _, _, p, _ => by simp [comb, Halfplane.contains]
  | _ :: _, [], _, p, _ => by simp [comb, Halfplane.contains]

/-- `P ⊆ g` by a Farkas combination. -/
def impliesB (P : Polygon) (mu : List ℚ) (g : Halfplane) : Bool :=
  (mu.all fun m => decide (0 ≤ m)) && decide ((comb P mu).a = g.a) &&
    decide ((comb P mu).b = g.b) && decide ((comb P mu).c ≤ g.c)

theorem impliesB_sound {P : Polygon} {mu : List ℚ} {g : Halfplane} (h : impliesB P mu g = true)
    {p : Point} (hp : p ∈ P.carrier) : g.contains p := by
  simp only [impliesB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hnn, ha⟩, hb⟩, hc⟩ := h
  have := comb_contains P mu hnn p hp
  unfold Halfplane.contains at this ⊢
  rw [ha, hb] at this
  have hc' : ((comb P mu).c : ℝ) ≤ g.c := by exact_mod_cast hc
  linarith

/-- `P` is empty by a Farkas combination. -/
def emptyB (P : Polygon) (mu : List ℚ) : Bool :=
  (mu.all fun m => decide (0 ≤ m)) && decide ((comb P mu).a = 0) &&
    decide ((comb P mu).b = 0) && decide ((comb P mu).c < 0)

theorem emptyB_sound {P : Polygon} {mu : List ℚ} (h : emptyB P mu = true) (p : Point) :
    p ∉ P.carrier := by
  intro hp
  simp only [emptyB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hnn, ha⟩, hb⟩, hc⟩ := h
  have := comb_contains P mu hnn p hp
  unfold Halfplane.contains at this
  rw [ha, hb] at this
  have hc' : ((comb P mu).c : ℝ) < 0 := by exact_mod_cast hc
  push_cast at this
  linarith

/-- `P ⊆ K` half-plane by half-plane. -/
def subsetB (P K : Polygon) (mus : List (List ℚ)) : Bool :=
  (mus.length == K.length) && ((K.zip mus).all fun gm => impliesB P gm.2 gm.1)

theorem subsetB_sound {P K : Polygon} {mus : List (List ℚ)} (h : subsetB P K mus = true) :
    P.carrier ⊆ K.carrier := by
  intro p hp g hg
  simp only [subsetB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hg
  have hn' : n < mus.length := hlen ▸ hn
  have := hall (K[n], mus[n]) (by
    rw [List.mem_iff_getElem]; exact ⟨n, by simp [hn, hn'], by simp⟩)
  exact impliesB_sound this hp

/-! ## The square at a chart parameter -/

lemma chart_den_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

lemma axis_unit' (q : UnitSquare) : q.axis.1 ^ 2 + q.axis.2 ^ 2 = 1 := by
  have := q.axis_unit; simp only [normSq, dot] at this; nlinarith

/-- `n · d` in the square's frame. -/
lemma dot_split (q : UnitSquare) (n d : Point) :
    dot n d = dot n q.axis * dot d q.axis + dot n (perp q.axis) * dot d (perp q.axis) := by
  have hu := axis_unit' q
  simp only [dot, perp]
  linear_combination (-(n.1 * d.1) - n.2 * d.2) * hu

lemma localX_add (q : UnitSquare) (w : Point) : localX q (q.center + w) = dot w q.axis := by
  simp [localX]
lemma localY_add (q : UnitSquare) (w : Point) : localY q (q.center + w) = dot w (perp q.axis) := by
  simp [localY]

lemma abs_combo_le {X Y A B : ℝ} (hX : |X| ≤ 1 / 2) (hY : |Y| ≤ 1 / 2) :
    A * X + B * Y ≤ (|A| + |B|) / 2 := by
  have h1 : A * X ≤ |A| * |X| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : B * Y ≤ |B| * |Y| := by rw [← abs_mul]; exact le_abs_self _
  nlinarith [mul_le_mul_of_nonneg_left hX (abs_nonneg A), mul_le_mul_of_nonneg_left hY (abs_nonneg B)]

lemma chart_dot (t : ℝ) (w : Point) :
    dot w (chartAxis t) = (w.1 * (1 - t ^ 2) + w.2 * (2 * t)) / (1 + t ^ 2) := by
  simp only [dot, chartAxis]; field_simp
lemma chart_dot_perp (t : ℝ) (w : Point) :
    dot w (perp (chartAxis t)) = (w.1 * (-(2 * t)) + w.2 * (1 - t ^ 2)) / (1 + t ^ 2) := by
  simp only [dot, perp, chartAxis]; field_simp

/-- `|N / (1 + t²)| < 1/2` from two strictly positive quadratics. -/
lemma abs_div_lt_half {N t : ℝ} (h1 : 0 < (1 + t ^ 2) / 2 - N) (h2 : 0 < (1 + t ^ 2) / 2 + N) :
    |N / (1 + t ^ 2)| < 1 / 2 := by
  have hd := chart_den_pos t
  rw [abs_div, abs_of_pos hd, div_lt_iff₀ hd, abs_lt]
  constructor <;> linarith

/-! ### Core vertices -/

/-- The four strict quadratics saying that `v` lies in the open square at every
parameter of `[a, b]`. -/
def coreVB (a b : ℚ) (v : QPoint) : Bool :=
  posQ (1/2 - v.1) (-2 * v.2) (1/2 + v.1) a b && posQ (1/2 + v.1) (2 * v.2) (1/2 - v.1) a b &&
    posQ (1/2 - v.2) (2 * v.1) (1/2 + v.2) a b && posQ (1/2 + v.2) (-2 * v.1) (1/2 - v.2) a b

theorem coreVB_sound {a b : ℚ} {v : QPoint} (h : coreVB a b v = true) {q : UnitSquare} {t : ℝ}
    (ha : (a : ℝ) ≤ t) (hb : t ≤ b) (hax : q.axis = chartAxis t) :
    OpenSquare q (q.center + realPoint v) := by
  simp only [coreVB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have e1 := posQ_sound h1 ha hb
  have e2 := posQ_sound h2 ha hb
  have e3 := posQ_sound h3 ha hb
  have e4 := posQ_sound h4 ha hb
  push_cast at e1 e2 e3 e4
  refine ⟨?_, ?_⟩
  · rw [localX_add, hax, chart_dot]
    apply abs_div_lt_half <;> simp only [realPoint] <;> nlinarith
  · rw [localY_add, hax, chart_dot_perp]
    apply abs_div_lt_half <;> simp only [realPoint] <;> nlinarith

lemma openSquare_shift_convex (q : UnitSquare) :
    Convex ℝ {w : Point | OpenSquare q (q.center + w)} := by
  intro x hx y hy s r hs hr hsr
  simp only [Set.mem_ofPred_eq, OpenSquare, localX_add, localY_add] at hx hy ⊢
  have lx : dot (s • x + r • y) q.axis = s * dot x q.axis + r * dot y q.axis := by
    simp [dot]; ring
  have ly : dot (s • x + r • y) (perp q.axis) = s * dot x (perp q.axis) + r * dot y (perp q.axis) := by
    simp [dot]; ring
  rw [lx, ly]
  have key : ∀ X Y : ℝ, |X| < 1/2 → |Y| < 1/2 → |s * X + r * Y| < 1/2 := by
    intro X Y hX hY
    rcases eq_or_lt_of_le hs with h0 | h0
    · subst h0; simp at hsr; subst hsr; simpa using hY
    · calc |s * X + r * Y| ≤ s * |X| + r * |Y| := by
            calc |s * X + r * Y| ≤ |s * X| + |r * Y| := abs_add_le _ _
              _ = s * |X| + r * |Y| := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hr]
        _ < 1/2 := by nlinarith [mul_le_mul_of_nonneg_left hY.le hr, mul_lt_mul_of_pos_left hX h0]
  exact ⟨key _ _ hx.1 hy.1, key _ _ hx.2 hy.2⟩

def corePts (core : List QPoint) : Set Point := {p | ∃ v ∈ core, p = realPoint v}

theorem core_fits {a b : ℚ} {core : List QPoint} (h : core.all (coreVB a b) = true)
    {q : UnitSquare} {t : ℝ} (ha : (a : ℝ) ≤ t) (hb : t ≤ b) (hax : q.axis = chartAxis t) :
    CoreFits (convexHull ℝ (corePts core)) q := by
  intro w hw
  have hsub : corePts core ⊆ {w : Point | OpenSquare q (q.center + w)} := by
    rintro p ⟨v, hv, rfl⟩
    exact coreVB_sound (List.all_eq_true.mp h v hv) ha hb hax
  exact (convexHull_min hsub (openSquare_shift_convex q)) hw

/-! ### Self cuts from the owner's own owned hull -/

/-- A self cut `(s n) · c ≤ u`, justified by the owned vertex `v` and the support
bound `|n · axis| + |n · perp axis| ≤ M` on `[a, b]`. -/
structure SelfCut where
  n1 : ℚ
  n2 : ℚ
  M : ℚ
  neg : Bool
  v : QPoint
  u : ℚ

def SelfCut.sgn (k : SelfCut) : ℚ := if k.neg then -1 else 1

def SelfCut.half (k : SelfCut) : Halfplane := ⟨k.sgn * k.n1, k.sgn * k.n2, k.u⟩

def supportB (n1 n2 M a b : ℚ) : Bool :=
  nnQ (M - n1 - n2) (-2 * n2 + 2 * n1) (M + n1 + n2) a b &&
  nnQ (M - n1 + n2) (-2 * n2 - 2 * n1) (M + n1 - n2) a b &&
  nnQ (M + n1 - n2) (2 * n2 + 2 * n1) (M - n1 + n2) a b &&
  nnQ (M + n1 + n2) (2 * n2 - 2 * n1) (M - n1 - n2) a b

def SelfCut.check (k : SelfCut) (owned : List QPoint) (a b : ℚ) : Bool :=
  supportB k.n1 k.n2 k.M a b && owned.contains k.v &&
    decide (k.sgn * (k.n1 * k.v.1 + k.n2 * k.v.2) + k.M / 2 ≤ k.u)

lemma support_le {n1 n2 M a b : ℚ} (h : supportB n1 n2 M a b = true) {t : ℝ}
    (ha : (a : ℝ) ≤ t) (hb : t ≤ b) :
    |dot ((n1 : ℝ), (n2 : ℝ)) (chartAxis t)| + |dot ((n1 : ℝ), (n2 : ℝ)) (perp (chartAxis t))| ≤ M := by
  simp only [supportB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have e1 := nnQ_sound h1 ha hb
  have e2 := nnQ_sound h2 ha hb
  have e3 := nnQ_sound h3 ha hb
  have e4 := nnQ_sound h4 ha hb
  push_cast at e1 e2 e3 e4
  have hd := chart_den_pos t
  rw [chart_dot, chart_dot_perp, abs_div, abs_div, abs_of_pos hd, ← add_div, div_le_iff₀ hd]
  set N1 : ℝ := (n1 : ℝ) * (1 - t ^ 2) + n2 * (2 * t)
  set N2 : ℝ := (n1 : ℝ) * (-(2 * t)) + n2 * (1 - t ^ 2)
  rcases le_total 0 N1 with p1 | p1 <;> rcases le_total 0 N2 with p2 | p2 <;>
    simp only [abs_of_nonneg, abs_of_nonpos, p1, p2] <;> nlinarith

theorem SelfCut.sound {k : SelfCut} {owned : List QPoint} {a b : ℚ}
    (h : k.check owned a b = true) {q : UnitSquare} {t : ℝ}
    (ha : (a : ℝ) ≤ t) (hb : t ≤ b) (hax : q.axis = chartAxis t)
    (hown : rationalHull owned ⊆ {p | OpenSquare q p}) : k.half.contains q.center := by
  simp only [SelfCut.check, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  obtain ⟨⟨hsup, hv⟩, hu⟩ := h
  have hin : OpenSquare q (realPoint k.v) :=
    hown (subset_convexHull ℝ _ ⟨k.v, hv, rfl⟩)
  set d : Point := realPoint k.v - q.center
  have hX : |dot d q.axis| ≤ 1 / 2 := by have := hin.1; simp only [localX] at this; exact this.le
  have hY : |dot d (perp q.axis)| ≤ 1 / 2 := by have := hin.2; simp only [localY] at this; exact this.le
  have hs := support_le hsup ha hb
  rw [← hax] at hs
  set n : Point := ((k.n1 : ℝ), (k.n2 : ℝ))
  have hsplit := dot_split q n d
  have hsg : (k.sgn : ℝ) = 1 ∨ (k.sgn : ℝ) = -1 := by
    unfold SelfCut.sgn; split_ifs <;> norm_num
  -- `-(sgn) n · d ≤ M/2`
  have key : -(k.sgn : ℝ) * dot n d ≤ (k.M : ℝ) / 2 := by
    rw [hsplit]
    have hb' := abs_combo_le (A := -(k.sgn : ℝ) * dot n q.axis) (B := -(k.sgn : ℝ) * dot n (perp q.axis)) hX hY
    have habs : |-(k.sgn : ℝ) * dot n q.axis| + |-(k.sgn : ℝ) * dot n (perp q.axis)|
        = |dot n q.axis| + |dot n (perp q.axis)| := by
      rcases hsg with e | e <;> rw [e] <;> simp
    nlinarith
  have hu' : (k.sgn : ℝ) * (k.n1 * k.v.1 + k.n2 * k.v.2) + k.M / 2 ≤ k.u := by exact_mod_cast hu
  unfold Halfplane.contains SelfCut.half
  simp only [d, n, dot, realPoint, Prod.fst_sub, Prod.snd_sub] at key
  push_cast
  nlinarith

/-! ### Wall cuts from the container -/

def coverQ : ℚ := 387708359002281417731 / 100000000000000000000

lemma coverQ_cast : ((coverQ : ℚ) : ℝ) = coverCap := by norm_num [coverQ, coverCap]

/-- `|axis.1| + |axis.2| ≥ 2 h` on `[a, b] ⊆ [0, 1]`. -/
def wallB (h a b : ℚ) : Bool := nnQ (1 - 2 * h) 2 (-1 - 2 * h) a b

def wallHalves (h : ℚ) : Polygon :=
  [⟨-1, 0, -h⟩, ⟨1, 0, coverQ - h⟩, ⟨0, -1, -h⟩, ⟨0, 1, coverQ - h⟩]

lemma closed_offset (q : UnitSquare) (X Y : ℝ) (hX : |X| ≤ 1 / 2) (hY : |Y| ≤ 1 / 2) :
    ClosedSquare q (q.center + (X * q.axis.1 - Y * q.axis.2, X * q.axis.2 + Y * q.axis.1)) := by
  have hu := axis_unit' q
  refine ⟨?_, ?_⟩
  · rw [localX_add]; simp only [dot]
    have : (X * q.axis.1 - Y * q.axis.2) * q.axis.1 + (X * q.axis.2 + Y * q.axis.1) * q.axis.2 = X := by
      linear_combination X * hu
    rw [this]; exact hX
  · rw [localY_add]; simp only [dot, perp]
    have : (X * q.axis.1 - Y * q.axis.2) * -q.axis.2 + (X * q.axis.2 + Y * q.axis.1) * q.axis.1 = Y := by
      linear_combination Y * hu
    rw [this]; exact hY

theorem wall_sound {h a b : ℚ} (hw : wallB h a b = true) {q : UnitSquare} {t : ℝ}
    (ha : (a : ℝ) ≤ t) (hb : t ≤ b) (hax : q.axis = chartAxis t)
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p) :
    q.center ∈ (wallHalves h).carrier := by
  have e := nnQ_sound hw ha hb
  push_cast at e
  have hd := chart_den_pos t
  have hsum : 2 * (h : ℝ) ≤ q.axis.1 + q.axis.2 := by
    rw [hax]; simp only [chartAxis]
    rw [← add_div, le_div_iff₀ hd]; nlinarith
  have p1 := hcont _ (closed_offset q (-1/2) (1/2) (by norm_num [abs_div]) (by norm_num [abs_div]))
  have p2 := hcont _ (closed_offset q (1/2) (-1/2) (by norm_num [abs_div]) (by norm_num [abs_div]))
  have p3 := hcont _ (closed_offset q (-1/2) (-1/2) (by norm_num [abs_div]) (by norm_num [abs_div]))
  have p4 := hcont _ (closed_offset q (1/2) (1/2) (by norm_num [abs_div]) (by norm_num [abs_div]))
  simp only [InContainer, Prod.fst_add, Prod.snd_add] at p1 p2 p3 p4
  intro l hl
  simp only [wallHalves, List.mem_cons, List.not_mem_nil, or_false] at hl
  have hc := coverQ_cast
  rcases hl with rfl | rfl | rfl | rfl <;> simp only [Halfplane.contains] <;> push_cast <;>
    (try rw [hc]) <;> nlinarith [p1.1, p2.2.1, p3.2.2.1, p4.2.2.2]

/-! ## Forbidden triangles -/

/-- A triangle `w_m = k_m - v_m` with `k_m` owned by the partner and `v_m` a core
vertex, and affine barycentric coordinates `λ_m(p) = α_m p.1 + β_m p.2 + γ_m`. -/
structure Tri where
  k : List QPoint
  v : List QPoint
  lam : List (ℚ × ℚ × ℚ)
  mus : List (List ℚ)

def triW (T : Tri) : List QPoint := (T.k.zip T.v).map fun kv => (kv.1.1 - kv.2.1, kv.1.2 - kv.2.2)

lemma conv3 {S : Set Point} (hS : Convex ℝ S) {x y z : Point} (hx : x ∈ S) (hy : y ∈ S)
    (hz : z ∈ S) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) :
    a • x + b • y + c • z ∈ S := by
  have := hS.sum_mem (t := Finset.univ) (w := ![a, b, c]) (z := ![x, y, z])
    (by intro i _; fin_cases i <;> simp [ha, hb, hc])
    (by simp [Fin.sum_univ_three, habc])
    (by intro i _; fin_cases i <;> simp [hx, hy, hz])
  simpa [Fin.sum_univ_three] using this

def lamHalf (l : ℚ × ℚ × ℚ) : Halfplane := ⟨-l.1, -l.2.1, l.2.2⟩

def sum3 (f : ℕ → ℚ) : ℚ := f 0 + f 1 + f 2

def Tri.check (T : Tri) (owned core : List QPoint) (P : Polygon) : Bool :=
  (T.k.length == 3) && (T.v.length == 3) && (T.lam.length == 3) && (T.mus.length == 3) &&
  (T.k.all owned.contains) && (T.v.all core.contains) &&
  (let L := fun m => T.lam.getD m (0, 0, 0)
   let W := fun m => (triW T).getD m (0, 0)
   decide (sum3 (fun m => (L m).1) = 0 ∧ sum3 (fun m => (L m).2.1) = 0 ∧ sum3 (fun m => (L m).2.2) = 1 ∧
     sum3 (fun m => (L m).1 * (W m).1) = 1 ∧ sum3 (fun m => (L m).2.1 * (W m).1) = 0 ∧
     sum3 (fun m => (L m).2.2 * (W m).1) = 0 ∧
     sum3 (fun m => (L m).1 * (W m).2) = 0 ∧ sum3 (fun m => (L m).2.1 * (W m).2) = 1 ∧
     sum3 (fun m => (L m).2.2 * (W m).2) = 0)) &&
  ((T.lam.zip T.mus).all fun lm => impliesB P lm.2 (lamHalf lm.1))

theorem Tri.sound {T : Tri} {owned core : List QPoint} {P : Polygon} (h : T.check owned core P = true)
    {p : Point} (hp : p ∈ P.carrier) :
    p ∈ forbiddenCenters (rationalHull owned) (convexHull ℝ (corePts core)) := by
  rcases T with ⟨tk, tv, tl, tm⟩
  simp only [Tri.check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hk3, hv3⟩, hl3⟩, hm3⟩, hkm⟩, hvm⟩, hid⟩, hmus⟩ := h
  obtain ⟨k0, k1, k2, rfl⟩ := List.length_eq_three.mp hk3
  obtain ⟨v0, v1, v2, rfl⟩ := List.length_eq_three.mp hv3
  obtain ⟨l0, l1, l2, rfl⟩ := List.length_eq_three.mp hl3
  obtain ⟨m0, m1, m2, rfl⟩ := List.length_eq_three.mp hm3
  simp only [triW, sum3, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ] at hid
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := hid
  -- the barycentric coordinates are non-negative at `p`
  have hl : ∀ l ∈ [(l0, m0), (l1, m1), (l2, m2)], 0 ≤ (l.1.1 : ℝ) * p.1 + l.1.2.1 * p.2 + l.1.2.2 := by
    intro l hlm
    have := impliesB_sound (hmus l (by simpa [List.zip] using hlm)) hp
    simp only [lamHalf, Halfplane.contains] at this; push_cast at this; linarith
  set L0 : ℝ := (l0.1 : ℝ) * p.1 + l0.2.1 * p.2 + l0.2.2
  set L1 : ℝ := (l1.1 : ℝ) * p.1 + l1.2.1 * p.2 + l1.2.2
  set L2 : ℝ := (l2.1 : ℝ) * p.1 + l2.2.1 * p.2 + l2.2.2
  have h0 : 0 ≤ L0 := hl (l0, m0) (by simp)
  have h1 : 0 ≤ L1 := hl (l1, m1) (by simp)
  have h2 : 0 ≤ L2 := hl (l2, m2) (by simp)
  have q1 : ((l0.1 + l1.1 + l2.1 : ℚ) : ℝ) = 0 := by exact_mod_cast e1
  have q2 : ((l0.2.1 + l1.2.1 + l2.2.1 : ℚ) : ℝ) = 0 := by exact_mod_cast e2
  have q3 : ((l0.2.2 + l1.2.2 + l2.2.2 : ℚ) : ℝ) = 1 := by exact_mod_cast e3
  push_cast at q1 q2 q3
  have hsum : L0 + L1 + L2 = 1 := by
    simp only [L0, L1, L2]; linear_combination p.1 * q1 + p.2 * q2 + q3
  have r4 := congrArg (fun x : ℚ => (x : ℝ)) e4
  have r5 := congrArg (fun x : ℚ => (x : ℝ)) e5
  have r6 := congrArg (fun x : ℚ => (x : ℝ)) e6
  have r7 := congrArg (fun x : ℚ => (x : ℝ)) e7
  have r8 := congrArg (fun x : ℚ => (x : ℝ)) e8
  have r9 := congrArg (fun x : ℚ => (x : ℝ)) e9
  push_cast at r4 r5 r6 r7 r8 r9
  set K : Point := L0 • realPoint k0 + L1 • realPoint k1 + L2 • realPoint k2
  set V : Point := L0 • realPoint v0 + L1 • realPoint v1 + L2 • realPoint v2
  have hK : K ∈ rationalHull owned :=
    conv3 (convex_convexHull ℝ _) (subset_convexHull ℝ {p : Point | ∃ v ∈ owned, p = realPoint v} ⟨k0, hkm k0 (by simp), rfl⟩)
      (subset_convexHull ℝ {p : Point | ∃ v ∈ owned, p = realPoint v} ⟨k1, hkm k1 (by simp), rfl⟩)
      (subset_convexHull ℝ {p : Point | ∃ v ∈ owned, p = realPoint v} ⟨k2, hkm k2 (by simp), rfl⟩) h0 h1 h2 hsum
  have hV : V ∈ convexHull ℝ (corePts core) :=
    conv3 (convex_convexHull ℝ _) (subset_convexHull ℝ (corePts core) ⟨v0, hvm v0 (by simp), rfl⟩)
      (subset_convexHull ℝ (corePts core) ⟨v1, hvm v1 (by simp), rfl⟩)
      (subset_convexHull ℝ (corePts core) ⟨v2, hvm v2 (by simp), rfl⟩) h0 h1 h2 hsum
  refine ⟨K, hK, V, hV, ?_⟩
  ext
  · simp only [K, V, L0, L1, L2, realPoint, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linear_combination (-p.1) * r4 + (-p.2) * r5 - r6
  · simp only [K, V, L0, L1, L2, realPoint, Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linear_combination (-p.1) * r7 + (-p.2) * r8 - r9

/-! ## Cover trees -/

inductive CTree
  | empty (mu : List ℚ)
  | keep (m : ℕ) (mus : List (List ℚ))
  | forbid (j : ℕ) (T : Tri)
  | split (l : Halfplane) (le ge : CTree)

def negH (l : Halfplane) : Halfplane := ⟨-l.a, -l.b, -l.c⟩

/-- The context of one sub-row: the state, the owner, the new rows, the core and
the angle interval. -/
structure Ctx where
  s : PoseState
  i : Owner
  rs : List PoseRow
  core : List QPoint
  a : ℚ
  b : ℚ

def ownedOf (s : PoseState) (j : ℕ) : List QPoint := if h : j < 11 then s.owned ⟨j, h⟩ else []

def CTree.check (C : Ctx) : Polygon → CTree → Bool
  | P, .empty mu => emptyB P mu
  | P, .keep m mus => decide (m < C.rs.length) &&
      subsetB P (C.rs.getD m ⟨0, 0, []⟩).centers mus &&
      decide ((C.rs.getD m ⟨0, 0, []⟩).lo ≤ C.a) && decide (C.b ≤ (C.rs.getD m ⟨0, 0, []⟩).hi)
  | P, .forbid j T => decide (j < 11) && decide (j ≠ C.i.val) && T.check (ownedOf C.s j) C.core P
  | P, .split l le ge => CTree.check C (l :: P) le && CTree.check C (negH l :: P) ge

/-- The conclusion of a tree at a pose. -/
def Good (C : Ctx) (q : UnitSquare) : Prop :=
  RowsContain C.rs q ∨ ∃ j : Owner, C.i ≠ j ∧
    q.center ∈ forbiddenCenters (rationalHull (C.s.owned j)) (convexHull ℝ (corePts C.core))

theorem CTree.sound (C : Ctx) {q : UnitSquare} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : (C.a : ℝ) ≤ t) (hb : t ≤ C.b) (hax : q.axis = chartAxis t) :
    ∀ (T : CTree) (P : Polygon), T.check C P = true → q.center ∈ P.carrier → Good C q
  | .empty mu, P, h, hp => absurd hp (emptyB_sound h _)
  | .keep m mus, P, h, hp => by
    simp only [CTree.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hm, hsub⟩, hlo⟩, hhi⟩ := h
    left
    refine ⟨C.rs.getD m ⟨0, 0, []⟩, ?_, subsetB_sound hsub hp, t, ht0, ht1,
      le_trans (by exact_mod_cast hlo) ha, le_trans hb (by exact_mod_cast hhi), hax⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
    exact List.getElem_mem hm
  | .forbid j T, P, h, hp => by
    simp only [CTree.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hj, hji⟩, hT⟩ := h
    right
    refine ⟨⟨j, hj⟩, fun e => hji (by rw [e]), ?_⟩
    have := Tri.sound hT hp
    simpa [ownedOf, hj] using this
  | .split l le ge, P, h, hp => by
    simp only [CTree.check, Bool.and_eq_true] at h
    by_cases hl : l.contains q.center
    · exact CTree.sound C ht0 ht1 ha hb hax le (l :: P) h.1 (by
        intro g hg; rcases List.mem_cons.mp hg with rfl | hg
        · exact hl
        · exact hp g hg)
    · exact CTree.sound C ht0 ht1 ha hb hax ge (negH l :: P) h.2 (by
        intro g hg; rcases List.mem_cons.mp hg with rfl | hg
        · unfold Halfplane.contains at hl ⊢; simp only [negH]; push_cast; push Not at hl; linarith
        · exact hp g hg)

/-! ## Rows and steps -/

/-- One angular sub-row `[a, b]` of an old row. -/
structure Sub where
  a : ℚ
  b : ℚ
  cuts : List SelfCut
  wall : ℚ
  core : List QPoint
  tree : CTree

def subPoly (r : PoseRow) (u : Sub) : Polygon :=
  r.centers ++ u.cuts.map SelfCut.half ++ wallHalves u.wall

def Sub.check (s : PoseState) (i : Owner) (rs : List PoseRow) (r : PoseRow) (u : Sub) : Bool :=
  (u.cuts.all fun k => k.check (s.owned i) u.a u.b) && wallB u.wall u.a u.b &&
    (u.core.all (coreVB u.a u.b)) && CTree.check ⟨s, i, rs, u.core, u.a, u.b⟩ (subPoly r u) u.tree

/-- The sub-rows cover `[x, hi]`. -/
def coversB (hi : ℚ) : ℚ → List Sub → Bool
  | x, [] => decide (hi < x)
  | x, u :: L => decide (hi < x) ||
      (decide (u.a ≤ x) && decide (x ≤ u.b) && (decide (hi ≤ u.b) || coversB hi u.b L))

theorem coversB_sound (hi : ℚ) : ∀ (x : ℚ) (L : List Sub), coversB hi x L = true →
    ∀ t : ℝ, (x : ℝ) ≤ t → t ≤ hi → ∃ u ∈ L, (u.a : ℝ) ≤ t ∧ t ≤ u.b
  | x, [], h, t, hx, hh => by
    simp only [coversB, decide_eq_true_eq] at h
    have : (hi : ℝ) < x := by exact_mod_cast h
    linarith
  | x, u :: L, h, t, hx, hh => by
    simp only [coversB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨⟨hua, hxu⟩, hL⟩
    · have : (hi : ℝ) < x := by exact_mod_cast h
      linarith
    · by_cases htu : t ≤ u.b
      · exact ⟨u, List.mem_cons_self, le_trans (by exact_mod_cast hua) hx, htu⟩
      · rcases hL with hL | hL
        · have : (hi : ℝ) ≤ u.b := by exact_mod_cast hL
          exact absurd (le_trans hh this) htu
        · obtain ⟨w, hw, hw'⟩ := coversB_sound hi u.b L hL t (le_of_lt (lt_of_not_ge htu)) hh
          exact ⟨w, List.mem_cons_of_mem _ hw, hw'⟩

def rowB (s : PoseState) (i : Owner) (rs : List PoseRow) (r : PoseRow) (subs : List Sub) : Bool :=
  coversB r.hi r.lo subs && subs.all (Sub.check s i rs r)

def stepB (s : PoseState) (i : Owner) (rs : List PoseRow) (certs : List (List Sub)) : Bool :=
  (certs.length == (s.rows i).length) && (((s.rows i).zip certs).all fun rc => rowB s i rs rc.1 rc.2)

theorem rowB_sound {s : PoseState} {i : Owner} {rs : List PoseRow} {r : PoseRow} {subs : List Sub}
    (h : rowB s i rs r subs = true) {q : UnitSquare} (hr : r.contains q)
    (hown : rationalHull (s.owned i) ⊆ {p | OpenSquare q p})
    (hcont : ∀ p, ClosedSquare q p → InContainer coverCap p) :
    RowsContain rs q ∨ ∃ j : Owner, i ≠ j ∧ ∃ Q : Set Point,
      CoreFits Q q ∧ q.center ∈ forbiddenCenters (rationalHull (s.owned j)) Q := by
  simp only [rowB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hcov, hsubs⟩ := h
  obtain ⟨hc, t, ht0, ht1, hlo, hhi, hax⟩ := hr
  obtain ⟨u, hu, hua, hub⟩ := coversB_sound r.hi r.lo subs hcov t hlo hhi
  have hU := hsubs u hu
  simp only [Sub.check, Bool.and_eq_true, List.all_eq_true] at hU
  obtain ⟨⟨⟨hcuts, hwall⟩, hcore⟩, htree⟩ := hU
  have hP : q.center ∈ (subPoly r u).carrier := by
    intro l hl
    simp only [subPoly, List.mem_append, List.mem_map] at hl
    rcases hl with (hl | ⟨k, hk, rfl⟩) | hl
    · exact hc l hl
    · exact SelfCut.sound (hcuts k hk) hua hub hax hown
    · exact wall_sound hwall hua hub hax hcont l hl
  rcases CTree.sound ⟨s, i, rs, u.core, u.a, u.b⟩ ht0 ht1 hua hub hax u.tree (subPoly r u) htree hP with
    hkeep | ⟨j, hij, hf⟩
  · exact Or.inl hkeep
  · exact Or.inr ⟨j, hij, _, core_fits (List.all_eq_true.mpr hcore) hua hub hax, hf⟩

/-- **Soundness of a checked step.** -/
theorem stepB_sound {s : PoseState} {i : Owner} {rs : List PoseRow} {certs : List (List Sub)}
    (h : stepB s i rs certs = true) : ExtStep s (replaceRows s i rs) := by
  apply ExtStep.pruneOwned
  intro q ⟨r, hr, hc⟩ hown hcont
  simp only [stepB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hr
  have hn' : n < certs.length := hlen ▸ hn
  have hmem : ((s.rows i)[n], certs[n]) ∈ (s.rows i).zip certs := by
    rw [List.mem_iff_getElem]; exact ⟨n, by simp [hn, hn'], by simp⟩
  exact rowB_sound (hall _ hmem) hc hown hcont

end
end ElevenSquare.Tasks.T07.Ext
