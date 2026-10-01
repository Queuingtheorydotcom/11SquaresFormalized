import Sqpack.S11Opt.Split.U4.Sat

/-!
# U4 — linearisation of the gap functions with explicit remainders

A corner gap `pgap` and a wall gap `wgap` at a perturbed pose equal their value at the base
pose, plus a linear form in the perturbation, plus a remainder.  Every remainder term has degree
at least two in the perturbation, so for a perturbation `h` with `|h_k| ≤ τ r_k`, `0 ≤ τ ≤ 1`,
it is at most `τ` times an explicit constant `K` (`pgap_approx`, `wgap_approx`).  The
coefficients of the linear form may be replaced by approximations; their errors enter `K`.
-/

open Real

namespace SquarePacking.S11Opt.Split

lemma abs_cos_sub_one_le (x : ℝ) : |cos x - 1| ≤ x ^ 2 / 2 := by
  rw [abs_sub_comm, abs_of_nonneg (by linarith [cos_le_one x])]
  linarith [one_sub_sq_div_two_le_cos (x := x)]

lemma abs_sin_sub_self_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) : |sin x - x| ≤ x ^ 3 / 6 := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h; simp
  rw [abs_sub_comm, abs_of_nonneg (by linarith [sin_le hx])]
  linarith [sin_gt_sub_cube h]

lemma abs_sin_sub_self_le (x : ℝ) : |sin x - x| ≤ |x| ^ 3 / 6 := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; exact abs_sin_sub_self_le_of_nonneg h
  · have := abs_sin_sub_self_le_of_nonneg (neg_nonneg.mpr h)
    rw [sin_neg, show -sin x - -x = -(sin x - x) by ring, abs_neg] at this
    rwa [abs_of_nonpos h]

/-- Powers of a quantity at most `τ w`, with `0 ≤ τ ≤ 1`, are at most `τ w^n`. -/
lemma sq_le_tau {a τ w : ℝ} (ha : |a| ≤ τ * w) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    a ^ 2 ≤ τ * w ^ 2 := by
  have hw : 0 ≤ τ * w := le_trans (abs_nonneg a) ha
  have h2 : a ^ 2 ≤ (τ * w) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have : (τ * w) ^ 2 = τ * (τ * w ^ 2) := by ring
  have hw2 : 0 ≤ τ * w ^ 2 := mul_nonneg hτ0 (sq_nonneg w)
  nlinarith [mul_le_of_le_one_left hw2 hτ1]

lemma cube_le_tau {a τ w : ℝ} (ha : |a| ≤ τ * w) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hw0 : 0 ≤ w) :
    |a| ^ 3 ≤ τ * w ^ 3 := by
  have h3 : |a| ^ 3 ≤ (τ * w) ^ 3 := pow_le_pow_left₀ (abs_nonneg a) ha 3
  have : (τ * w) ^ 3 = τ * (τ ^ 2 * w ^ 3) := by ring
  have hτ2 : τ ^ 2 ≤ 1 := by nlinarith
  have hw3 : 0 ≤ w ^ 3 := pow_nonneg hw0 3
  nlinarith [mul_le_mul_of_nonneg_right hτ2 hw3, mul_nonneg hτ0 hw3]

/-! ## Corner gaps -/

/-- **Expansion of a corner gap** around a base pose. -/
lemma pgap_expand (co cp co' cp' : ℝ × ℝ) (α β x y s1 s2 : ℝ) :
    pgap co' cp' (α + x) (β + y) s1 s2 = pgap co cp α β s1 s2
      + (cos α * ((cp'.1 - co'.1) - (cp.1 - co.1)) + sin α * ((cp'.2 - co'.2) - (cp.2 - co.2))
        + ((-sin α * (cp.1 - co.1) + cos α * (cp.2 - co.2))
            - (-s1 * sin (β - α) - s2 * cos (β - α)) / 2) * x
        + ((-s1 * sin (β - α) - s2 * cos (β - α)) / 2) * y)
      + ((cos α * (cp.1 - co.1) + sin α * (cp.2 - co.2)) * (cos x - 1)
        + (-sin α * (cp.1 - co.1) + cos α * (cp.2 - co.2)) * (sin x - x)
        + (cos α * ((cp'.1 - co'.1) - (cp.1 - co.1)) + sin α * ((cp'.2 - co'.2) - (cp.2 - co.2)))
            * (cos x - 1)
        + (-sin α * ((cp'.1 - co'.1) - (cp.1 - co.1)) + cos α * ((cp'.2 - co'.2) - (cp.2 - co.2)))
            * sin x
        + ((s1 * cos (β - α) - s2 * sin (β - α)) / 2) * (cos (y - x) - 1)
        + ((-s1 * sin (β - α) - s2 * cos (β - α)) / 2) * (sin (y - x) - (y - x))) := by
  unfold pgap
  rw [show β + y - (α + x) = (β - α) + (y - x) by ring]
  simp only [cos_add, sin_add]
  ring

/-- **Linearisation of a corner gap** with approximate coefficients `C, S, G, Z`. -/
theorem pgap_approx {co cp co' cp' : ℝ × ℝ} {α β x y s1 s2 τ Rx Ry wo wp : ℝ}
    {C S G Z eC eS eG eZ bP bPd bz bzd : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hRx : 0 ≤ Rx) (hRy : 0 ≤ Ry) (hwo : 0 ≤ wo) (hwp : 0 ≤ wp)
    (hdx : |(cp'.1 - co'.1) - (cp.1 - co.1)| ≤ τ * Rx)
    (hdy : |(cp'.2 - co'.2) - (cp.2 - co.2)| ≤ τ * Ry)
    (hx : |x| ≤ τ * wo) (hy : |y| ≤ τ * wp)
    (hC : |cos α - C| ≤ eC) (hS : |sin α - S| ≤ eS)
    (hG : |((-sin α * (cp.1 - co.1) + cos α * (cp.2 - co.2))
            - (-s1 * sin (β - α) - s2 * cos (β - α)) / 2) - G| ≤ eG)
    (hZ : |(-s1 * sin (β - α) - s2 * cos (β - α)) / 2 - Z| ≤ eZ)
    (hbP : |cos α * (cp.1 - co.1) + sin α * (cp.2 - co.2)| ≤ bP)
    (hbPd : |-sin α * (cp.1 - co.1) + cos α * (cp.2 - co.2)| ≤ bPd)
    (hbz : |(s1 * cos (β - α) - s2 * sin (β - α)) / 2| ≤ bz)
    (hbzd : |(-s1 * sin (β - α) - s2 * cos (β - α)) / 2| ≤ bzd) :
    |pgap co' cp' (α + x) (β + y) s1 s2 - pgap co cp α β s1 s2
        - (C * ((cp'.1 - co'.1) - (cp.1 - co.1)) + S * ((cp'.2 - co'.2) - (cp.2 - co.2))
          + G * x + Z * y)|
      ≤ τ * (bP * wo ^ 2 / 2 + bPd * wo ^ 3 / 6 + (Rx + Ry) * wo ^ 2 / 2 + (Rx + Ry) * wo
          + bz * (wo + wp) ^ 2 / 2 + bzd * (wo + wp) ^ 3 / 6
          + eC * Rx + eS * Ry + eG * wo + eZ * wp) := by
  rw [pgap_expand co cp co' cp' α β x y s1 s2]
  set dx := (cp'.1 - co'.1) - (cp.1 - co.1)
  set dy := (cp'.2 - co'.2) - (cp.2 - co.2)
  set Pv := cos α * (cp.1 - co.1) + sin α * (cp.2 - co.2)
  set Pd := -sin α * (cp.1 - co.1) + cos α * (cp.2 - co.2)
  set z0 := (s1 * cos (β - α) - s2 * sin (β - α)) / 2
  set zd := (-s1 * sin (β - α) - s2 * cos (β - α)) / 2
  have hc := abs_cos_le_one α
  have hs := abs_sin_le_one α
  have he : |y - x| ≤ τ * (wo + wp) := by
    calc |y - x| ≤ |y| + |x| := abs_sub _ _
      _ ≤ τ * (wo + wp) := by linarith
  -- the pieces of the remainder
  have r1 : |Pv * (cos x - 1)| ≤ τ * (bP * wo ^ 2 / 2) := by
    rw [abs_mul]
    have := le_trans (abs_cos_sub_one_le x) (by linarith [sq_le_tau hx hτ0 hτ1])
      (c := τ * wo ^ 2 / 2)
    have hbP0 : 0 ≤ bP := le_trans (abs_nonneg _) hbP
    calc |Pv| * |cos x - 1| ≤ bP * (τ * wo ^ 2 / 2) :=
          mul_le_mul hbP this (abs_nonneg _) hbP0
      _ = τ * (bP * wo ^ 2 / 2) := by ring
  have r2 : |Pd * (sin x - x)| ≤ τ * (bPd * wo ^ 3 / 6) := by
    rw [abs_mul]
    have := le_trans (abs_sin_sub_self_le x) (by linarith [cube_le_tau hx hτ0 hτ1 hwo])
      (c := τ * wo ^ 3 / 6)
    have hb0 : 0 ≤ bPd := le_trans (abs_nonneg _) hbPd
    calc |Pd| * |sin x - x| ≤ bPd * (τ * wo ^ 3 / 6) :=
          mul_le_mul hbPd this (abs_nonneg _) hb0
      _ = τ * (bPd * wo ^ 3 / 6) := by ring
  have hlin1 : |cos α * dx + sin α * dy| ≤ τ * (Rx + Ry) := by
    calc |cos α * dx + sin α * dy| ≤ |cos α| * |dx| + |sin α| * |dy| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * (τ * Rx) + 1 * (τ * Ry) := by
          gcongr
      _ = τ * (Rx + Ry) := by ring
  have hlin2 : |-sin α * dx + cos α * dy| ≤ τ * (Rx + Ry) := by
    calc |-sin α * dx + cos α * dy| ≤ |-sin α| * |dx| + |cos α| * |dy| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * (τ * Rx) + 1 * (τ * Ry) := by
          rw [abs_neg]; gcongr
      _ = τ * (Rx + Ry) := by ring
  have hR0 : 0 ≤ Rx + Ry := by linarith
  have r3 : |(cos α * dx + sin α * dy) * (cos x - 1)| ≤ τ * ((Rx + Ry) * wo ^ 2 / 2) := by
    rw [abs_mul]
    have hcx := le_trans (abs_cos_sub_one_le x) (by linarith [sq_le_tau hx hτ0 hτ1])
      (c := τ * wo ^ 2 / 2)
    have h0 : 0 ≤ τ * wo ^ 2 / 2 := le_trans (abs_nonneg _) hcx
    calc |cos α * dx + sin α * dy| * |cos x - 1| ≤ (τ * (Rx + Ry)) * (τ * wo ^ 2 / 2) :=
          mul_le_mul hlin1 hcx (abs_nonneg _) (mul_nonneg hτ0 hR0)
      _ = τ * (τ * ((Rx + Ry) * wo ^ 2 / 2)) := by ring
      _ ≤ τ * ((Rx + Ry) * wo ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_left _ hτ0
          have : 0 ≤ (Rx + Ry) * wo ^ 2 / 2 := by positivity
          nlinarith
  have r4 : |(-sin α * dx + cos α * dy) * sin x| ≤ τ * ((Rx + Ry) * wo) := by
    rw [abs_mul]
    have hsx : |sin x| ≤ τ * wo := le_trans abs_sin_le_abs hx
    have hwo' : 0 ≤ τ * wo := le_trans (abs_nonneg _) hsx
    calc |-sin α * dx + cos α * dy| * |sin x| ≤ (τ * (Rx + Ry)) * (τ * wo) :=
          mul_le_mul hlin2 hsx (abs_nonneg _) (mul_nonneg hτ0 hR0)
      _ = τ * (τ * ((Rx + Ry) * wo)) := by ring
      _ ≤ τ * ((Rx + Ry) * wo) := by
          apply mul_le_mul_of_nonneg_left _ hτ0
          have : 0 ≤ (Rx + Ry) * wo := mul_nonneg hR0 hwo
          nlinarith
  have r5 : |z0 * (cos (y - x) - 1)| ≤ τ * (bz * (wo + wp) ^ 2 / 2) := by
    rw [abs_mul]
    have := le_trans (abs_cos_sub_one_le (y - x)) (by linarith [sq_le_tau he hτ0 hτ1])
      (c := τ * (wo + wp) ^ 2 / 2)
    have hb0 : 0 ≤ bz := le_trans (abs_nonneg _) hbz
    calc |z0| * |cos (y - x) - 1| ≤ bz * (τ * (wo + wp) ^ 2 / 2) :=
          mul_le_mul hbz this (abs_nonneg _) hb0
      _ = τ * (bz * (wo + wp) ^ 2 / 2) := by ring
  have r6 : |zd * (sin (y - x) - (y - x))| ≤ τ * (bzd * (wo + wp) ^ 3 / 6) := by
    rw [abs_mul]
    have := le_trans (abs_sin_sub_self_le (y - x)) (by linarith [cube_le_tau he hτ0 hτ1 (by linarith)])
      (c := τ * (wo + wp) ^ 3 / 6)
    have hb0 : 0 ≤ bzd := le_trans (abs_nonneg _) hbzd
    calc |zd| * |sin (y - x) - (y - x)| ≤ bzd * (τ * (wo + wp) ^ 3 / 6) :=
          mul_le_mul hbzd this (abs_nonneg _) hb0
      _ = τ * (bzd * (wo + wp) ^ 3 / 6) := by ring
  -- the approximation of the linear form
  have a1 : |(cos α - C) * dx| ≤ eC * (τ * Rx) :=
    by rw [abs_mul]; exact mul_le_mul hC hdx (abs_nonneg _) (le_trans (abs_nonneg _) hC)
  have a2 : |(sin α - S) * dy| ≤ eS * (τ * Ry) :=
    by rw [abs_mul]; exact mul_le_mul hS hdy (abs_nonneg _) (le_trans (abs_nonneg _) hS)
  have a3 : |((Pd - zd) - G) * x| ≤ eG * (τ * wo) :=
    by rw [abs_mul]; exact mul_le_mul hG hx (abs_nonneg _) (le_trans (abs_nonneg _) hG)
  have a4 : |(zd - Z) * y| ≤ eZ * (τ * wp) :=
    by rw [abs_mul]; exact mul_le_mul hZ hy (abs_nonneg _) (le_trans (abs_nonneg _) hZ)
  have e : pgap co cp α β s1 s2
      + (cos α * dx + sin α * dy + (Pd - zd) * x + zd * y)
      + (Pv * (cos x - 1) + Pd * (sin x - x) + (cos α * dx + sin α * dy) * (cos x - 1)
        + (-sin α * dx + cos α * dy) * sin x + z0 * (cos (y - x) - 1) + zd * (sin (y - x) - (y - x)))
      - pgap co cp α β s1 s2 - (C * dx + S * dy + G * x + Z * y)
      = ((cos α - C) * dx + (sin α - S) * dy + ((Pd - zd) - G) * x + (zd - Z) * y)
        + (Pv * (cos x - 1) + Pd * (sin x - x) + (cos α * dx + sin α * dy) * (cos x - 1)
          + (-sin α * dx + cos α * dy) * sin x + z0 * (cos (y - x) - 1)
          + zd * (sin (y - x) - (y - x))) := by ring
  rw [e]
  have t := abs_add_le ((cos α - C) * dx + (sin α - S) * dy + ((Pd - zd) - G) * x + (zd - Z) * y)
    (Pv * (cos x - 1) + Pd * (sin x - x) + (cos α * dx + sin α * dy) * (cos x - 1)
      + (-sin α * dx + cos α * dy) * sin x + z0 * (cos (y - x) - 1)
      + zd * (sin (y - x) - (y - x)))
  have t1 := abs_add_le ((cos α - C) * dx + (sin α - S) * dy + ((Pd - zd) - G) * x) ((zd - Z) * y)
  have t2 := abs_add_le ((cos α - C) * dx + (sin α - S) * dy) (((Pd - zd) - G) * x)
  have t3 := abs_add_le ((cos α - C) * dx) ((sin α - S) * dy)
  have u1 := abs_add_le (Pv * (cos x - 1) + Pd * (sin x - x) + (cos α * dx + sin α * dy) * (cos x - 1)
      + (-sin α * dx + cos α * dy) * sin x + z0 * (cos (y - x) - 1)) (zd * (sin (y - x) - (y - x)))
  have u2 := abs_add_le (Pv * (cos x - 1) + Pd * (sin x - x) + (cos α * dx + sin α * dy) * (cos x - 1)
      + (-sin α * dx + cos α * dy) * sin x) (z0 * (cos (y - x) - 1))
  have u3 := abs_add_le (Pv * (cos x - 1) + Pd * (sin x - x) + (cos α * dx + sin α * dy) * (cos x - 1))
      ((-sin α * dx + cos α * dy) * sin x)
  have u4 := abs_add_le (Pv * (cos x - 1) + Pd * (sin x - x)) ((cos α * dx + sin α * dy) * (cos x - 1))
  have u5 := abs_add_le (Pv * (cos x - 1)) (Pd * (sin x - x))
  linarith

/-! ## Wall gaps -/

/-- A wall gap: `σ c_q + κ - (s₁ cos θ + s₂ sin θ)/2`, where `c_q` is a centre coordinate. -/
noncomputable def wgap (cq σ κ θ s1 s2 : ℝ) : ℝ := σ * cq + κ - (s1 * cos θ + s2 * sin θ) / 2

theorem wgap_approx {cq cq' σ κ θ x s1 s2 τ w W eW bF bF' : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hw : 0 ≤ w) (hx : |x| ≤ τ * w)
    (hW : |(-(-s1 * sin θ + s2 * cos θ)) / 2 - W| ≤ eW)
    (hbF : |s1 * cos θ + s2 * sin θ| ≤ bF) (hbF' : |-s1 * sin θ + s2 * cos θ| ≤ bF') :
    |wgap cq' σ κ (θ + x) s1 s2 - wgap cq σ κ θ s1 s2 - (σ * (cq' - cq) + W * x)|
      ≤ τ * (bF * w ^ 2 / 4 + bF' * w ^ 3 / 12 + eW * w) := by
  have e : wgap cq' σ κ (θ + x) s1 s2 - wgap cq σ κ θ s1 s2 - (σ * (cq' - cq) + W * x)
      = ((-(-s1 * sin θ + s2 * cos θ)) / 2 - W) * x
        - ((s1 * cos θ + s2 * sin θ) * (cos x - 1) + (-s1 * sin θ + s2 * cos θ) * (sin x - x)) / 2 := by
    unfold wgap; rw [cos_add, sin_add]; ring
  rw [e]
  have r1 : |(s1 * cos θ + s2 * sin θ) * (cos x - 1)| ≤ bF * (τ * w ^ 2 / 2) := by
    rw [abs_mul]
    exact mul_le_mul hbF (le_trans (abs_cos_sub_one_le x) (by linarith [sq_le_tau hx hτ0 hτ1]))
      (abs_nonneg _) (le_trans (abs_nonneg _) hbF)
  have r2 : |(-s1 * sin θ + s2 * cos θ) * (sin x - x)| ≤ bF' * (τ * w ^ 3 / 6) := by
    rw [abs_mul]
    exact mul_le_mul hbF' (le_trans (abs_sin_sub_self_le x) (by linarith [cube_le_tau hx hτ0 hτ1 hw]))
      (abs_nonneg _) (le_trans (abs_nonneg _) hbF')
  have r3 : |((-(-s1 * sin θ + s2 * cos θ)) / 2 - W) * x| ≤ eW * (τ * w) := by
    rw [abs_mul]; exact mul_le_mul hW hx (abs_nonneg _) (le_trans (abs_nonneg _) hW)
  have t := abs_sub ((-(-s1 * sin θ + s2 * cos θ) / 2 - W) * x)
    (((s1 * cos θ + s2 * sin θ) * (cos x - 1) + (-s1 * sin θ + s2 * cos θ) * (sin x - x)) / 2)
  have t2 := abs_add_le ((s1 * cos θ + s2 * sin θ) * (cos x - 1)) ((-s1 * sin θ + s2 * cos θ) * (sin x - x))
  rw [abs_div, abs_two] at t
  linarith

end SquarePacking.S11Opt.Split
