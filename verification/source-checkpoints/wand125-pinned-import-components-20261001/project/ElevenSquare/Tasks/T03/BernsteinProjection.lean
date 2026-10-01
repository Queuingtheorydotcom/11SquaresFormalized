import ElevenSquare.Tasks.T03.Quadratic

namespace ElevenSquare.Pending.T03
noncomputable section

theorem quadratic_positive_of_controls (A B C lo hi t : ℝ)
    (hab : lo < hi) (hta : lo ≤ t) (htb : t ≤ hi)
    (ha : 0 < A*lo^2+B*lo+C)
    (hm : 0 < A*lo*hi+B*(lo+hi)/2+C)
    (hb : 0 < A*hi^2+B*hi+C) : 0 < A*t^2+B*t+C := by
  let eps := min (A*lo^2+B*lo+C) (min (A*lo*hi+B*(lo+hi)/2+C) (A*hi^2+B*hi+C))
  have he : 0 < eps := lt_min ha (lt_min hm hb)
  have hea := min_le_left (A*lo^2+B*lo+C) (min (A*lo*hi+B*(lo+hi)/2+C) (A*hi^2+B*hi+C))
  have hem : eps ≤ A*lo*hi+B*(lo+hi)/2+C := le_trans (min_le_right _ _) (min_le_left _ _)
  have heb : eps ≤ A*hi^2+B*hi+C := le_trans (min_le_right _ _) (min_le_right _ _)
  exact lt_of_lt_of_le he (quadratic_lower_bound A B C lo hi eps t hab hta htb
    (by dsimp [eps] at *; linarith only [hea])
    (by nlinarith only [hem]) (by linarith only [heb]))

theorem homogeneous_projection_positive (a b x y : ℝ) (hd : 0 < 1+a*b)
    (h : ((1-a*b)/(1+a*b))*x+((a+b)/(1+a*b))*y < 1/2) :
    0 < (1+a*b)/2-(1-a*b)*x-(a+b)*y := by
  have hh : ((1-a*b)*x+(a+b)*y)/(1+a*b) < 1/2 := by
    simpa only [div_mul_eq_mul_div, ← add_div] using h
  have hh' := (div_lt_iff hd).mp hh
  linarith only [hh']

theorem projection_positive_of_controls (lo hi t x y : ℝ)
    (hl : 0 ≤ lo) (hab : lo < hi) (hta : lo ≤ t) (htb : t ≤ hi)
    (ha : ((1-lo^2)/(1+lo^2))*x+(2*lo/(1+lo^2))*y < 1/2)
    (hm : ((1-lo*hi)/(1+lo*hi))*x+((lo+hi)/(1+lo*hi))*y < 1/2)
    (hb : ((1-hi^2)/(1+hi^2))*x+(2*hi/(1+hi^2))*y < 1/2) :
    0 < (1/2+x)*t^2+(-2*y)*t+(1/2-x) := by
  have hhi : 0 ≤ hi := by linarith
  have hda : 0 < 1+lo*lo := by nlinarith [sq_nonneg lo]
  have hdb : 0 < 1+hi*hi := by nlinarith [sq_nonneg hi]
  have hdm : 0 < 1+lo*hi := by nlinarith [mul_nonneg hl hhi]
  have hpa := homogeneous_projection_positive lo lo x y hda (by simpa [pow_two, two_mul] using ha)
  have hpm := homogeneous_projection_positive lo hi x y hdm hm
  have hpb := homogeneous_projection_positive hi hi x y hdb (by simpa [pow_two, two_mul] using hb)
  exact quadratic_positive_of_controls (1/2+x) (-2*y) (1/2-x) lo hi t hab hta htb
    (by nlinarith only [hpa]) (by nlinarith only [hpm]) (by nlinarith only [hpb])

end
end ElevenSquare.Pending.T03
