import ElevenSquare.Tasks.T03.AngleBands
import ElevenSquare.Tasks.T03.CornerCertificates
import ElevenSquare.Tasks.T03.BernsteinProjection

namespace ElevenSquare.Pending.T03
noncomputable section

def rationalControl (a b : ℚ) : QPoint := ((1-a*b)/(1+a*b),(a+b)/(1+a*b))

structure BernsteinBandCertificate where
  band : AngleBand
  low : CornerCertificate
  middle : CornerCertificate
  high : CornerCertificate
  deriving DecidableEq, Inhabited

def BernsteinBandCertificate.check (w : BernsteinBandCertificate) (i : Fin 16) (v : QPoint) : Bool :=
  let a := rationalControl w.band.lo w.band.lo
  let m := rationalControl w.band.lo w.band.hi
  let b := rationalControl w.band.hi w.band.hi
  let ls := w.band.domain i
  w.band.check && w.low.check ls v a.1 a.2 &&
    w.middle.check ls v m.1 m.2 && w.high.check ls v b.1 b.2

theorem BernsteinBandCertificate.sound (w : BernsteinBandCertificate) (i : Fin 16) (v : QPoint)
    (h : w.check i v = true) (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell i (normalizeCenter q.center)) (hq : q.axis = chartAxis t)
    (ht0 : (w.band.lo:ℝ) ≤ t) (ht1 : t ≤ (w.band.hi:ℝ)) : OpenSquare q (realPoint v) := by
  simp only [BernsteinBandCertificate.check, Bool.and_eq_true] at h
  have hband := h.1.1.1
  have hp := w.band.contains_center i hband q t hc hcell hq ht0 ht1
  have ha := w.low.sound _ v _ _ h.1.1.2 q.center hp
  have hm := w.middle.sound _ v _ _ h.1.2 q.center hp
  have hb := w.high.sound _ v _ _ h.2 q.center hp
  dsimp [rationalControl] at ha hm hb
  push_cast at ha hm hb
  have hlo : (0:ℝ) ≤ (w.band.lo:ℝ) := by exact_mod_cast (of_decide_eq_true hband).2.2.1
  have hab : (w.band.lo:ℝ) < (w.band.hi:ℝ) := by exact_mod_cast (of_decide_eq_true hband).2.2.2.1
  have hpx := projection_positive_of_controls w.band.lo w.band.hi t
    ((v.1:ℝ)-q.center.1) ((v.2:ℝ)-q.center.2) hlo hab ht0 ht1
    (by simpa [pow_two,two_mul] using ha.1) hm.1 (by simpa [pow_two,two_mul] using hb.1)
  have hnx := projection_positive_of_controls w.band.lo w.band.hi t
    (-((v.1:ℝ)-q.center.1)) (-((v.2:ℝ)-q.center.2)) hlo hab ht0 ht1
    (by simp only [pow_two,two_mul]; nlinarith only [ha.2.1])
    (by nlinarith only [hm.2.1])
    (by simp only [pow_two,two_mul]; nlinarith only [hb.2.1])
  have hpy := projection_positive_of_controls w.band.lo w.band.hi t
    ((v.2:ℝ)-q.center.2) (-((v.1:ℝ)-q.center.1)) hlo hab ht0 ht1
    (by simp only [pow_two,two_mul]; nlinarith only [ha.2.2.1])
    (by nlinarith only [hm.2.2.1])
    (by simp only [pow_two,two_mul]; nlinarith only [hb.2.2.1])
  have hny := projection_positive_of_controls w.band.lo w.band.hi t
    (-((v.2:ℝ)-q.center.2)) ((v.1:ℝ)-q.center.1) hlo hab ht0 ht1
    (by simp only [pow_two,two_mul]; nlinarith only [ha.2.2.2])
    (by nlinarith only [hm.2.2.2])
    (by simp only [pow_two,two_mul]; nlinarith only [hb.2.2.2])
  have hh := openSquare_of_chart_quadratics q (realPoint v-q.center) t hq
    (by simpa [realPoint] using hpx) (by dsimp [realPoint]; nlinarith only [hnx])
    (by dsimp [realPoint]; nlinarith only [hpy]) (by dsimp [realPoint]; nlinarith only [hny])
  simpa only [add_sub_cancel] using hh

end
end ElevenSquare.Pending.T03
