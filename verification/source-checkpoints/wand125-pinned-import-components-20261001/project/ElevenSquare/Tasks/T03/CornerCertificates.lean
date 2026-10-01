import ElevenSquare.Tasks.T03.ProjectionCertificates

namespace ElevenSquare.Pending.T03
noncomputable section

structure CornerCertificate where
  posX : ProjectionCertificate
  negX : ProjectionCertificate
  posY : ProjectionCertificate
  negY : ProjectionCertificate
  deriving DecidableEq, Inhabited

def CornerCertificate.check (w : CornerCertificate) (ls : List IntegerPlane)
    (v : QPoint) (c s : ℚ) : Bool :=
  w.posX.check ls v (c,s) && w.negX.check ls v (-c,-s) &&
  w.posY.check ls v (-s,c) && w.negY.check ls v (s,-c)

theorem CornerCertificate.sound (w : CornerCertificate) (ls : List IntegerPlane)
    (v : QPoint) (c s : ℚ) (h : w.check ls v c s = true) (p : Point)
    (hp : p ∈ IntegerCarrier ls) :
    (c:ℝ)*((v.1:ℝ)-p.1)+(s:ℝ)*((v.2:ℝ)-p.2) < 1/2 ∧
    -(c:ℝ)*((v.1:ℝ)-p.1)-(s:ℝ)*((v.2:ℝ)-p.2) < 1/2 ∧
    -(s:ℝ)*((v.1:ℝ)-p.1)+(c:ℝ)*((v.2:ℝ)-p.2) < 1/2 ∧
    (s:ℝ)*((v.1:ℝ)-p.1)-(c:ℝ)*((v.2:ℝ)-p.2) < 1/2 := by
  simp only [CornerCertificate.check, Bool.and_eq_true] at h
  have hpx := w.posX.sound ls v (c,s) h.1.1.1 p hp
  have hnx := w.negX.sound ls v (-c,-s) h.1.1.2 p hp
  have hpy := w.posY.sound ls v (-s,c) h.1.2 p hp
  have hny := w.negY.sound ls v (s,-c) h.2 p hp
  norm_num only [Rat.cast_neg, Prod.fst, Prod.snd] at hpx hnx hpy hny
  exact ⟨hpx, by linarith only [hnx], hpy, by linarith only [hny]⟩

end
end ElevenSquare.Pending.T03
