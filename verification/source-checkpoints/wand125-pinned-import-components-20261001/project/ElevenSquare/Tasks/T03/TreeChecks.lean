import ElevenSquare.Tasks.T03.OwnershipTree
import ElevenSquare.Tasks.T03.PoseTemplates

namespace ElevenSquare.Pending.T03

theorem OwnershipTree.leaf_checked (w : BernsteinBandCertificate) (i : Fin 16)
    (v : QPoint) (lo hi : ℚ) (hlo : w.band.lo = lo) (hhi : w.band.hi = hi)
    (h : w.check i v = true) : (OwnershipTree.leaf w).check i v lo hi = true := by
  simp [OwnershipTree.check,hlo,hhi,h]

theorem OwnershipTree.split_checked (left right : OwnershipTree) (i : Fin 16)
    (v : QPoint) (lo mid hi : ℚ) (hl : left.check i v lo mid = true)
    (hr : right.check i v mid hi = true) :
    (OwnershipTree.split mid left right).check i v lo hi = true := by
  simp only [OwnershipTree.check,hl,hr,Bool.and_self]

theorem PoseTemplate.leaf_checked (w : PoseBandCertificate) (i : Fin 16)
    (lo hi : ℚ) (hlo : w.band.lo = lo) (hhi : w.band.hi = hi)
    (h : w.check i = true) : (PoseTemplate.leaf w).check i lo hi = true := by
  simp [PoseTemplate.check,hlo,hhi,h]

theorem PoseTemplate.split_checked (left right : PoseTemplate) (i : Fin 16)
    (lo mid hi : ℚ) (hl : left.check i lo mid = true)
    (hr : right.check i mid hi = true) :
    (PoseTemplate.split mid left right).check i lo hi = true := by
  simp only [PoseTemplate.check,hl,hr,Bool.and_self]

end ElevenSquare.Pending.T03
