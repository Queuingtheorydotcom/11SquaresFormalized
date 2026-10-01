import ElevenSquare.Tasks.T03.AngleBands

namespace ElevenSquare.Pending.T03
noncomputable section

structure PoseBandCertificate where
  band : AngleBand
  cuts : List (IntegerPlane × LinearCertificate)

def PoseBandCertificate.row (w : PoseBandCertificate) : PoseRow :=
  ⟨w.band.lo,w.band.hi,(w.cuts.map Prod.fst).map IntegerPlane.rational⟩

def PoseBandCertificate.check (w : PoseBandCertificate) (i : Fin 16) : Bool :=
  w.band.check && decide (∀ pair ∈ w.cuts, pair.2.check (w.band.domain i) pair.1 = true)

theorem PoseBandCertificate.sound (w : PoseBandCertificate) (i : Fin 16)
    (h : w.check i = true) (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell i (normalizeCenter q.center)) (hq : q.axis = chartAxis t)
    (ht0 : (w.band.lo:ℝ) ≤ t) (ht1 : t ≤ (w.band.hi:ℝ)) : w.row.contains q := by
  simp only [PoseBandCertificate.check, Bool.and_eq_true, decide_eq_true_eq] at h
  have hp := w.band.contains_center i h.1 q t hc hcell hq ht0 ht1
  have hb := of_decide_eq_true h.1
  have hlo : (0:ℝ) ≤ (w.band.lo:ℝ) := by exact_mod_cast hb.2.2.1
  have hhi : (w.band.hi:ℝ) ≤ 1 := by exact_mod_cast hb.2.2.2.2.1
  refine ⟨?_,t,by linarith,by linarith,ht0,ht1,hq⟩
  change q.center ∈ Polygon.carrier ((w.cuts.map Prod.fst).map IntegerPlane.rational)
  rw [← integerCarrier_as_polygon]
  intro l hl
  obtain ⟨pair,hpair,rfl⟩ := List.mem_map.mp hl
  exact pair.2.sound _ pair.1 (h.2 pair hpair) hp

inductive PoseTemplate where
  | leaf : PoseBandCertificate → PoseTemplate
  | split : ℚ → PoseTemplate → PoseTemplate → PoseTemplate

def PoseTemplate.rows : PoseTemplate → List PoseRow
  | .leaf w => [w.row]
  | .split _ left right => left.rows ++ right.rows

def PoseTemplate.check (i : Fin 16) (lo hi : ℚ) : PoseTemplate → Bool
  | .leaf w => decide (w.band.lo=lo ∧ w.band.hi=hi) && w.check i
  | .split mid left right => left.check i lo mid && right.check i mid hi

theorem PoseTemplate.sound (tree : PoseTemplate) (i : Fin 16) (lo hi : ℚ)
    (h : tree.check i lo hi = true) (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell i (normalizeCenter q.center)) (hq : q.axis = chartAxis t)
    (ht0 : (lo:ℝ) ≤ t) (ht1 : t ≤ (hi:ℝ)) : RowsContain tree.rows q := by
  induction tree generalizing lo hi with
  | leaf w =>
    simp only [PoseTemplate.check, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨w.row,by simp [PoseTemplate.rows],w.sound i h.2 q t hc hcell hq
      (by simpa [h.1.1] using ht0) (by simpa [h.1.2] using ht1)⟩
  | split mid left right ihl ihr =>
    simp only [PoseTemplate.check, Bool.and_eq_true] at h
    by_cases hm : t ≤ (mid:ℝ)
    · obtain ⟨r,hr,hq'⟩ := ihl lo mid h.1 ht0 hm
      exact ⟨r,List.mem_append_left _ hr,hq'⟩
    · obtain ⟨r,hr,hq'⟩ := ihr mid hi h.2 (le_of_lt (lt_of_not_ge hm)) ht1
      exact ⟨r,List.mem_append_right _ hr,hq'⟩

end
end ElevenSquare.Pending.T03
