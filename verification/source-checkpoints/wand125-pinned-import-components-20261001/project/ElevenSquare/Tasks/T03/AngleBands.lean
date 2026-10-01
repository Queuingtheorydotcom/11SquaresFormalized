import ElevenSquare.Tasks.T03.CellPhysical
import ElevenSquare.Tasks.T03.ChartIntervals

namespace ElevenSquare.Pending.T03
noncomputable section

structure AngleBand where
  lo : ℚ
  hi : ℚ
  wallNum : ℤ
  wallDen : ℕ
  deriving DecidableEq, Inhabited

def AngleBand.width (r : AngleBand) : ℚ := 2*r.wallNum/r.wallDen

def AngleBand.check (r : AngleBand) : Bool := decide
  (0 < r.wallDen ∧ 0 ≤ r.width ∧ 0 ≤ r.lo ∧ r.lo < r.hi ∧ r.hi ≤ 1 ∧
    0 ≤ 1-r.width+2*r.lo-(1+r.width)*r.lo^2 ∧
    0 ≤ 1-r.width+2*r.hi-(1+r.width)*r.hi^2)

def wallPlanes (n : ℤ) (d : ℕ) : List IntegerPlane :=
  [⟨-d,0,-n⟩,⟨100000000000000000000*d,0,
      387708359002281417731*d-100000000000000000000*n⟩,
   ⟨0,-d,-n⟩,⟨0,100000000000000000000*d,
      387708359002281417731*d-100000000000000000000*n⟩]

theorem wallPlanes_of_bounds (n : ℤ) (d : ℕ) (hd : 0 < d) (p : Point)
    (hx0 : (n:ℝ)/d ≤ p.1) (hx1 : p.1+(n:ℝ)/d ≤ coverCap)
    (hy0 : (n:ℝ)/d ≤ p.2) (hy1 : p.2+(n:ℝ)/d ≤ coverCap) :
    p ∈ IntegerCarrier (wallPlanes n d) := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hx0' := (div_le_iff hd').mp hx0
  have hy0' := (div_le_iff hd').mp hy0
  have hx1' := (div_le_iff hd').mp
    (show (n:ℝ)/d ≤ coverCap-p.1 by linarith)
  have hy1' := (div_le_iff hd').mp
    (show (n:ℝ)/d ≤ coverCap-p.2 by linarith)
  dsimp [coverCap] at hx1' hy1'
  change ∀ l ∈ wallPlanes n d, l.holds p
  simp only [wallPlanes, List.forall_mem_cons, List.forall_mem_nil, and_true]
  norm_num [IntegerPlane.holds]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

def AngleBand.domain (r : AngleBand) (i : Fin 16) : List IntegerPlane :=
  physicalCell i ++ wallPlanes r.wallNum r.wallDen

theorem AngleBand.contains_center (r : AngleBand) (i : Fin 16) (h : r.check = true)
    (q : UnitSquare) (t : ℝ) (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell i (normalizeCenter q.center)) (hq : q.axis = chartAxis t)
    (ht0 : (r.lo:ℝ) ≤ t) (ht1 : t ≤ (r.hi:ℝ)) :
    q.center ∈ IntegerCarrier (r.domain i) := by
  obtain ⟨hd,hw,_,hab,_,ha,hb⟩ := of_decide_eq_true h
  have hw' : (0:ℝ) ≤ (r.width:ℝ) := by exact_mod_cast hw
  have hab' : (r.lo:ℝ) < (r.hi:ℝ) := by exact_mod_cast hab
  have ha' : (0:ℝ) ≤ 1-(r.width:ℝ)+2*(r.lo:ℝ)-(1+(r.width:ℝ))*(r.lo:ℝ)^2 := by
    exact_mod_cast ha
  have hb' : (0:ℝ) ≤ 1-(r.width:ℝ)+2*(r.hi:ℝ)-(1+(r.width:ℝ))*(r.hi:ℝ)^2 := by
    exact_mod_cast hb
  have hwall := contained_interval_wall_bounds q coverCap r.lo r.hi r.width t
    hc hq hw' hab' ht0 ht1 ha' hb'
  have he : (r.width:ℝ)/2 = (r.wallNum:ℝ)/r.wallDen := by
    simp [AngleBand.width]
    ring
  rw [he] at hwall
  have hp := (physicalCell_correct i q.center).mpr hcell
  have hwp := wallPlanes_of_bounds r.wallNum r.wallDen hd q.center
    hwall.1 hwall.2.1 hwall.2.2.1 hwall.2.2.2
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · exact hp l hl
  · exact hwp l hl

end
end ElevenSquare.Pending.T03
