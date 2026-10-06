import ElevenSquare.Pending.S07_IntegerBounds

/-! Exact, kernel-checked infeasibility certificates for closed-cell prefixes.
The certificates use nonnegative combinations of original integer halfplanes,
so boundary points and independent tie labels are retained. -/
namespace ElevenSquare.Pending.T04Completeness

private theorem planes_length (g : Fin 4) (i : Fin 16) :
    (integerViewPlanes g (integerCellPlanes i)).length = 20 := by
  simp [integerViewPlanes, integerCellPlanes, integerBoxPlanes]

def sourcePlane (g : Fin 4) (i : Fin 16) (j : Fin 20) : IntegerPlane :=
  (integerViewPlanes g (integerCellPlanes i)).get
    ⟨j.val, by rw [planes_length]; exact j.isLt⟩

theorem sourcePlane_sound (g : Fin 4) (i : Fin 16) (j : Fin 20)
    (p : Point) (h : ClosedCell i (view g p)) :
    (sourcePlane g i j).rational.contains p := by
  have hp := (integerViewPlanes_correct g (integerCellPlanes i) p).mpr
    ((integerCellPlanes_correct i (view g p)).mpr h)
  exact hp _ (List.get_mem _ _)

def refutationCheck (l m n : IntegerPlane) (u v w : ℤ) : Bool :=
  decide (0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧
    u*l.a + v*m.a + w*n.a = 0 ∧
    u*l.b + v*m.b + w*n.b = 0 ∧
    u*l.c + v*m.c + w*n.c < 0)

theorem refutationCheck_sound (l m n : IntegerPlane) (u v w : ℤ)
    (h : refutationCheck l m n u v w = true) (p : Point)
    (hl : l.rational.contains p) (hm : m.rational.contains p)
    (hn : n.rational.contains p) : False := by
  have hc := of_decide_eq_true h
  have hs := (l.combine m u v).combine_sound n 1 w (by norm_num) hc.2.2.1 p
    (l.combine_sound m u v hc.1 hc.2.1 p hl hm) hn
  let q := (l.combine m u v).combine n 1 w
  have ha : q.a = 0 := by simpa [q, IntegerPlane.combine] using hc.2.2.2.1
  have hb : q.b = 0 := by simpa [q, IntegerPlane.combine] using hc.2.2.2.2.1
  have hz : q.c < 0 := by simpa [q, IntegerPlane.combine] using hc.2.2.2.2.2
  change (q.a:ℝ)*p.1 + (q.b:ℝ)*p.2 ≤ (q.c:ℝ) at hs
  rw [ha, hb] at hs
  norm_num at hs
  exact (not_le_of_gt hz) hs

theorem reject (p : Point)
    (g₁ : Fin 4) (i₁ : Fin 16) (j₁ : Fin 20)
    (g₂ : Fin 4) (i₂ : Fin 16) (j₂ : Fin 20)
    (g₃ : Fin 4) (i₃ : Fin 16) (j₃ : Fin 20)
    (u v w : ℤ)
    (h₁ : ClosedCell i₁ (view g₁ p))
    (h₂ : ClosedCell i₂ (view g₂ p))
    (h₃ : ClosedCell i₃ (view g₃ p))
    (hc : refutationCheck (sourcePlane g₁ i₁ j₁)
      (sourcePlane g₂ i₂ j₂) (sourcePlane g₃ i₃ j₃) u v w = true) : False :=
  refutationCheck_sound _ _ _ _ _ _ hc p
    (sourcePlane_sound g₁ i₁ j₁ p h₁)
    (sourcePlane_sound g₂ i₂ j₂ p h₂)
    (sourcePlane_sound g₃ i₃ j₃ p h₃)

end ElevenSquare.Pending.T04Completeness
