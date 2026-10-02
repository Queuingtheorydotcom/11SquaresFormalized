import ElevenSquare.Tasks.T07.GeometryRoleOrder
import ElevenSquare.Tasks.T07.NearCaptureRectangle
import ElevenSquare.Tasks.T07.NearStateRectangle
import ElevenSquare.Tasks.T07.ShortcutSiteCore
import ElevenSquare.Tasks.T07.Case438Certificate

/-! Convert the checked role-ordered near state to the physical case438 certificate.
This handoff is independent of the complete baseline/prior/returned exclusions. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

def RoleFinalNearCertificate : Prop :=
  ∀ (S : ℝ) (Q : Packing 11 coverCap),
    S ≤ T →
    CenteredPacking Q S →
    (∀ i, ClosedCell (roleCell i)
      (normalizeCenter (Q.squares i).center)) →
    IsCharted Q →
    FinalNearRowsHold Q

/-- The closed angular intervals and their rational field boxes are enough for
the focused local packet. This is the weakest checked near-state interface
used by the global composition. -/
def RoleNearBoxCertificate : Prop :=
  ∀ (S : ℝ) (Q : Packing 11 coverCap),
    S ≤ T →
    CenteredPacking Q S →
    (∀ i, ClosedCell (roleCell i)
      (normalizeCenter (Q.squares i).center)) →
    IsCharted Q →
    StateHolds Q nearOuterState

/-- A concrete Lean trace from the closed-cell seed to rows contained in the
checked near packet is sufficient. The seed includes one strict interior point
per occupied cell, and the trace must use only `VerifiedStep` constructors. -/
def RoleSiteNearTrace : Prop :=
  ∃ finalState : PoseState,
    VerifiedTrace (siteSeedFor roleCell) finalState ∧
    NearRowsSubsumed finalState

theorem role_site_trace_to_box_certificate
    (htrace : RoleSiteNearTrace) : RoleNearBoxCertificate := by
  obtain ⟨finalState, trace, hsub⟩ := htrace
  intro S Q _hST _hsmall hrole hchart
  have hseed : StateHolds Q (siteSeedFor roleCell) :=
    siteSeedFor_holds Q roleCell hchart hrole
  exact stateHolds_nearOuterState_of_subsumed Q finalState
    (verified_trace_sound Q hseed trace) hsub

theorem role_final_near_to_box_certificate
    (hfinal : RoleFinalNearCertificate) : RoleNearBoxCertificate := by
  intro S Q hST hsmall hrole hchart
  exact finalNearRows_to_outerState Q (hfinal S Q hST hsmall hrole hchart)

/-- Select a chart-axis representative after the physical owner-to-role
permutation. Center containment and closed-cell labels depend only on the
physical squares and their centers, so both survive this choice. -/
theorem chart_role_order {S : ℝ} (C : Packing 11 coverCap)
    (hsmall : CenteredPacking C S)
    (hrole : ∀ i, ClosedCell (roleCell i)
      (normalizeCenter (C.squares i).center)) :
    ∃ D : Packing 11 coverCap,
      CenteredPacking D S ∧
      (∀ i, ClosedCell (roleCell i)
        (normalizeCenter (D.squares i).center)) ∧
      IsCharted D ∧
      (∀ i, SameSquare (C.squares i) (D.squares i)) := by
  obtain ⟨D, t, ht, hsame⟩ := C.exists_chart
  refine ⟨D, ?_, ?_, ?_, hsame⟩
  · intro i p hp
    exact hsmall i p (((hsame i).closed_iff p).mpr hp)
  · intro i
    rw [← (hsame i).center_eq]
    exact hrole i
  · intro i
    exact ⟨t i, (ht i).1, (ht i).2.1, (ht i).2.2⟩

theorem role_near_box_to_case438_certificate
    (hnear : RoleNearBoxCertificate) : Case438NearCertificate := by
  intro S Q hST hocc hsmall
  obtain ⟨perm, hroles⟩ := occupied_has_role_order Q hocc
  let C : Packing 11 coverCap := relabelPacking Q perm
  have hCsmall : CenteredPacking C S := relabel_centered Q perm hsmall
  obtain ⟨D, hDsmall, hDroles, hDchart, _⟩ :=
    chart_role_order C hCsmall hroles
  have hDnear : StateHolds D nearOuterState :=
    hnear S D hST hDsmall hDroles hDchart
  obtain ⟨R, θ, hRsmall, hrectangle, hpose⟩ :=
    nearOuterState_to_local_packing D S hDsmall hST hDnear
  exact ⟨R, hRsmall, poseDisplacementWithAngles R.squares θ,
    hrectangle, hpose⟩

/-- The final near-row statement supplies exactly the local certificate
required by the global composition. In particular, the owner permutation is
performed before near rows are indexed by construction role. -/
theorem role_final_near_to_case438_certificate
    (hfinal : RoleFinalNearCertificate) : Case438NearCertificate :=
  role_near_box_to_case438_certificate
    (role_final_near_to_box_certificate hfinal)

end
end ElevenSquare.Tasks.T07
