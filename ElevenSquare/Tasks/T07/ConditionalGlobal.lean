import ElevenSquare.Tasks.T07.RoleNearCertificate
import ElevenSquare.Tasks.T07.GeometryRoles
import ElevenSquare.Tasks.T07.GlobalComposition

/-! Compose independent case438 capture certificates with the global case reduction. -/
namespace ElevenSquare.Tasks.T07
open ElevenSquare.Pending
noncomputable section

theorem global_lower_bound_of_role_near_box
    (hnear : RoleNearBoxCertificate)
    {S : ℝ} (P : Packing 11 S) : T ≤ S :=
  global_lower_bound_of_case438_certificate
    (role_near_box_to_case438_certificate hnear) P

theorem global_lower_bound_of_role_site_trace
    (htrace : RoleSiteNearTrace)
    {S : ℝ} (P : Packing 11 S) : T ≤ S :=
  global_lower_bound_of_role_near_box
    (role_site_trace_to_box_certificate htrace) P

theorem global_lower_bound_of_role_final_near
    (hfinal : RoleFinalNearCertificate)
    {S : ℝ} (P : Packing 11 S) : T ≤ S :=
  global_lower_bound_of_case438_certificate
    (role_final_near_to_case438_certificate hfinal) P

end
end ElevenSquare.Tasks.T07
