import ElevenSquare.Tasks.T07.Ext.Case438
import ElevenSquare.Tasks.T07.ConditionalGlobal

/-! `RoleNearBoxCertificate` and `Case438NearCertificate` from `role_near_box_state`. -/
namespace ElevenSquare.Tasks.T07.Ext
open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07

theorem role_near_box_certificate : RoleNearBoxCertificate :=
  fun _ Q _ _ hrole hchart => role_near_box_state Q hrole hchart

theorem case438_near_certificate' : Case438NearCertificate :=
  role_near_box_to_case438_certificate role_near_box_certificate

end ElevenSquare.Tasks.T07.Ext
