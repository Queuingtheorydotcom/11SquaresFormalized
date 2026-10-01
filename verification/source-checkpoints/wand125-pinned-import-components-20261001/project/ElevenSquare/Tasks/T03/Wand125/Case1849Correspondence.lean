import ElevenSquare.Tasks.T03.Batch09.Seed1849
import ElevenSquare.Tasks.T03.KernelBoolRefl
import ElevenSquare.Tasks.T03.Wand125.CertificateTransport
import ElevenSquare.Tasks.T03.Wand125.Upstream.S11Opt.Split.U2R.C1849.Data

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace ElevenSquare.Pending.T03.Wand125.Case1849
open SquarePacking.S11Opt.Split.U2R.C1849

theorem bounds : ∀ j ∈ J, j < 16 := by
  exact of_decide_eq_true (by t03_bool_refl)

theorem mask_eq : cellsOf J = caseMask ⟨1849, by decide⟩ := by
  calc
    cellsOf J = Finset.univ.image ElevenSquare.Pending.T03.Batch09.Seed1849.cells := by
      exact of_decide_eq_true (by t03_bool_refl)
    _ = caseMask ⟨1849, by decide⟩ := ElevenSquare.Pending.T03.Batch09.Seed1849.mask_binding

end ElevenSquare.Pending.T03.Wand125.Case1849
