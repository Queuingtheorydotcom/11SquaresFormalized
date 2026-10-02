import ElevenSquare.Tasks.T02.Prior1000Step000Row063.SharedCoreInteger.Checks
import ElevenSquare.Tasks.T02.Prior1000Step000Row063.SharedCoreInteger.Forbidden
import ElevenSquare.Tasks.T02.IntegerPruning

namespace ElevenSquare.Tasks.T02.Prior1000Step000Row063.SharedCoreInteger
open ElevenSquare.Pending ElevenSquare.Tasks.T02
open IntegerCover
noncomputable section

theorem row_retained {S : ℝ} (P : Packing 11 S) (s : PoseState)
    (hs : StateHolds P s) (ho : s.owned = ownedByRole)
    (hq : inputRow.contains (P.squares (4 : Owner))) :
    retainedRow.contains (P.squares (4 : Owner)) := by
  have hf : ∀ p ∈ certificate.forbidden, p.Check s (4 : Owner) inputRow := by
    simpa only [ForbiddenPiece.Check, checkState, ho] using forbidden_checked
  rcases integer_row_pruning_sound s (4 : Owner) inputRow certificate integerCertificate
      coverage_checked hf _ hq with hk | hb
  · obtain ⟨r, hr, hcontains⟩ := hk
    have he : r = retainedRow := by
      simpa only [RowPruningCertificate.keptRows, certificate, inputRow, retainedRow,
        List.map_cons, List.map_nil, List.mem_singleton] using hr
    exact he ▸ hcontains
  · obtain ⟨j, hij, Q, hcore, hforbidden⟩ := hb
    obtain ⟨p, hpi, hpj⟩ := forbidden_center_implies_overlap _ _ _ _ (hs.2 j) hcore hforbidden
    exact False.elim (P.interior_disjoint _ j hij p ⟨hpi, hpj⟩)

end
end ElevenSquare.Tasks.T02.Prior1000Step000Row063.SharedCoreInteger
