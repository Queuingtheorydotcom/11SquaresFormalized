import Sqpack.S11Opt.Simplified.SelectedFieldData
import Sqpack.S11Opt.F00.Final
import Sqpack.S11Opt.Bundled.F01.Final
import Sqpack.S11Opt.Bundled.F02.Final
import Sqpack.S11Opt.Bundled.F03.Final
import Sqpack.S11Opt.Bundled.F04.Final
import Sqpack.S11Opt.Bundled.F05.Final
import Sqpack.S11Opt.Bundled.F06.Final
import Sqpack.S11Opt.Bundled.F07.Final
import Sqpack.S11Opt.Bundled.F08.Final
import Sqpack.S11Opt.Bundled.F09.Final
import Sqpack.S11Opt.Bundled.F10.Final
import Sqpack.S11Opt.Bundled.F11.Final
import Sqpack.S11Opt.Bundled.F12.Final
import Sqpack.S11Opt.Bundled.F15.Final
import Sqpack.S11Opt.Bundled.F18.Final
import Sqpack.S11Opt.Bundled.F19.Final
import Sqpack.S11Opt.Bundled.F20.Final
import Sqpack.S11Opt.Bundled.F21.Final
import Sqpack.S11Opt.Bundled.F23.Final
import Sqpack.S11Opt.Bundled.F25.Final
import Sqpack.S11Opt.Bundled.F26.Final
import Sqpack.S11Opt.Bundled.F27.Final
import Sqpack.S11Opt.Bundled.F31.Final
import Sqpack.S11Opt.Bundled.F33.Final
import Sqpack.S11Opt.Bundled.F35.Final
import Sqpack.S11Opt.Bundled.F36.Final
import Sqpack.S11Opt.Bundled.F37.Final
import Sqpack.S11Opt.Bundled.F38.Final
import Sqpack.S11Opt.Bundled.F39.Final
import Sqpack.S11Opt.Bundled.F40.Final
import Sqpack.S11Opt.Bundled.F41.Final
import Sqpack.S11Opt.Bundled.F43.Final
import Sqpack.S11Opt.Bundled.F44.Final
import Sqpack.S11Opt.Bundled.F45.Final
import Sqpack.S11Opt.Bundled.F46.Final
import Sqpack.S11Opt.Bundled.F47.Final
import Sqpack.S11Opt.Bundled.F48.Final
import Sqpack.S11Opt.Bundled.F50.Final
import Sqpack.S11Opt.Bundled.F52.Final
import Sqpack.S11Opt.Bundled.F53.Final
import Sqpack.S11Opt.Bundled.F55.Final
import Sqpack.S11Opt.Bundled.F56.Final
import Sqpack.S11Opt.Bundled.F57.Final
import Sqpack.S11Opt.Bundled.F58.Final

/-! The 44 selected certificates exclude the same 1,904 field cases.
The omitted certificates overlap these cases and are not needed. -/
namespace SquarePacking.S11Opt.Simplified.SelectedFields
open SquarePacking.S11Opt.Split

theorem app00_sound {J : List ℕ} (h : app00 J = true) : CaseExcluded J := by
  change F00.supp.all (· ∈ J) = true at h
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact fun hR => F00.caseExcluded_supp (hR.mono h)

theorem app_sound {J : List ℕ} (h : app J = true) : CaseExcluded J := by
  simp only [app, Bool.or_eq_true] at h
  rcases h with (((((((((((((((((((((((((((((((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · exact app00_sound h
  · exact Bundled.F01.applicable_sound h
  · exact Bundled.F02.applicable_sound h
  · exact Bundled.F03.applicable_sound h
  · exact Bundled.F04.applicable_sound h
  · exact Bundled.F05.applicable_sound h
  · exact Bundled.F06.applicable_sound h
  · exact Bundled.F07.applicable_sound h
  · exact Bundled.F08.applicable_sound h
  · exact Bundled.F09.applicable_sound h
  · exact Bundled.F10.applicable_sound h
  · exact Bundled.F11.applicable_sound h
  · exact Bundled.F12.applicable_sound h
  · exact Bundled.F15.applicable_sound h
  · exact Bundled.F18.applicable_sound h
  · exact Bundled.F19.applicable_sound h
  · exact Bundled.F20.applicable_sound h
  · exact Bundled.F21.applicable_sound h
  · exact Bundled.F23.applicable_sound h
  · exact Bundled.F25.applicable_sound h
  · exact Bundled.F26.applicable_sound h
  · exact Bundled.F27.applicable_sound h
  · exact Bundled.F31.applicable_sound h
  · exact Bundled.F33.applicable_sound h
  · exact Bundled.F35.applicable_sound h
  · exact Bundled.F36.applicable_sound h
  · exact Bundled.F37.applicable_sound h
  · exact Bundled.F38.applicable_sound h
  · exact Bundled.F39.applicable_sound h
  · exact Bundled.F40.applicable_sound h
  · exact Bundled.F41.applicable_sound h
  · exact Bundled.F43.applicable_sound h
  · exact Bundled.F44.applicable_sound h
  · exact Bundled.F45.applicable_sound h
  · exact Bundled.F46.applicable_sound h
  · exact Bundled.F47.applicable_sound h
  · exact Bundled.F48.applicable_sound h
  · exact Bundled.F50.applicable_sound h
  · exact Bundled.F52.applicable_sound h
  · exact Bundled.F53.applicable_sound h
  · exact Bundled.F55.applicable_sound h
  · exact Bundled.F56.applicable_sound h
  · exact Bundled.F57.applicable_sound h
  · exact Bundled.F58.applicable_sound h

/-- The unchanged complete field-family contract. -/
theorem field_excluded : ∀ i < 2184, i ∉ candIdx → i ∉ genericIdx → i ∉ priorIdx →
    i ∉ returnedIdx → CaseExcluded (maskAt i) := by
  intro i hi hc hg hp hr
  have hf : i ∈ fieldIdx := by
    simp [fieldIdx, hi, hc, hg, hp, hr]
  have happ := fieldIdx_app i hf
  simp only [Bool.or_eq_true] at happ
  rcases happ with happ | happ
  · exact app_sound happ
  · have hcanonical : maskAt i ∈ canonicalMasks :=
      mem_canonical_iff_maskAt.mpr ⟨i, hi, rfl⟩
    exact fun hR => app_sound happ (hR.hmask (canonicalMasks_lt _ hcanonical))

-- The exact native-certificate audit requires full names inside this namespace.
set_option pp.fullNames true in
#print axioms app_sound
set_option pp.fullNames true in
#print axioms field_excluded
end SquarePacking.S11Opt.Simplified.SelectedFields
