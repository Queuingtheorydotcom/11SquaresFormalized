import Sqpack.S11Opt.F01.Data
import Sqpack.S11Opt.F02.Data
import Sqpack.S11Opt.F03.Data
import Sqpack.S11Opt.F04.Data
import Sqpack.S11Opt.F05.Data
import Sqpack.S11Opt.F06.Data
import Sqpack.S11Opt.F07.Data
import Sqpack.S11Opt.F08.Data
import Sqpack.S11Opt.F09.Data
import Sqpack.S11Opt.F10.Data
import Sqpack.S11Opt.F11.Data
import Sqpack.S11Opt.F12.Data
import Sqpack.S11Opt.F15.Data
import Sqpack.S11Opt.F18.Data
import Sqpack.S11Opt.F19.Data
import Sqpack.S11Opt.F20.Data
import Sqpack.S11Opt.F21.Data
import Sqpack.S11Opt.F23.Data
import Sqpack.S11Opt.F25.Data
import Sqpack.S11Opt.F26.Data
import Sqpack.S11Opt.F27.Data
import Sqpack.S11Opt.F31.Data
import Sqpack.S11Opt.F33.Data
import Sqpack.S11Opt.F35.Data
import Sqpack.S11Opt.F36.Data
import Sqpack.S11Opt.F37.Data
import Sqpack.S11Opt.F38.Data
import Sqpack.S11Opt.F39.Data
import Sqpack.S11Opt.F40.Data
import Sqpack.S11Opt.F41.Data
import Sqpack.S11Opt.F43.Data
import Sqpack.S11Opt.F44.Data
import Sqpack.S11Opt.F45.Data
import Sqpack.S11Opt.F46.Data
import Sqpack.S11Opt.F47.Data
import Sqpack.S11Opt.F48.Data
import Sqpack.S11Opt.F50.Data
import Sqpack.S11Opt.F52.Data
import Sqpack.S11Opt.F53.Data
import Sqpack.S11Opt.F55.Data
import Sqpack.S11Opt.F56.Data
import Sqpack.S11Opt.F57.Data
import Sqpack.S11Opt.F58.Data
import Sqpack.S11Opt.Split.Interface

/-! A source-minimal selection from the existing 59 field certificates.
This module checks only the complete finite case coverage; it imports no
selected field cover proofs. Closed cells and the half-turn are unchanged. -/
namespace SquarePacking.S11Opt.Simplified.SelectedFields
open SquarePacking.S11Opt.Split

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def app00 (J : List ℕ) : Bool :=
  ([1, 2, 4, 5, 8, 9, 13] : List ℕ).all (· ∈ J)

noncomputable def app01 (J : List ℕ) : Bool :=
  F01.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F01.atoms.length, F01.wts.getD a 0) <
      ((F01.pos.filter (· ∈ J)).map (F01.gam.getD · 0)).sum)

noncomputable def app02 (J : List ℕ) : Bool :=
  F02.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F02.atoms.length, F02.wts.getD a 0) <
      ((F02.pos.filter (· ∈ J)).map (F02.gam.getD · 0)).sum)

noncomputable def app03 (J : List ℕ) : Bool :=
  F03.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F03.atoms.length, F03.wts.getD a 0) <
      ((F03.pos.filter (· ∈ J)).map (F03.gam.getD · 0)).sum)

noncomputable def app04 (J : List ℕ) : Bool :=
  F04.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F04.atoms.length, F04.wts.getD a 0) <
      ((F04.pos.filter (· ∈ J)).map (F04.gam.getD · 0)).sum)

noncomputable def app05 (J : List ℕ) : Bool :=
  F05.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F05.atoms.length, F05.wts.getD a 0) <
      ((F05.pos.filter (· ∈ J)).map (F05.gam.getD · 0)).sum)

noncomputable def app06 (J : List ℕ) : Bool :=
  F06.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F06.atoms.length, F06.wts.getD a 0) <
      ((F06.pos.filter (· ∈ J)).map (F06.gam.getD · 0)).sum)

noncomputable def app07 (J : List ℕ) : Bool :=
  F07.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F07.atoms.length, F07.wts.getD a 0) <
      ((F07.pos.filter (· ∈ J)).map (F07.gam.getD · 0)).sum)

noncomputable def app08 (J : List ℕ) : Bool :=
  F08.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F08.atoms.length, F08.wts.getD a 0) <
      ((F08.pos.filter (· ∈ J)).map (F08.gam.getD · 0)).sum)

noncomputable def app09 (J : List ℕ) : Bool :=
  F09.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F09.atoms.length, F09.wts.getD a 0) <
      ((F09.pos.filter (· ∈ J)).map (F09.gam.getD · 0)).sum)

noncomputable def app10 (J : List ℕ) : Bool :=
  F10.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F10.atoms.length, F10.wts.getD a 0) <
      ((F10.pos.filter (· ∈ J)).map (F10.gam.getD · 0)).sum)

noncomputable def app11 (J : List ℕ) : Bool :=
  F11.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F11.atoms.length, F11.wts.getD a 0) <
      ((F11.pos.filter (· ∈ J)).map (F11.gam.getD · 0)).sum)

noncomputable def app12 (J : List ℕ) : Bool :=
  F12.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F12.atoms.length, F12.wts.getD a 0) <
      ((F12.pos.filter (· ∈ J)).map (F12.gam.getD · 0)).sum)

noncomputable def app15 (J : List ℕ) : Bool :=
  F15.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F15.atoms.length, F15.wts.getD a 0) <
      ((F15.pos.filter (· ∈ J)).map (F15.gam.getD · 0)).sum)

noncomputable def app18 (J : List ℕ) : Bool :=
  F18.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F18.atoms.length, F18.wts.getD a 0) <
      ((F18.pos.filter (· ∈ J)).map (F18.gam.getD · 0)).sum)

noncomputable def app19 (J : List ℕ) : Bool :=
  F19.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F19.atoms.length, F19.wts.getD a 0) <
      ((F19.pos.filter (· ∈ J)).map (F19.gam.getD · 0)).sum)

noncomputable def app20 (J : List ℕ) : Bool :=
  F20.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F20.atoms.length, F20.wts.getD a 0) <
      ((F20.pos.filter (· ∈ J)).map (F20.gam.getD · 0)).sum)

noncomputable def app21 (J : List ℕ) : Bool :=
  F21.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F21.atoms.length, F21.wts.getD a 0) <
      ((F21.pos.filter (· ∈ J)).map (F21.gam.getD · 0)).sum)

noncomputable def app23 (J : List ℕ) : Bool :=
  F23.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F23.atoms.length, F23.wts.getD a 0) <
      ((F23.pos.filter (· ∈ J)).map (F23.gam.getD · 0)).sum)

noncomputable def app25 (J : List ℕ) : Bool :=
  F25.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F25.atoms.length, F25.wts.getD a 0) <
      ((F25.pos.filter (· ∈ J)).map (F25.gam.getD · 0)).sum)

noncomputable def app26 (J : List ℕ) : Bool :=
  F26.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F26.atoms.length, F26.wts.getD a 0) <
      ((F26.pos.filter (· ∈ J)).map (F26.gam.getD · 0)).sum)

noncomputable def app27 (J : List ℕ) : Bool :=
  F27.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F27.atoms.length, F27.wts.getD a 0) <
      ((F27.pos.filter (· ∈ J)).map (F27.gam.getD · 0)).sum)

noncomputable def app31 (J : List ℕ) : Bool :=
  F31.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F31.atoms.length, F31.wts.getD a 0) <
      ((F31.pos.filter (· ∈ J)).map (F31.gam.getD · 0)).sum)

noncomputable def app33 (J : List ℕ) : Bool :=
  F33.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F33.atoms.length, F33.wts.getD a 0) <
      ((F33.pos.filter (· ∈ J)).map (F33.gam.getD · 0)).sum)

noncomputable def app35 (J : List ℕ) : Bool :=
  F35.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F35.atoms.length, F35.wts.getD a 0) <
      ((F35.pos.filter (· ∈ J)).map (F35.gam.getD · 0)).sum)

noncomputable def app36 (J : List ℕ) : Bool :=
  F36.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F36.atoms.length, F36.wts.getD a 0) <
      ((F36.pos.filter (· ∈ J)).map (F36.gam.getD · 0)).sum)

noncomputable def app37 (J : List ℕ) : Bool :=
  F37.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F37.atoms.length, F37.wts.getD a 0) <
      ((F37.pos.filter (· ∈ J)).map (F37.gam.getD · 0)).sum)

noncomputable def app38 (J : List ℕ) : Bool :=
  F38.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F38.atoms.length, F38.wts.getD a 0) <
      ((F38.pos.filter (· ∈ J)).map (F38.gam.getD · 0)).sum)

noncomputable def app39 (J : List ℕ) : Bool :=
  F39.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F39.atoms.length, F39.wts.getD a 0) <
      ((F39.pos.filter (· ∈ J)).map (F39.gam.getD · 0)).sum)

noncomputable def app40 (J : List ℕ) : Bool :=
  F40.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F40.atoms.length, F40.wts.getD a 0) <
      ((F40.pos.filter (· ∈ J)).map (F40.gam.getD · 0)).sum)

noncomputable def app41 (J : List ℕ) : Bool :=
  F41.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F41.atoms.length, F41.wts.getD a 0) <
      ((F41.pos.filter (· ∈ J)).map (F41.gam.getD · 0)).sum)

noncomputable def app43 (J : List ℕ) : Bool :=
  F43.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F43.atoms.length, F43.wts.getD a 0) <
      ((F43.pos.filter (· ∈ J)).map (F43.gam.getD · 0)).sum)

noncomputable def app44 (J : List ℕ) : Bool :=
  F44.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F44.atoms.length, F44.wts.getD a 0) <
      ((F44.pos.filter (· ∈ J)).map (F44.gam.getD · 0)).sum)

noncomputable def app45 (J : List ℕ) : Bool :=
  F45.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F45.atoms.length, F45.wts.getD a 0) <
      ((F45.pos.filter (· ∈ J)).map (F45.gam.getD · 0)).sum)

noncomputable def app46 (J : List ℕ) : Bool :=
  F46.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F46.atoms.length, F46.wts.getD a 0) <
      ((F46.pos.filter (· ∈ J)).map (F46.gam.getD · 0)).sum)

noncomputable def app47 (J : List ℕ) : Bool :=
  F47.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F47.atoms.length, F47.wts.getD a 0) <
      ((F47.pos.filter (· ∈ J)).map (F47.gam.getD · 0)).sum)

noncomputable def app48 (J : List ℕ) : Bool :=
  F48.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F48.atoms.length, F48.wts.getD a 0) <
      ((F48.pos.filter (· ∈ J)).map (F48.gam.getD · 0)).sum)

noncomputable def app50 (J : List ℕ) : Bool :=
  F50.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F50.atoms.length, F50.wts.getD a 0) <
      ((F50.pos.filter (· ∈ J)).map (F50.gam.getD · 0)).sum)

noncomputable def app52 (J : List ℕ) : Bool :=
  F52.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F52.atoms.length, F52.wts.getD a 0) <
      ((F52.pos.filter (· ∈ J)).map (F52.gam.getD · 0)).sum)

noncomputable def app53 (J : List ℕ) : Bool :=
  F53.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F53.atoms.length, F53.wts.getD a 0) <
      ((F53.pos.filter (· ∈ J)).map (F53.gam.getD · 0)).sum)

noncomputable def app55 (J : List ℕ) : Bool :=
  F55.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F55.atoms.length, F55.wts.getD a 0) <
      ((F55.pos.filter (· ∈ J)).map (F55.gam.getD · 0)).sum)

noncomputable def app56 (J : List ℕ) : Bool :=
  F56.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F56.atoms.length, F56.wts.getD a 0) <
      ((F56.pos.filter (· ∈ J)).map (F56.gam.getD · 0)).sum)

noncomputable def app57 (J : List ℕ) : Bool :=
  F57.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F57.atoms.length, F57.wts.getD a 0) <
      ((F57.pos.filter (· ∈ J)).map (F57.gam.getD · 0)).sum)

noncomputable def app58 (J : List ℕ) : Bool :=
  F58.supp.all (· ∈ J) &&
    decide ((∑ a ∈ Finset.range F58.atoms.length, F58.wts.getD a 0) <
      ((F58.pos.filter (· ∈ J)).map (F58.gam.getD · 0)).sum)

noncomputable def app (J : List ℕ) : Bool :=
  app00 J ||
  app01 J ||
  app02 J ||
  app03 J ||
  app04 J ||
  app05 J ||
  app06 J ||
  app07 J ||
  app08 J ||
  app09 J ||
  app10 J ||
  app11 J ||
  app12 J ||
  app15 J ||
  app18 J ||
  app19 J ||
  app20 J ||
  app21 J ||
  app23 J ||
  app25 J ||
  app26 J ||
  app27 J ||
  app31 J ||
  app33 J ||
  app35 J ||
  app36 J ||
  app37 J ||
  app38 J ||
  app39 J ||
  app40 J ||
  app41 J ||
  app43 J ||
  app44 J ||
  app45 J ||
  app46 J ||
  app47 J ||
  app48 J ||
  app50 J ||
  app52 J ||
  app53 J ||
  app55 J ||
  app56 J ||
  app57 J ||
  app58 J

def fieldIdx : List ℕ :=
  (List.range 2184).filter fun i =>
    !(decide (i ∈ candIdx) || decide (i ∈ genericIdx) || decide (i ∈ priorIdx) ||
      decide (i ∈ returnedIdx))

/-- Direct exclusion test; avoids recomputing the complete filtered list per index. -/
def outsideField (i : ℕ) : Bool :=
  decide (i ∈ candIdx) || decide (i ∈ genericIdx) || decide (i ∈ priorIdx) ||
    decide (i ∈ returnedIdx)

end SquarePacking.S11Opt.Simplified.SelectedFields
