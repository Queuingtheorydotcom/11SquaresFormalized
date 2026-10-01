import Lake
open Lake DSL

package elevenSquare where
  moreLeanArgs := #["-DautoImplicit=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "3fef63ff3bda38478ba4364ff03999f0246745a2"

@[default_target]
lean_lib ElevenSquare
