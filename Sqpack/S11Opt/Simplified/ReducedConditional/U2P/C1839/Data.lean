import Sqpack.S11Opt.Split.U2P.Branch

/-! Demand-reduced helper data. Original public helper definitions are unchanged. -/
set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace SquarePacking.S11Opt.Simplified.ReducedConditional.U2P.C1839
open FieldTree
open SquarePacking.S11Opt.Split
open SquarePacking.S11Opt.Split.U2P

def J : List ℕ := [0, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14]

def cs_r : List Cond := []

def cs_rL : List Cond := [(3, (0, 1, 2927102889))]

def cs_rLL : List Cond := [(8, (1, 0, 2910841206)), (3, (0, 1, 2927102889))]

def cs_rLLL : List Cond := [(2, (1, 0, 8813832033)), (8, (1, 0, 2910841206)), (3, (0, 1, 2927102889))]

def cs_rLLR : List Cond := [(2, (-1, 0, -8813832033)), (8, (1, 0, 2910841206)), (3, (0, 1, 2927102889))]

def cs_rLR : List Cond := [(8, (-1, 0, -2910841206)), (3, (0, 1, 2927102889))]

def cs_rR : List Cond := [(3, (0, -1, -2927102889))]

def cs_rRL : List Cond := [(8, (1, 0, 2927102889)), (3, (0, -1, -2927102889))]

def cs_rRLL : List Cond := [(2, (1, 0, 8813832033)), (8, (1, 0, 2927102889)), (3, (0, -1, -2927102889))]

def cs_rRLR : List Cond := [(2, (-1, 0, -8813832033)), (8, (1, 0, 2927102889)), (3, (0, -1, -2927102889))]

def cs_rRR : List Cond := [(8, (-1, 0, -2927102889)), (3, (0, -1, -2927102889))]

end SquarePacking.S11Opt.Simplified.ReducedConditional.U2P.C1839
