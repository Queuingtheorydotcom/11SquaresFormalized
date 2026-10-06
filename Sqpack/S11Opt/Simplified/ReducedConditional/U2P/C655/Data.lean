import Sqpack.S11Opt.Split.U2P.Branch

/-! Demand-reduced helper data. Original public helper definitions are unchanged. -/
set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace SquarePacking.S11Opt.Simplified.ReducedConditional.U2P.C655
open FieldTree
open SquarePacking.S11Opt.Split
open SquarePacking.S11Opt.Split.U2P

def J : List ℕ := [0, 1, 2, 3, 5, 8, 10, 11, 12, 13, 15]

def cs_r : List Cond := []

def cs_rL : List Cond := [(15, (1, 0, 13724860214))]

def cs_rLL : List Cond := [(0, (0, 1, 3317383274)), (15, (1, 0, 13724860214))]

def cs_rLR : List Cond := [(0, (0, -1, -3317383274)), (15, (1, 0, 13724860214))]

def cs_rLRL : List Cond := [(11, (0, 1, 8781308668)), (0, (0, -1, -3317383274)), (15, (1, 0, 13724860214))]

def cs_rLRR : List Cond := [(11, (0, -1, -8781308668)), (0, (0, -1, -3317383274)), (15, (1, 0, 13724860214))]

def cs_rR : List Cond := [(15, (-1, 0, -13724860214))]

def cs_rRL : List Cond := [(11, (0, 1, 8781308668)), (15, (-1, 0, -13724860214))]

def cs_rRR : List Cond := [(11, (0, -1, -8781308668)), (15, (-1, 0, -13724860214))]

end SquarePacking.S11Opt.Simplified.ReducedConditional.U2P.C655
