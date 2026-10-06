import Sqpack.S11Opt.Split.U2P.Branch

/-! Demand-reduced helper data. Original public helper definitions are unchanged. -/
set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace SquarePacking.S11Opt.Simplified.ReducedConditional.U2R.C1465
open FieldTree
open SquarePacking.S11Opt.Split
open SquarePacking.S11Opt.Split.U2P

def J : List ℕ := [0, 1, 3, 5, 6, 8, 10, 11, 12, 13, 15]

def cs_r : List Cond := []

def cs_rL : List Cond := [(0, (0, 1, 3236074860))]

def cs_rLL : List Cond := [(15, (1, 0, 13724860214)), (0, (0, 1, 3236074860))]

def cs_rLR : List Cond := [(15, (-1, 0, -13724860214)), (0, (0, 1, 3236074860))]

def cs_rLRL : List Cond := [(10, (1, 0, 8927663811)), (15, (-1, 0, -13724860214)), (0, (0, 1, 3236074860))]

def cs_rLRR : List Cond := [(10, (-1, 0, -8927663811)), (15, (-1, 0, -13724860214)), (0, (0, 1, 3236074860))]

def cs_rLRRL : List Cond := [(12, (1, 0, 2666915965)), (10, (-1, 0, -8927663811)), (15, (-1, 0, -13724860214)), (0, (0, 1, 3236074860))]

def cs_rLRRLL : List Cond := [(5, (0, 1, 7350280588)), (12, (1, 0, 2666915965)), (10, (-1, 0, -8927663811)), (15, (-1, 0, -13724860214)), (0, (0, 1, 3236074860))]

def cs_rLRRLR : List Cond := [(5, (0, -1, -7350280588)), (12, (1, 0, 2666915965)), (10, (-1, 0, -8927663811)), (15, (-1, 0, -13724860214)), (0, (0, 1, 3236074860))]

def cs_rLRRR : List Cond := [(12, (-1, 0, -2666915965)), (10, (-1, 0, -8927663811)), (15, (-1, 0, -13724860214)), (0, (0, 1, 3236074860))]

def cs_rR : List Cond := [(0, (0, -1, -3236074860))]

def cs_rRL : List Cond := [(15, (1, 0, 13074392905)), (0, (0, -1, -3236074860))]

def cs_rRR : List Cond := [(15, (-1, 0, -13074392905)), (0, (0, -1, -3236074860))]

def cs_rRRL : List Cond := [(0, (0, 1, 3610093563)), (15, (-1, 0, -13074392905)), (0, (0, -1, -3236074860))]

def cs_rRRR : List Cond := [(0, (0, -1, -3610093563)), (15, (-1, 0, -13074392905)), (0, (0, -1, -3236074860))]

end SquarePacking.S11Opt.Simplified.ReducedConditional.U2R.C1465
