"""Certificates that the final near state lies in the frozen near packet (untrusted).

    python3 gen_near.py <repo root> <Near_state.pkl> <out dir>

Reads the near rows and field boxes from the packet's Lean sources, and writes
<out dir>/NearConn.lean: for every owner a list of `NRow` (the index of a near
row whose angle interval contains the state row, and Farkas multipliers for the
four box half-planes) with the theorem `NearRowsSubsumed Near.final`.
"""
import os, pickle, re, sys
from fractions import Fraction as F
from geom import vertices, implies_mu
from gen_step import q, lst
from gen_chain import HDR, NS

SCALE = F(382000000000000000000, 387708359002281417731)
NUM = r"\(Rat\.divInt (-?\d+) (\d+)\)|\((-?\d+) : ℚ\)"


def num(m):
    return F(int(m[0]), int(m[1])) if m[0] else F(int(m[2]))


def packet(root):
    boxes, rows = {}, {}
    for i in range(11):
        src = open(os.path.join(root, f"ElevenSquare/Tasks/T07/NearSourceData{i}.lean")).read()
        b = re.search(rf"def nearBox{i} : NearRatRect := ⟨(.*?)⟩\n", src).group(1)
        boxes[i] = [num(m) for m in re.findall(NUM, b)]
        assert len(boxes[i]) == 4
        defs = {}
        for m in re.finditer(rf"def nearRow{i}_(\d+) : NearPoseRow :=\n  ⟨(.*?), (.*?), \[", src):
            lo = [num(x) for x in re.findall(NUM, m.group(2))]
            hi = [num(x) for x in re.findall(NUM, m.group(3))]
            defs[int(m.group(1))] = (lo[0], hi[0])
        order = re.search(rf"def nearRows{i} : List NearPoseRow :=\n  \[(.*?)\]", src).group(1)
        rows[i] = [defs[int(x)] for x in re.findall(rf"nearRow{i}_(\d+)", order)]
    return boxes, rows


def main(root, state, out):
    boxes, nrows = packet(root)
    with open(state, 'rb') as f:
        srows, _, _ = pickle.load(f)
    L = ["import ElevenSquare.Tasks.T07.Ext.Gen.Near\nimport ElevenSquare.Tasks.T07.Ext.Near\n",
         f"namespace {NS}.NearConn", HDR]
    for i in range(11):
        lx, hx, ly, hy = boxes[i]
        planes = [(-SCALE, F(0), -lx), (SCALE, F(0), hx), (F(0), -SCALE, -ly), (F(0), SCALE, hy)]
        cs = []
        for lo, hi, hs in srows[i]:
            k = next(k for k, (a, b) in enumerate(nrows[i]) if a <= lo and hi <= b)
            V = vertices(hs)
            mus = [implies_mu(hs, g, V) for g in planes]
            assert all(m is not None for m in mus), f'owner {i}: row outside its near box'
            cs.append(f"⟨{k}, {lst(lst(q(x) for x in mu) for mu in mus)}⟩")
        L.append(f"def c{i} : List NRow := {lst(cs)}\n")
        L.append(f"theorem ok{i} : nearRowsB {i} ({NS}.Near.final.rows {i}) c{i} = true := by decide +kernel\n")
    L.append("def cs : Owner → List NRow := ![" + ", ".join(f"c{i}" for i in range(11)) + "]\n")
    L.append("theorem subsumed : NearRowsSubsumed {NS}.Near.final := by\n"
             "  refine nearFiniteRowEnclosure_subsumed _ (nearRowsB_sound (cs := cs) ?_)\n"
             "  intro i\n  fin_cases i\n" + "\n".join(f"  · exact ok{i}" for i in range(11)) + "\n")
    L.append(f"end {NS}.NearConn\n")
    open(os.path.join(out, "NearConn.lean"), "w").write("\n".join(L))


if __name__ == "__main__":
    main(*sys.argv[1:])
