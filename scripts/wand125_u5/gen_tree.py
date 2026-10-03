"""Emit the whole archived case-438 capture tree as chained `ExtTrace`s (untrusted).

    python3 gen_tree.py <json dir> <out dir> [node ...]

<json dir> holds the author's files under the names below (read locally, never
committed).  Every node starts from its parent's final state with Fan's cut
functions (or `cutAngleBelow` on the far side of an angular split), exactly as
the composition `ext_near_of_far` consumes them.
"""
import json
import sys, os
from state_io import load_state, save_state
from fractions import Fraction as F
from geom import hull, halfplanes
from gen_step import OWNER, q, qp, half, lst
from gen_node import Node, canon
import gen_chain
from gen_chain import Chain, row_lean, HDR, NS

U = F(387708359002281417731, 10 ** 20)
YCUT = U / 2 + F(5, 4)

# name, json file, parent, cut (kind, owner, value)
TREE = [
    ("Root240", "root240.json", None, None),
    ("Far15", "far15y.json", "Root240", ("yUpper", 1, YCUT)),
    ("R1", "r1.json", "Root240", ("yLower", 1, YCUT)),
    ("R10", "r10.json", "R1", ("angBelow", 10, F(147, 512))),
    ("Far13", "far13.json", "R10", None),
    ("Near13", "near13.json", "R1", ("angLower", 10, F(147, 512))),
    ("R11", "r11.json", "Near13", None),
    ("R110", "r110.json", "R11", ("angBelow", 6, F(183, 512))),
    ("R111", "r111.json", "R11", ("angLower", 6, F(183, 512))),
    ("Near", "near.json", "R111", None),
]

LEAN_CUT = {"yUpper": "cutYUpper", "yLower": "cutYLower", "angBelow": "cutAngleBelow", "angLower": "cutAngleLower"}


def apply_cut(rows, refs, cut):
    kind, o, v = cut
    rs, rf = rows[o], refs[o]
    if kind == "yUpper":
        rows[o] = [(lo, hi, [(F(0), F(1), v)] + hs) for lo, hi, hs in rs]
    elif kind == "yLower":
        rows[o] = [(lo, hi, [(F(0), F(-1), -v)] + hs) for lo, hi, hs in rs]
    elif kind == "angBelow":
        keep = [m for m, r in enumerate(rs) if r[0] < v]
        rows[o] = [(rs[m][0], min(rs[m][1], v), rs[m][2]) for m in keep]
        refs[o] = [rf[m] for m in keep]
    elif kind == "angLower":
        rows[o] = [(max(lo, v), hi, hs) for lo, hi, hs in rs]


def lean_value(v):
    return "physicalYCut" if v == YCUT else q(v)


def root_state(p2, first_step, B):
    rows, refs = {o: [] for o in range(11)}, {o: [] for o in range(11)}
    phys = lambda p: (F(p[0]) / B, F(p[1]) / B)
    for cell in p2['rounds'][-1]['cells']:
        c, o = cell['owner'], OWNER[cell['owner']]
        for idx, r in enumerate(cell['rows']):
            if not r['residual_polygons']:
                continue
            lo, hi = map(F, r['interval'])
            H = hull([phys(p) for poly in r['residual_polygons'] for p in poly])
            rows[o].append((lo, hi, halfplanes(H)))
            refs[o].append(canon({"kind": "phase2", "round": p2['rounds'][-1]['index'], "owner": c, "row": idx}))
    prior = first_step['prior_owned_hulls']
    prior = json.loads(prior) if isinstance(prior, str) else prior
    owned = {o: [] for o in range(11)}
    for c, pts in prior.items():
        owned[OWNER[int(c)]] = hull([phys(p) for p in pts])
    return rows, refs, owned


def main(jdir, out, *only):
    states = {}
    # U5_P2STATE=<p2_state.json from gen_p2.py> starts the root at the phase-2 chain
    p2_state = os.environ.get('U5_P2STATE')
    for name, fn, parent, cut in TREE:
        node = json.load(open(os.path.join(jdir, fn)))
        B = F(node['B'])
        if parent is None:
            rows, refs, owned = root_state(json.load(open(os.path.join(jdir, "p2.json"))), node['steps'][0], B)
            if p2_state:
                prows, prefs, powned = load_state(p2_state)
                assert all(prows[o] == rows[o] for o in range(11)), 'phase-2 rows differ from the root rows'
                assert all(prefs[o] == refs[o] for o in range(11)), 'phase-2 references differ'
                assert all(set(powned[o]) == set(owned[o]) for o in range(11)), 'phase-2 hulls differ'
                owned = powned
        else:
            prows, prefs, powned = states[parent]
            rows = {o: list(v) for o, v in prows.items()}
            refs = {o: list(v) for o, v in prefs.items()}
            owned = {o: list(v) for o, v in powned.items()}
            if cut:
                apply_cut(rows, refs, cut)
        ch = Chain.__new__(Chain)
        ch.node, ch.name, ch.per = node, name, 40
        ch.N = Node(node, {'final_state': {'cells': {}}})
        ch.rows, ch.refs, ch.owned = rows, refs, owned
        emit = (not only) or (name in only)
        if emit:
            d = os.path.join(out, name)
            os.makedirs(d, exist_ok=True)
            if parent is None and p2_state:
                # the root starts where the phase-2 chain ends
                L = ["import ElevenSquare.Tasks.T07.Ext.Gen.P2\n", f"namespace {NS}.{name}", HDR,
                     f"def st0 : PoseState := {NS}.P2.final\n", f"end {NS}.{name}\n"]
                open(os.path.join(d, "Init.lean"), "w").write("\n".join(L))
            elif parent is None:
                ch.emit_init(out)
            else:
                pm = f"ElevenSquare.Tasks.T07.Ext.Gen.{parent}"
                expr = f"{NS}.{parent}.final"
                if cut:
                    kind, o, v = cut
                    expr = f"{LEAN_CUT[kind]} {expr} {o} {lean_value(v)}"
                L = [f"import {pm}\nimport ElevenSquare.Tasks.T07.Ext.Compose\n", f"namespace {NS}.{name}", HDR,
                     f"def st0 : PoseState := {expr}\n", f"end {NS}.{name}\n"]
                open(os.path.join(d, "Init.lean"), "w").write("\n".join(L))
        n = len(node['steps'])
        last = None
        # optional checkpoints: U5_CKPT=<dir> saves the state after every step,
        # U5_FROM=<name>:<k> resumes that node at step k from the saved state
        ckpt = os.environ.get('U5_CKPT')
        start = 0
        frm = os.environ.get('U5_FROM', '')
        if ckpt and frm.startswith(name + ':'):
            start = int(frm.split(':')[1])
            ch.rows, ch.refs, ch.owned = load_state(os.path.join(ckpt, f"{name}_{start - 1}.json"))
        for k in range(start, n):
            if emit:
                last = ch.step(k, out)
            else:
                last = ch.step_quiet(k)
            if ckpt:
                save_state(os.path.join(ckpt, f"{name}_{k}.json"), (ch.rows, ch.refs, ch.owned))
        if emit:
            mod = f"ElevenSquare.Tasks.T07.Ext.Gen.{name}"
            base = f"{NS}.{name}"
            T = [f"import {mod}.S{n - 1}\nimport ElevenSquare.Tasks.T07.CaptureTraceCombinators\n",
                 f"namespace {base}", HDR, f"def final : PoseState := S{n - 1}.next\n",
                 "theorem trace : ExtTrace st0 final := by"]
            expr = f"S{n - 1}.trace"
            for k in range(n - 2, -1, -1):
                expr = f"(ExtTrace.trans S{k}.trace {expr})"
            T.append(f"  exact {expr}\n")
            if node.get('contradiction'):
                i, _ = last
                T.append(f"theorem terminal : Terminal final :=\n"
                         f"  terminal_of_empty_owner _ {i} (by simp [final, S{n - 1}.next, S{n - 1}.mid, replaceRows, S{n - 1}.rs])\n")
            T.append(f"end {base}\n")
            open(os.path.join(out, f"{name}.lean"), "w").write("\n".join(T))
        states[name] = (ch.rows, ch.refs, ch.owned)
        save_state(os.path.join(out, f"{name}_state.json"), states[name])
        print(f"== {name} done", file=sys.stderr)


if __name__ == "__main__":
    main(*sys.argv[1:])
