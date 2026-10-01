"""Emit the archived phase-2 rounds of case 438 as a chain of `ExtStep`s (untrusted).

    python3 gen_p2.py <data dir> <out dir> [rows per file]

<data dir> holds p2.json (the adaptive phase-2 run), seed.json (its owned
seed) and root240.json (for the scale B).  The chain starts at the closed-cell
seed `siteSeedFor roleCell` and ends at the state the capture root starts from.

Round 0 splits the seed row of every owner along the angle intervals of round 1
and promotes the seed's wall points.  Rounds 1..14 replay the archive: every row
is pruned by the forbidden centres of the other owners' hulls, the residual
polygons become the new rows, and the compressed kernel is promoted.  Each round
is emitted as eleven steps, one owner at a time; the owned hulls only grow, so a
later owner's step uses at least the hulls the archive used.

Writes <out dir>/P2/Init.lean, the step files, P2.lean, and p2_state.pkl (the
final rows, references and owned hulls, read by gen_tree.py).
"""
import json, os, pickle, sys
from fractions import Fraction as F
from geom import hull, vertices
from gen_step import OWNER, cs, wall_halves, coreVB
from gen_node import Node, canon, self_cuts, cut_hs
from gen_chain import Chain, HDR, NS

CAP = F(387708359002281417731, 10 ** 20)
SITE = [(F(104991, 1000000), F(265837, 2000000)), (F(186601, 500000), F(45503, 1000000)),
        (F(1267243, 2000000), F(34689, 250000)), (F(1731123, 2000000), F(25701, 250000)),
        (F(206181, 2000000), F(400379, 1000000)), (F(742311, 2000000), F(312933, 1000000)),
        (F(635257, 1000000), F(166409, 400000)), (F(445439, 500000), F(167763, 500000)),
        (F(54561, 500000), F(332237, 500000)), (F(364743, 1000000), F(233591, 400000)),
        (F(1257689, 2000000), F(687067, 1000000)), (F(1793819, 2000000), F(599621, 1000000)),
        (F(268877, 2000000), F(224299, 250000)), (F(732757, 2000000), F(215311, 250000)),
        (F(313399, 500000), F(954497, 1000000)), (F(895009, 1000000), F(1734163, 2000000))]
ROLE_CELL = [3, 15, 8, 0, 4, 1, 2, 11, 9, 10, 13]


def seed_polygon(i):
    """`seedCellPolygon i`, half-plane for half-plane."""
    out = [(F(-1), F(0), F(-1, 2)), (F(1), F(0), CAP - F(1, 2)),
           (F(0), F(-1), F(-1, 2)), (F(0), F(1), CAP - F(1, 2))]
    a = SITE[i]
    for b in SITE:
        out.append((2 * (b[0] - a[0]), 2 * (b[1] - a[1]),
                    (CAP - 1) * (b[0] ** 2 + b[1] ** 2 - a[0] ** 2 - a[1] ** 2) + (b[0] - a[0]) + (b[1] - a[1])))
    return out


def physical_site(i):
    return ((CAP - 1) * SITE[i][0] + F(1, 2), (CAP - 1) * SITE[i][1] + F(1, 2))


def ref(rnd, cell, idx):
    return {"kind": "phase2", "round": rnd, "owner": cell, "row": idx}


def core_field(r, B):
    """The square core of a row (side `core_side` at the reference angle), in field units."""
    t = F(r['reference_half_angle'])
    h = F(r['core_side']) / 2
    u = ((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))
    w = (-u[1], u[0])
    return [(h * (s1 * u[0] + s2 * w[0]), h * (s1 * u[1] + s2 * w[1]))
            for s1, s2 in ((1, 1), (-1, 1), (-1, -1), (1, -1))]


def build_steps(p2, seed, B):
    steps = []
    # round 0: split the seed rows finer than the round-1 intervals until every
    # seed point lies in every square of every piece, then promote the seed points
    pieces = {}
    for cell in p2['rounds'][0]['cells']:
        c = cell['owner']
        own = [physical_site(c)]
        kern = [(F(p[0]) / B, F(p[1]) / B) for p in seed['owned_points'][c]]

        def poly(a, b):
            h = min(sum(cs(a)), sum(cs(b))) / 2
            V = vertices(seed_polygon(c) + cut_hs(self_cuts(own, a, b)) + wall_halves(h))
            assert len(V) >= 3
            return V

        def split(a, b, depth=0):
            V = poly(a, b)
            if all(coreVB(a, b, v) for v in hull([(k[0] - x[0], k[1] - x[1]) for k in kern for x in V])):
                return [(a, b, V)]
            assert depth < 12, f'seed points not owned near {a}..{b} in cell {c}'
            m = (a + b) / 2
            return split(a, m, depth + 1) + split(m, b, depth + 1)

        rows, pcs = [], []
        for idx, r in enumerate(cell['rows']):
            a, b = map(F, r['interval'])
            for j, (a1, b1, V) in enumerate(split(a, b)):
                rf = {"kind": "phase2", "round": 0, "owner": c, "row": idx, "piece": j}
                rows.append(dict(interval=[str(a1), str(b1)], prior_reference={"kind": "seed"}, reference=rf,
                                 core_vertices=core_field(r, B), collision_regions=[],
                                 residual_polygons=[[(x * B, y * B) for x, y in V]]))
                pcs.append((a1, b1, rf))
        pieces[c] = pcs
        pts = seed['owned_points'][c]
        steps.append(dict(owner=c, complete=True, rows=rows, prior_owned_hulls={},
                          prior_partner_pose_covers=None, common_owned_kernel=pts,
                          inner_grid_compression={"vertices": pts}))
        print(f"round 0 cell {c}: {len(cell['rows'])} intervals -> {len(rows)} pieces", file=sys.stderr, flush=True)
    live = pieces
    # rounds 1..14
    for R in p2['rounds']:
        k = R['index']
        nxt = {}
        for cell in R['cells']:
            c = cell['owner']
            rows = []
            for idx, r in enumerate(cell['rows']):
                a, b = map(F, r['interval'])
                if k == 1:
                    # one sub-row for every round-0 piece of the interval
                    for a1, b1, pref in (x for x in live[c] if a <= x[0] and x[1] <= b):
                        rows.append(dict(interval=r['interval'], sub_interval=[str(a1), str(b1)], prior_reference=pref,
                                         reference=ref(k, c, idx), core_vertices=core_field(r, B),
                                         collision_regions=[], residual_polygons=r['residual_polygons']))
                    continue
                pr = [x for x in live[c] if x[0] <= a and b <= x[1]]
                if not pr:
                    continue
                rows.append(dict(interval=r['interval'], prior_reference=pr[0][2], reference=ref(k, c, idx),
                                 core_vertices=core_field(r, B), collision_regions=[],
                                 residual_polygons=r['residual_polygons']))
            # the sub-rows of every live prior row tile its interval
            for lo, hi, pref in live[c]:
                iv = sorted(tuple(map(F, x.get('sub_interval', x['interval']))) for x in rows if x['prior_reference'] == pref)
                assert iv and iv[0][0] == lo and iv[-1][1] == hi and all(iv[m][1] == iv[m + 1][0] for m in range(len(iv) - 1)), \
                    f'round {k} cell {c}: sub-rows do not tile {lo}..{hi}'
            nxt[c] = []
            for x in rows:
                e = (F(x['interval'][0]), F(x['interval'][1]), x['reference'])
                if x['residual_polygons'] and e not in nxt[c]:
                    nxt[c].append(e)
            steps.append(dict(owner=c, complete=True, rows=rows, prior_owned_hulls={},
                              prior_partner_pose_covers=None, common_owned_kernel=cell['common_core_kernel'],
                              inner_grid_compression=cell['inner_grid_compression']))
        live = nxt
    return steps


def main(jdir, out, per=40):
    p2 = json.load(open(os.path.join(jdir, "p2.json")))
    seed = json.load(open(os.path.join(jdir, "seed.json")))
    B = F(json.load(open(os.path.join(jdir, "root240.json")))['B'])
    steps = build_steps(p2, seed, B)
    node = {'B': str(B), 'constraints': [], 'steps': steps}
    name = "P2"
    ch = Chain.__new__(Chain)
    ch.node, ch.name, ch.per = node, name, int(per)
    ch.N = Node(node, {'final_state': {'cells': {}}})
    ch.rows = {o: [(F(0), F(1), seed_polygon(ROLE_CELL[o]))] for o in range(11)}
    ch.refs = {o: [canon({"kind": "seed"})] for o in range(11)}
    ch.owned = {o: [physical_site(ROLE_CELL[o])] for o in range(11)}
    d = os.path.join(out, name)
    os.makedirs(d, exist_ok=True)
    L = ["import ElevenSquare.Tasks.T07.Ext.Promote\nimport ElevenSquare.Tasks.T07.ShortcutSiteCore\n"
         "import ElevenSquare.Tasks.T07.RoleAssignmentFinite\n", f"namespace {NS}.{name}", HDR,
         "def st0 : PoseState := siteSeedFor roleCell\n", f"end {NS}.{name}\n"]
    open(os.path.join(d, "Init.lean"), "w").write("\n".join(L))
    # resume support as in gen_tree.py
    ckpt = os.environ.get('U5_CKPT')
    start = int(os.environ.get('U5_P2_FROM', '0'))
    if ckpt and start:
        with open(os.path.join(ckpt, f"{name}_{start - 1}.pkl"), 'rb') as f:
            ch.rows, ch.refs, ch.owned = pickle.load(f)
    n = len(steps)
    stop = int(os.environ.get('U5_P2_TO', n))
    for k in range(start, stop):
        ch.step(k, out)
        if ckpt:
            with open(os.path.join(ckpt, f"{name}_{k}.pkl"), 'wb') as f:
                pickle.dump((ch.rows, ch.refs, ch.owned), f)
    if stop < n:
        return
    mod = f"ElevenSquare.Tasks.T07.Ext.Gen.{name}"
    base = f"{NS}.{name}"
    T = [f"import {mod}.S{n - 1}\n", f"namespace {base}", HDR, f"def final : PoseState := S{n - 1}.next\n",
         "theorem trace : ExtTrace st0 final := by"]
    expr = f"S{n - 1}.trace"
    for k in range(n - 2, -1, -1):
        expr = f"(ExtTrace.trans S{k}.trace {expr})"
    T.append(f"  exact {expr}\n")
    T.append(f"end {base}\n")
    open(os.path.join(out, f"{name}.lean"), "w").write("\n".join(T))
    with open(os.path.join(out, "p2_state.pkl"), 'wb') as f:
        pickle.dump((ch.rows, ch.refs, ch.owned), f)


if __name__ == "__main__":
    main(*sys.argv[1:])
