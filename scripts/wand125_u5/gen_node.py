"""Emit Lean certificates for one step of an archived capture node (untrusted).

    python3 gen_node.py <node.json> <parent.json> <step index> <out.lean> [module name]

The state before the step is replayed from the parent's final state and the
node's earlier complete steps.  Fan's `PoseState` rows are one row per live
archived row: the closed angle interval and the hull of its residual polygons,
with the node's centre constraints prepended (as `clipYUpper`/`clipYLower` do)
and its half-angle constraints applied to the interval (`clipAngle*`).
"""
import json, sys, os
from fractions import Fraction as F
from geom import hull, halfplanes, contains, vertices, implies_mu, empty_mu, round_in, round_out, round_core, mink_ok, mink_labels
from gen_step import (OWNER, cs, envelope, supportB, coreVB, wallB, wall_halves, Region,
                      minkowski_regions, centroid, q, qp, half, lst)


def canon(x):
    return json.dumps(x, sort_keys=True)


def comment_label(value):
    """Keep archive text on one line inside a Lean block comment."""
    if type(value) is not str:
        raise ValueError('node_id must be a string')
    return json.dumps(value, ensure_ascii=True).replace('/-', '/ -').replace('-/', '- /')


class Node:
    def __init__(self, node, parent):
        self.node, self.B = node, F(node['B'])
        self.cells = {int(c): [r for r in rows if r['residual_polygons']]
                      for c, rows in parent['final_state']['cells'].items()}
        self.cons = node['constraints']

    def phys(self, p):
        return (F(p[0]) / self.B, F(p[1]) / self.B)

    def replay(self, k):
        cells = {c: list(rs) for c, rs in self.cells.items()}
        for st in self.node['steps'][:k]:
            if st['complete']:
                cells[st['owner']] = [r for r in st['rows'] if r['residual_polygons']]
        return cells

    def cut_halves(self, cell):
        out = []
        for c in self.cons:
            if c['owner'] == cell and c.get('kind') != 'half_angle':
                n = tuple(map(F, c['normal']))
                out.append((n[0], n[1], F(c['upper_field']) / self.B))
        return out

    def angle_range(self, cell):
        lo, hi = F(0), F(1)
        for c in self.cons:
            if c.get('kind') == 'half_angle' and c['owner'] == cell:
                t = F(c['bound_half_angle'])
                if c['keep'] == 'le':
                    hi = min(hi, t)
                else:
                    lo = max(lo, t)
        return lo, hi

    def fan_row(self, cell, r):
        lo, hi = map(F, r['interval'])
        alo, ahi = self.angle_range(cell)
        lo, hi = max(lo, alo), min(hi, ahi)
        H = hull([self.phys(p) for poly in r['residual_polygons'] for p in poly])
        return (lo, hi, self.cut_halves(cell) + halfplanes(H))


def self_cuts(own, a, b):
    (c, s), M = envelope(a, b)
    cuts = []
    for n in ((c, s), (-s, c)):
        assert supportB(n[0], n[1], M, a, b)
        vmin = min(own, key=lambda v: n[0] * v[0] + n[1] * v[1])
        vmax = max(own, key=lambda v: n[0] * v[0] + n[1] * v[1])
        cuts.append((n, M, False, vmin, n[0] * vmin[0] + n[1] * vmin[1] + M / 2))
        cuts.append((n, M, True, vmax, -(n[0] * vmax[0] + n[1] * vmax[1]) + M / 2))
    return cuts


def cut_hs(cuts):
    return [((-1 if neg else 1) * n[0], (-1 if neg else 1) * n[1], u) for n, M, neg, v, u in cuts]


class Keep:
    def __init__(self, m, piece_hs):
        self.m, self.hs = m, piece_hs


class Coll:
    def __init__(self, k, verts):
        self.k, self.hs = k, halfplanes(verts)


def build(hs, regions, rows_hs, stats, depth=0):
    V = vertices(hs)
    if not V:
        mu = empty_mu(hs)
        assert mu is not None
        stats['empty'] += 1
        return ('empty', mu)
    for R in regions:
        if all(contains(h, p) for h in R.hs for p in V):
            if isinstance(R, Region):
                mus = [implies_mu(hs, (-a, -b, c), V) for (a, b, c) in R.lam]
                assert all(m is not None for m in mus)
                stats['forbid'] += 1
                return ('forbid', R, mus)
            if isinstance(R, Keep):
                mus = [implies_mu(hs, g, V) for g in rows_hs[R.m]]
                assert all(m is not None for m in mus)
                stats['keep'] += 1
                return ('keep', R.m, mus)
            mus = [implies_mu(hs, g, V) for g in R.hs]
            assert all(m is not None for m in mus)
            stats['collide'] += 1
            return ('collide', R.k, mus)
    assert depth < 80, 'cover tree too deep'
    c = centroid(V)
    cand = [R for R in regions if all(contains(h, c) for h in R.hs)]
    assert cand, 'centroid not covered'
    R = cand[0]
    for e in R.hs:
        if any(not contains(e, p) for p in V):
            stats['split'] += 1
            ne = (-e[0], -e[1], -e[2])
            return ('split', e, build([e] + hs, regions, rows_hs, stats, depth + 1),
                    build([ne] + hs, regions, rows_hs, stats, depth + 1))
    raise AssertionError('unreachable')


def tree_lean(t):
    if t[0] == 'empty':
        return f"(.empty {lst(q(m) for m in t[1])})"
    if t[0] == 'forbid':
        R, mus = t[1], t[2]
        lam = lst(f"({q(a)}, {q(b)}, {q(c)})" for a, b, c in R.lam)
        return (f"(.forbid {R.owner} ⟨{lst(qp(k) for k in R.ks)}, {lst(qp(v) for v in R.vs)}, {lam}, "
                f"{lst(lst(q(m) for m in mu) for mu in mus)}⟩)")
    if t[0] == 'keep':
        return f"(.keep {t[1]} {lst(lst(q(m) for m in mu) for mu in t[2])})"
    if t[0] == 'collide':
        return f"(.collide {t[1]} {lst(lst(q(m) for m in mu) for mu in t[2])})"
    return f"(.split {half(t[1])}\n    {tree_lean(t[2])}\n    {tree_lean(t[3])})"


GRID = 10 ** 20


def zp(p):
    x, y = p[0] * GRID, p[1] * GRID
    assert x.denominator == 1 and y.denominator == 1, 'off-grid point'
    return f"({x.numerator}, {y.numerator})"


def regs_lean(regs):
    out = []
    for j, vs, ms in regs:
        labs = lst(lst(f"({a}, {b})" for a, b in L) for L in ms)
        out.append(f"⟨{j}, {lst(zp(v) for v in vs)}, {labs}⟩")
    return lst(out)


def cuts_lean(cuts):
    return lst(f"⟨{q(nv[0])}, {q(nv[1])}, {q(M)}, {'true' if neg else 'false'}, {qp(v)}, {q(u)}⟩"
               for nv, M, neg, v, u in cuts)


def main(node_path, parent_path, k, out_path, modname='Gen'):
    node = json.load(open(node_path))
    label = comment_label(node['node_id'])
    parent = json.load(open(parent_path))
    N = Node(node, parent)
    k = int(k)
    step = node['steps'][k]
    cell = step['owner']
    i = OWNER[cell]
    cells = N.replay(k)
    prior = step['prior_owned_hulls']
    prior = json.loads(prior) if isinstance(prior, str) else prior
    owned = {OWNER[int(c)]: hull([N.phys(p) for p in pts]) for c, pts in prior.items()}
    # Fan rows of every owner, and the map from archived references to row indices
    fan_rows, ref_idx = {}, {}
    for c, rs in cells.items():
        o = OWNER[c]
        fan_rows[o] = [N.fan_row(c, r) for r in rs]
        ref_idx[o] = {canon(r['reference']): m for m, r in enumerate(rs)}
    # the new rows of the owner
    new_live = [r for r in step['rows'] if r['residual_polygons']] if step['complete'] else []
    rs_new = [N.fan_row(cell, r) for r in new_live]
    new_idx = {canon(r['reference']): m for m, r in enumerate(new_live)}
    stats = dict(empty=0, forbid=0, keep=0, collide=0, split=0)
    # partner pose covers
    pcov = {}
    for jc, crow in (step.get('prior_partner_pose_covers') or {}).items():
        jc = int(jc)
        j = OWNER[jc]
        by_ref = {}
        for r in crow:
            by_ref.setdefault(canon(r['reference']), []).append(r)
        tab = []
        for m, (lo, hi, R_hs) in enumerate(fan_rows[j]):
            ref = [x for x, mm in ref_idx[j].items() if mm == m][0]
            pieces = []
            for r in sorted(by_ref.get(ref, []), key=lambda r: F(r['interval'][0])):
                a, b = map(F, r['interval'])
                cuts = self_cuts(owned[j], a, b)
                h = min(sum(cs(a)), sum(cs(b))) / 2
                assert wallB(h, a, b)
                poly = R_hs + cut_hs(cuts) + wall_halves(h)
                V = vertices(poly)
                if not V:
                    pieces.append(dict(a=a, b=b, cuts=cuts, h=h, core=[], dverts=[], dmus=[empty_mu(poly)]))
                    continue
                assert len(V) >= 3
                core = round_core([N.phys(v) for v in r['core']], lambda v: coreVB(a, b, v))
                assert all(coreVB(a, b, v) for v in core)
                Dv = round_out(V)
                dmus = [implies_mu(poly, g, V) for g in halfplanes(Dv)]
                assert all(m is not None for m in dmus)
                pieces.append(dict(a=a, b=b, cuts=cuts, h=h, core=core, dverts=Dv, dmus=dmus))
            tab.append(pieces)
        pcov[j] = tab
    # the sub-rows of every old row of the owner
    certs = []
    old_rows = fan_rows[i]
    by_prior = {}
    for r in step['rows']:
        by_prior.setdefault(canon(r['prior_reference']), []).append(r)
    for m, (lo, hi, row_hs) in enumerate(old_rows):
        ref = [x for x, mm in ref_idx[i].items() if mm == m][0]
        subs = []
        for r in sorted(by_prior.get(ref, []), key=lambda r: F(r['interval'][0])):
            a, b = map(F, r['interval'])
            cuts = self_cuts(owned[i], a, b)
            h = min(sum(cs(a)), sum(cs(b))) / 2
            assert wallB(h, a, b)
            core = hull([N.phys(v) for v in r['core_vertices']])
            assert all(coreVB(a, b, v) for v in core)
            ccore = round_core(core, lambda v: coreVB(a, b, v)) if core else []
            assert all(coreVB(a, b, v) for v in ccore)
            regions, regs = [], []
            for j, K in owned.items():
                if j != i and K and core:
                    regions += minkowski_regions(j, K, core)
            for g in r.get('collision_regions') or []:
                verts = round_out([N.phys(p) for p in g['vertices']])
                for ps in (x for row in pcov[OWNER[g['partner']]] for x in row):
                    if ps['dverts']:
                        assert mink_ok(ps['core'], ccore, verts, ps['dverts']), 'collision margin lost'
                jj = OWNER[g['partner']]
                ms = [mink_labels(ps['core'], ccore) if ps['dverts'] else []
                      for row in pcov[jj] for ps in row]
                regs.append((jj, verts, ms))
                regions.append(Coll(len(regs) - 1, verts))
            if r['residual_polygons']:
                mm = new_idx[canon(r['reference'])]
                for piece in r['residual_polygons']:
                    regions.append(Keep(mm, halfplanes(hull([N.phys(p) for p in piece]))))
            poly = row_hs + cut_hs(cuts) + wall_halves(h)
            tree = build(poly, regions, [x[2] for x in rs_new], stats)
            subs.append(dict(a=a, b=b, cuts=cuts, h=h, core=core, ccore=ccore, regs=regs, tree=tree))
        certs.append(subs)
    print(f"step {k} owner {i} (cell {cell}): old rows {len(old_rows)}, new rows {len(rs_new)}, "
          f"partners { {j: len(t) for j, t in pcov.items()} }, leaves {stats}", file=sys.stderr)

    ns = f"ElevenSquare.Tasks.T07.Ext.{modname}"
    L = ["import ElevenSquare.Tasks.T07.Ext.Check", "",
         f"/-! Generated by `scripts/wand125_u5/gen_node.py` from {label}, step {k}.",
         "Do not edit by hand. -/", "", f"namespace {ns}",
         "open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext", "",
         "set_option maxRecDepth 100000", ""]

    def row_lean(r):
        lo, hi, hs = r
        return f"{{ lo := {q(lo)}, hi := {q(hi)}, centers := {lst(half(x) for x in hs)} }}"

    for o in range(11):
        L.append(f"def rows{o} : List PoseRow := {lst(row_lean(r) for r in fan_rows.get(o, []))}\n")
    L.append("def state : PoseState where\n  rows := ![" + ", ".join(f"rows{o}" for o in range(11)) +
             "]\n  owned := ![" + ", ".join(lst(qp(p) for p in owned.get(o, [])) for o in range(11)) + "]\n")
    L.append(f"def newRows : List PoseRow := {lst(row_lean(r) for r in rs_new)}\n")
    for j, tab in pcov.items():
        L.append(f"def pc{j} : List (List PartnerPiece) := " + lst(
            lst(f"⟨{q(ps['a'])}, {q(ps['b'])}, {cuts_lean(ps['cuts'])}, {q(ps['h'])}, "
                f"{lst(zp(v) for v in ps['core'])}, {lst(zp(v) for v in ps['dverts'])}, "
                f"{lst(lst(q(x) for x in mu) for mu in ps['dmus'])}⟩" for ps in pieces)
            for pieces in tab) + "\n")
    body = " else ".join(f"if j = {j} then pc{j}" for j in pcov)
    L.append(f"def pcov (j : ℕ) : List (List PartnerPiece) := {body + ' else []' if pcov else '[]'}\n")
    for m, subs in enumerate(certs):
        L.append(f"def cert{m} : List Sub := " + lst(
            f"⟨{q(u['a'])}, {q(u['b'])}, {cuts_lean(u['cuts'])}, {q(u['h'])}, {lst(qp(v) for v in u['core'])}, "
            f"{lst(zp(v) for v in u['ccore'])}, "
            f"{regs_lean(u['regs'])},\n  {tree_lean(u['tree'])}⟩"
            for u in subs) + "\n")
        L.append(f"theorem cert{m}_ok : rowB state {i} newRows pcov (rows{i}.getD {m} ⟨0, 0, []⟩) cert{m} = true := by\n"
                 f"  decide +kernel\n")
    L.append(f"def certs : List (List Sub) := {lst(f'cert{m}' for m in range(len(certs)))}\n")
    L.append(f"end {ns}\n")
    open(out_path, "w").write("\n".join(L))


if __name__ == "__main__":
    main(*sys.argv[1:])
