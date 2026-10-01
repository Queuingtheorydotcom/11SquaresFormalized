"""General field-certificate box trees (all 59 baseline field certificates).

Atoms: weighted point sites (captured when the site lies in the open square) and weighted
majority features (TRUE: a witness of every k-subset hull lies in the open square).  Each atom is
captured by at most one square of a packing (open squares are disjoint; capacity one).  A square
with centre in a positive cell i must capture atoms of total weight >= gamma_i, or contain a point
owned by another square.  With sum of gamma over the positive cells > total weight: contradiction.

Usage: python3 field_gen.py survey [idx ...]    (tree sizes only)
"""
import sys
import time
from fractions import Fraction as F
from itertools import combinations
from multiprocessing import Pool

import author
import field_tree as FT

MULT = 12          # site grid coordinates are multiples of MULT (exact barycentric lattices)


def bary_lattice(S, m):
    """Grid points in conv(S) with integer barycentric weights summing to m."""
    k = len(S)
    out = {}

    def rec(i, left, lam):
        if i == k - 1:
            lam = lam + [left]
            x = sum(l * p[0] for l, p in zip(lam, S))
            y = sum(l * p[1] for l, p in zip(lam, S))
            if x % m == 0 and y % m == 0:
                out.setdefault((x // m, y // m), tuple(lam))
            return
        for l in range(left + 1):
            rec(i + 1, left - l, lam + [l])
    rec(0, m, [])
    return sorted(out.items())


def load_cert(idx):
    M = author.read_json('research/phase3/PHASE3_REPLAY_MANIFEST.json')
    r = M['field_recipes'][idx]
    pk = author.read_json('research/phase3/' + r['packet'])
    cover = author.read_json('research/phase3/current/research/optimality/global_capture/center-cover-symmetric-exact.json')
    return pk, cover


def build_atoms(pk):
    cert = pk['certificate']
    D = cert['coordinate_denominator']
    sites = [FT.to_grid((F(x, D), F(y, D)), MULT) for x, y in cert['sites']]
    atoms = []                     # (weight, kind, data)
    for j, w in enumerate(cert['point_weights']):
        if w:
            atoms.append((w, 'pt', sites[j]))
    for f in cert['features']:
        assert f['kind'] == 'majority_hull'
        if not f['weight']:
            continue
        pts = [sites[j] for j in f['indices']]
        k = f['threshold']
        assert len(pts) == 2 * k - 1
        m = {2: 6, 3: 6, 4: 6}.get(k, 6) if k > 1 else 1
        groups = []
        for I in combinations(range(len(pts)), k):
            groups.append(bary_lattice([pts[j] for j in I], m) if k > 1 else [(pts[I[0]], (1,))])
        atoms.append((f['weight'], 'maj', (k, pts, groups)))
    budget = sum(a[0] for a in atoms)
    assert budget == cert['budget_units'], (budget, cert['budget_units'])
    return atoms


def survey_cell(args):
    idx, k = args
    pk, cover = load_cert(idx)
    C = [tuple(map(F, c['center'])) for c in cover['cells']]
    atoms = build_atoms(pk)
    gamma = pk['threshold_units']
    support = pk.get('conditional_owner_support', pk['mask'])
    owned = {o: [FT.to_grid(tuple(map(F, p))) for p in pk['ownership_points_field'][o]] for o in support}
    others = [(o, p) for o in support if o != k for p in owned[o]]
    need = gamma[k]
    used = set()

    def leaf(tr, xl, xh, yl, yh):
        tot = 0
        sat = []
        for ai, (w, kind, data) in enumerate(atoms):
            if kind == 'pt':
                ok = FT.pt_ok(tr, xl, xh, yl, yh, *data)
            else:
                ok = all(any(FT.pt_ok(tr, xl, xh, yl, yh, X, Y) for (X, Y), _ in g) for g in data[2])
            if ok:
                tot += w
                sat.append(ai)
                if tot >= need:
                    return 'atoms', sat
        for o, p in others:
            if FT.pt_ok(tr, xl, xh, yl, yh, *p):
                used.add((o, p))
                return 'own', (o, p)
        return None
    T = FT.Tree(leaf, FT.cell_halfplanes(C, k), maxdepth=64)
    t0 = time.time()
    T.go(0, FT.M, 0, FT.M, 0, FT.R)
    return idx, k, T.leaves, T.kinds, T.fail is not None, len(used), round(time.time() - t0, 1)


def main():
    if sys.argv[1] == 'survey':
        idxs = [int(x) for x in sys.argv[2:]] or list(range(59))
        jobs = []
        for idx in idxs:
            pk, _ = load_cert(idx)
            g = pk['threshold_units']
            jobs += [(idx, k) for k in pk['mask'] if g[k] > 0]
        with Pool(int(__import__('os').environ.get('N11_PROCS', '4'))) as pool:
            for res in pool.imap_unordered(survey_cell, jobs):
                print(*res, flush=True)


if __name__ == '__main__':
    main()
