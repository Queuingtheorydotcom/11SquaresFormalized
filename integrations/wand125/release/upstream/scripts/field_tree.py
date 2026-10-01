"""Feasibility prototype: re-prove one field certificate (default field-00) with box trees.

World: unit squares in the container [0, U]^2 (U = the author's rational upper value), scaled by
1/s (s < 1), so that "p/s lies in the closed unit square about c/s" gives "p lies in the OPEN unit
square about c".  All scaled coordinates are integers over Q; the angle parameter u = tan(θ/2)
is over R, u in [0, 1] (a full quarter turn).  The containment test mirrors evand's
`BoxTree.ptOk` (Nat semantics) exactly.

Claims checked here (all on the scaled integer grid):
* cover(k): for every admissible pose whose centre lies in Voronoi cell k (k a positive cell),
  either every majority k-subset hull of some TRUE feature has a witness point in the square, or
  an owned point of another conditional owner lies in the square;
* own(o, p): for every admissible pose with centre in cell o, the owned point p lies in the square.
"""
import json
import os
import sys
import time
from fractions import Fraction as F
from itertools import combinations
from math import ceil, floor, gcd

sys.setrecursionlimit(100000)
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
HERE = __file__.rsplit('/', 1)[0]
DATA = os.environ.get('N11_DATA', HERE + '/../../data')

U = F(387708359002281417731, 10 ** 20)
L = F(191, 50)
B = L / U
KQ, KR = 32, 24
Q = 2 ** KQ
R = 2 ** KR
SDEN = 2 ** 20
s = 1 - F(1, SDEN)
M = ceil(Q * U / s)          # scaled container side over Q (rounded up: admissibility is necessary)
MULT = 6                     # site grid coordinates are multiples of MULT (exact witness lattice)


def nsub(a, b):
    return a - b if a > b else 0


def triples(U0, U1):
    RR = R * R
    return [(2 * nsub(RR, U0 * U0), 4 * R * U0, RR + U0 * U0),
            (2 * nsub(RR, U1 * U1), 4 * R * U1, RR + U1 * U1),
            (2 * nsub(RR, U0 * U1), 2 * R * (U0 + U1), RR + U0 * U1)]


def tri_ok(G, a, b, xl, xh, yl, yh, X, Y):
    aX, bY, bX, aY = a * X, b * Y, b * X, a * Y
    return (aX + bY <= G + a * xl + b * yl and a * xh + b * yh <= G + aX + bY
            and aY + b * xh <= G + bX + a * yl and bX + a * yh <= G + aY + b * xl)


def pt_ok(tr, xl, xh, yl, yh, X, Y):
    return all(tri_ok(g * Q, a, b, xl, xh, yl, yh, X, Y) for a, b, g in tr)


def wlo(U0, U1):
    return (Q * nsub(R * R + 2 * U0 * R, U1 * U1)) // (2 * (R * R + U1 * U1))


def load():
    # the author's files (Queuingtheorydotcom/11SquaresOptimal f9e0de7), by content hash
    cover = json.load(open(DATA + '/cover/center-cover-symmetric-exact.json'))   # sha256 df7938d9…
    pk = json.load(open(DATA + '/field-00/research/phase3/work/continuation/mask2045-omit14-packet.json'))  # 4aca103f…
    return cover, pk


def to_grid(p_field, mult=1):
    """field coordinates -> unit (/B) -> scaled (/s) -> nearest grid point (multiple of mult)."""
    return tuple(int(round(float(x / B / s * Q / mult))) * mult for x in p_field)


def unit_centres(C):
    """Voronoi sites in unit coordinates: P = 1/2 + (U - 1) * c (container [0, U])."""
    return [(F(1, 2) + (U - 1) * c[0], F(1, 2) + (U - 1) * c[1]) for c in C]


def cell_halfplanes(C, k):
    """Cell k: |c - P_k|^2 <= |c - P_j|^2, i.e. 2(P_j - P_k).c <= |P_j|^2 - |P_k|^2, in unit
    coordinates c = s X / Q.  Returned as integers (A, B, Cc): A X + B Y <= Cc, together with the
    positive integer factor `den` (A = den * 2 (P_j - P_k).x * s / Q, ...)."""
    P = unit_centres(C)
    pk = P[k]
    out = []
    for j, pj in enumerate(P):
        if j == k:
            continue
        a, b = 2 * (pj[0] - pk[0]), 2 * (pj[1] - pk[1])
        r = pj[0] ** 2 + pj[1] ** 2 - pk[0] ** 2 - pk[1] ** 2
        ax, ay = a * s / Q, b * s / Q
        den = 1
        for z in (ax, ay, r):
            den = den * z.denominator // gcd(den, z.denominator)
        out.append((int(ax * den), int(ay * den), int(r * den)))
    return out


def outside(hps, xl, xh, yl, yh):
    """Index of an integer half-plane (A, B, C) excluding the rectangle (mirror of `outOk`)."""
    for j, (A, Bc, Cc) in enumerate(hps):
        if Cc < A * (xl if A >= 0 else xh) + Bc * (yl if Bc >= 0 else yh):
            return j
    return None


def in_cell_bbox(hps, verts):
    xs = [(F(1, 2) + (U - 1) * v[0]) / s * Q for v in verts]
    ys = [(F(1, 2) + (U - 1) * v[1]) / s * Q for v in verts]
    return floor(min(xs)) - 1, ceil(max(xs)) + 1, floor(min(ys)) - 1, ceil(max(ys)) + 1


def tri_lattice(a, b, c, m=MULT):
    pts = set()
    for i in range(m + 1):
        for j in range(m + 1 - i):
            l = m - i - j
            x = (i * a[0] + j * b[0] + l * c[0])
            y = (i * a[1] + j * b[1] + l * c[1])
            assert x % m == 0 and y % m == 0
            pts.add((x // m, y // m))
    return sorted(pts)


def seg_lattice(a, b, m=MULT):
    return sorted({((i * a[0] + (m - i) * b[0]) // m, (i * a[1] + (m - i) * b[1]) // m) for i in range(m + 1)})


class Tree:
    def __init__(self, leaf_fn, hps, maxdepth=60):
        self.leaf_fn, self.hps, self.maxdepth = leaf_fn, hps, maxdepth
        self.leaves = 0
        self.kinds = {}
        self.fail = None

    def go(self, x0, x1, y0, y1, u0, u1, depth=0):
        if self.fail:
            return None
        wl = wlo(u0, u1)
        xl, xh, yl, yh = max(x0, wl), min(x1, M - wl), max(y0, wl), min(y1, M - wl)
        kind = None
        kind = payload = None
        if xh < xl or yh < yl:
            kind, payload = 'wall', ()
        else:
            j = outside(self.hps, xl, xh, yl, yh)
            if j is not None:
                kind, payload = 'cell', j
            else:
                self.cur_u = (u0, u1)
                r = self.leaf_fn(triples(u0, u1), xl, xh, yl, yh)
                if r:
                    kind, payload = r
        if kind:
            self.leaves += 1
            self.kinds[kind] = self.kinds.get(kind, 0) + 1
            return ('L', kind, payload)
        if depth >= self.maxdepth:
            self.fail = (x0, x1, y0, y1, u0, u1)
            return None
        # split the relatively widest axis (angle measured against 1 radian ~ R/2)
        wx, wy, wu = (x1 - x0) / Q, (y1 - y0) / Q, (u1 - u0) / R * 2
        if wu >= wx and wu >= wy:
            m = (u0 + u1) // 2
            return ('U', self.go(x0, x1, y0, y1, u0, m, depth + 1), self.go(x0, x1, y0, y1, m, u1, depth + 1))
        if wx >= wy:
            m = (x0 + x1) // 2
            return ('X', self.go(x0, m, y0, y1, u0, u1, depth + 1), self.go(m, x1, y0, y1, u0, u1, depth + 1))
        m = (y0 + y1) // 2
        return ('Y', self.go(x0, x1, y0, m, u0, u1, depth + 1), self.go(x0, x1, m, y1, u0, u1, depth + 1))


BASE = 128
FUEL = 200
CHUNK = 1500


def encode(t, out):
    """Digit stream (mirror of `FieldTree.dec`), least significant first."""
    if t[0] == 'L':
        kind, pay = t[1], t[2]
        if kind == 'wall':
            out.append(0)
        elif kind == 'cell':
            out += [1, pay]
        else:
            i, ks = pay
            out += [2, i, len(ks)] + list(ks)
        return
    out.append({'X': 3, 'Y': 4, 'U': 5}[t[0]])
    encode(t[1], out)
    encode(t[2], out)


def numeral(digits):
    n = 0
    for d in reversed(digits):
        assert 0 <= d < BASE
        n = n * BASE + d
    return n


def nleaves(t):
    return 1 if t[0] == 'L' else nleaves(t[1]) + nleaves(t[2])


class Emitter:
    def __init__(self):
        self.lines = []
        self.count = 0

    def chunks(self, name, t, box, hp, op):
        """Emit theorems proving `CovF … box` for tree `t`; return the theorem name."""
        x0, x1, y0, y1, u0, u1 = box
        stmt = f"CovF Q M R {hp} {op} {x0} {x1} {y0} {y1} {u0} {u1}"
        self.count += 1
        nm = f"{name}_{self.count}"
        if nleaves(t) <= CHUNK:
            digits = []
            encode(t, digits)
            self.lines.append(f"theorem {nm} : {stmt} :=\n  soundDec Q M R {BASE} {FUEL} {numeral(digits)} "
                              f"(by norm_num [Q]) (by norm_num [R]) {hp} {op} (by decide +kernel)\n")
            return nm
        ax = t[0]
        if ax == 'X':
            m = (x0 + x1) // 2
            b1, b2 = (x0, m, y0, y1, u0, u1), (m, x1, y0, y1, u0, u1)
        elif ax == 'Y':
            m = (y0 + y1) // 2
            b1, b2 = (x0, x1, y0, m, u0, u1), (x0, x1, m, y1, u0, u1)
        else:
            m = (u0 + u1) // 2
            b1, b2 = (x0, x1, y0, y1, u0, m), (x0, x1, y0, y1, m, u1)
        l = self.chunks(name, t[1], b1, hp, op)
        r = self.chunks(name, t[2], b2, hp, op)
        self.lines.append(f"theorem {nm} : {stmt} :=\n  CovF.split{ax} {m} {l} {r}\n")
        return nm


def lean_pts(g):
    return "[" + ", ".join(f"({x}, {y})" for x, y in g) + "]"


def lean_q(q):
    q = F(q)
    return f"({q.numerator} / {q.denominator} : ℝ)" if q.denominator != 1 else f"({q.numerator} : ℝ)"


def tri_lattice_bary(S, m=MULT):
    """Witness candidates in conv(S) with their barycentric integer weights (sum m)."""
    n = len(S)
    out = {}
    if n == 3:
        combos = [(i, j, m - i - j) for i in range(m + 1) for j in range(m + 1 - i)]
    else:
        combos = [(i, m - i) for i in range(m + 1)]
    for lam in combos:
        x = sum(l * p[0] for l, p in zip(lam, S))
        y = sum(l * p[1] for l, p in zip(lam, S))
        assert x % m == 0 and y % m == 0
        out.setdefault((x // m, y // m), lam)
    return sorted(out.items())


def main():
    outdir = sys.argv[1]
    cover, pk = load()
    C = [tuple(map(F, c['center'])) for c in cover['cells']]
    cert = pk['certificate']
    D = cert['coordinate_denominator']
    sites = [to_grid((F(x, D), F(y, D)), MULT) for x, y in cert['sites']]
    feats = []      # per feature: (k, local sites, subsets (local index lists), groups [(pt, bary)])
    for f in cert['features']:
        assert f['kind'] == 'majority_hull'
        pts = [sites[j] for j in f['indices']]
        k = f['threshold']
        assert len(pts) == 2 * k - 1
        subs = list(combinations(range(len(pts)), k))
        groups = [tri_lattice_bary([pts[j] for j in I]) for I in subs]
        feats.append((k, pts, subs, groups))
    gamma = pk['threshold_units']
    support = pk['conditional_owner_support']
    owned = {o: [to_grid(tuple(map(F, p))) for p in pk['ownership_points_field'][o]] for o in support}
    positive = [i for i in pk['mask'] if gamma[i] > 0]
    root = (0, M, 0, M, 0, R)
    files = {}
    stats = []
    used_all = []          # (owner, point) with ownership trees, in order
    cellopts = {}
    for k in positive:
        hps = cell_halfplanes(C, k)
        others = [(o, p) for o in support if o != k for p in owned[o]]
        used = []

        def leaf(tr, xl, xh, yl, yh):
            for fi, (_, _, _, groups) in enumerate(feats):
                ks = []
                for g in groups:
                    kk = next((j for j, ((X, Y), _) in enumerate(g) if pt_ok(tr, xl, xh, yl, yh, X, Y)), None)
                    if kk is None:
                        break
                    ks.append(kk)
                else:
                    return 'TRUE%d' % fi, (fi, ks)
            for (o, (X, Y)) in others:
                if pt_ok(tr, xl, xh, yl, yh, X, Y):
                    if (o, (X, Y)) not in used:
                        used.append((o, (X, Y)))
                    return 'own', (len(feats) + used.index((o, (X, Y))), [0])
            return None
        T = Tree(leaf, hps)
        t = T.go(*root)
        assert t and not T.fail, T.fail
        stats.append(f"cover cell {k}: {T.leaves} leaves {T.kinds}, owned points used {len(used)}")
        for op in used:
            if op not in used_all:
                used_all.append(op)
        cellopts[k] = (hps, used)
        E = Emitter()
        E.chunks(f"cov{k}", t, root, f"hps{k}", f"opts{k}")
        files[f"Cov{k}"] = (E.lines, f"cov{k}_1")
    ownhps = {}
    for n, (o, p) in enumerate(used_all):
        hps = cell_halfplanes(C, o)
        ownhps[o] = hps
        T = Tree(lambda tr, xl, xh, yl, yh: ('pt', (0, [0])) if pt_ok(tr, xl, xh, yl, yh, *p) else None, hps)
        t = T.go(*root)
        assert t and not T.fail
        stats.append(f"own{n} (owner {o}) {p}: {T.leaves} leaves {T.kinds}")
        E = Emitter()
        E.chunks(f"own{n}", t, root, f"hps{o}", f"ownOpt{n}")
        files[f"Own{n}"] = (E.lines, f"own{n}_1")
    # ---- data file
    P = unit_centres(C)
    d = []
    d.append("import Sqpack.S11Opt.FieldTree\n")
    d.append("/-! Generated by `scripts/s11opt/field_tree.py` from the author's field-00 packet")
    d.append("(`mask2045-omit14-packet.json`, sha256 4aca103f…) and the centre cover")
    d.append("(`center-cover-symmetric-exact.json`, sha256 df7938d9…).  Scaled world: unit coordinates")
    d.append("divided by `s = 1 - 2⁻²⁰`, integers over `Q`; `u = tan(θ/2)` over `R`. -/\n")
    d.append("namespace SquarePacking.S11Opt.F00\n\nopen FieldTree\n")
    d.append(f"def Q : ℕ := {Q}\ndef M : ℕ := {M}\ndef R : ℕ := {R}\n")
    d.append(f"/-- The scale `s = 1 - 2⁻²⁰`. -/\nnoncomputable def sc : ℝ := 1 - 1 / {SDEN}\n")
    d.append("/-- Voronoi sites of the 16 cells in unit coordinates, `1/2 + (U - 1) c`. -/")
    d.append("noncomputable def PU : Fin 16 → ℝ × ℝ := ![" + ", ".join(f"({lean_q(a)}, {lean_q(b)})" for a, b in P) + "]\n")
    for fi, (k, pts, subs, groups) in enumerate(feats):
        d.append(f"/-- Feature {fi}: {len(pts)} sites, majority threshold {k}. -/")
        d.append(f"def site{fi} : List (ℕ × ℕ) := {lean_pts(pts)}")
        d.append(f"def subs{fi} : List (List ℕ) := [" + ", ".join("[" + ", ".join(map(str, I)) + "]" for I in subs) + "]")
        d.append(f"def grp{fi} : List (List (ℕ × ℕ)) := [" + ", ".join(lean_pts([p for p, _ in g]) for g in groups) + "]")
        d.append(f"def bary{fi} : List (List (List ℕ)) := [" + ", ".join(
            "[" + ", ".join("[" + ", ".join(map(str, lam)) + "]" for _, lam in g) + "]" for g in groups) + "]\n")
    for k, (hps, used) in cellopts.items():
        d.append(f"/-- Cell {k}: its Voronoi bisectors on the grid. -/")
        d.append(f"def hps{k} : List (ℤ × ℤ × ℤ) := [" + ", ".join(f"({a}, {b}, {c})" for a, b, c in hps) + "]")
        d.append(f"/-- Owned points (of other owners) used by the cover of cell {k}: owner, point. -/")
        d.append(f"def used{k} : List (ℕ × (ℕ × ℕ)) := [" + ", ".join(f"({o}, ({x}, {y}))" for o, (x, y) in used) + "]")
        d.append(f"def opts{k} : List (List (List (ℕ × ℕ))) := [grp0, grp1] ++ used{k}.map (fun e => [[e.2]])\n")
    for o, hps in ownhps.items():
        if o not in cellopts:
            d.append(f"def hps{o} : List (ℤ × ℤ × ℤ) := [" + ", ".join(f"({a}, {b}, {c})" for a, b, c in hps) + "]")
    d.append("/-- All owned points with ownership trees: owner, point. -/")
    d.append("def owned : List (ℕ × (ℕ × ℕ)) := [" + ", ".join(f"({o}, ({x}, {y}))" for o, (x, y) in used_all) + "]")
    for n, (o, (x, y)) in enumerate(used_all):
        d.append(f"def ownOpt{n} : List (List (List (ℕ × ℕ))) := [[[({x}, {y})]]]")
    d.append("\nend SquarePacking.S11Opt.F00")
    open(f"{outdir}/Data.lean", "w").write("\n".join(d) + "\n")
    for name, (lines, rootname) in files.items():
        with open(f"{outdir}/{name}.lean", "w") as fh:
            fh.write("import Sqpack.S11Opt.F00.Data\n\nnamespace SquarePacking.S11Opt.F00\n\nopen FieldTree\n\n")
            fh.write("\n".join(lines))
            fh.write("\nend SquarePacking.S11Opt.F00\n")
    with open(f"{outdir}/All.lean", "w") as fh:
        fh.write("import Sqpack.S11Opt.F00.Data\n")
        for name in sorted(files):
            fh.write(f"import Sqpack.S11Opt.F00.{name}\n")
    with open(f"{outdir}/Roots.txt", "w") as fh:
        for name, (lines, rootname) in files.items():
            fh.write(f"{name} {rootname}\n")
    print("\n".join(stats), file=sys.stderr)


if __name__ == '__main__':
    main()
