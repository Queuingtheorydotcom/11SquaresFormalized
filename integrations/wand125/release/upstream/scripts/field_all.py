"""All baseline field certificates: box trees and Lean (generic assembly `field_generic`).

  python3 field_all.py search  IDX...   # cover trees per positive cell   -> cache/cov-IDX-K.pkl
  python3 field_all.py own              # ownership trees of all used owned points -> cache/own-*.pkl
  python3 field_all.py emit OUTDIR IDX...   # Lean: Shared/, Own/, F<IDX>/

Shared across certificates: the grid (Q, M, R, s), the Voronoi half-planes of the 16 cells, the
ownership trees (keyed by owner and point).  Per certificate: atoms, options, cover trees, Final.
"""
import os
import pickle
import sys
import math
import time
from fractions import Fraction as F
from itertools import combinations
from multiprocessing import Pool

import author
import field_tree as FT
from field_gen import bary_lattice, load_cert

HERE = os.path.dirname(os.path.abspath(__file__))
CACHE = os.environ.get('N11_CACHE', os.path.join(HERE, '../../cache'))
PROCS = int(os.environ.get('N11_PROCS', '2'))
MULT = 192          # divisible by the barycentric denominators 6 (lattice) and 64 (refinement)
FINE = 64
BASE = 4096
FUEL = 200
CHUNK = 1500


def cover_centres():
    cover = author.read_json('research/phase3/current/research/optimality/global_capture/center-cover-symmetric-exact.json')
    return [tuple(map(F, c['center'])) for c in cover['cells']]


def cert_data(idx):
    """Atoms: list of (weight, groups, info); info = ('pt', p) or ('maj', k, sites, subs, barys)."""
    pk, _ = load_cert(idx)
    cert = pk['certificate']
    D = cert['coordinate_denominator']
    sites = [FT.to_grid((F(x, D), F(y, D)), MULT) for x, y in cert['sites']]
    atoms = []
    for j, w in enumerate(cert['point_weights']):
        if w:
            atoms.append((w, [[sites[j]]], ('pt', sites[j])))
    for f in cert['features']:
        assert f['kind'] == 'majority_hull'
        if not f['weight']:
            continue
        pts = [sites[j] for j in f['indices']]
        k = f['threshold']
        assert len(pts) == 2 * k - 1
        subs = list(combinations(range(len(pts)), k))
        lat = [bary_lattice([pts[j] for j in I], 6) for I in subs]
        groups = [[p for p, _ in g] for g in lat]
        atoms.append((f['weight'], groups, ('maj', k, pts, subs, lat)))
    assert sum(a[0] for a in atoms) == cert['budget_units']
    gamma = pk['threshold_units']
    pos = [k for k in pk['mask'] if gamma[k] > 0]
    supp = list(pk.get('conditional_owner_support', pk['mask']))
    owned = {o: [FT.to_grid(tuple(map(F, p))) for p in pk['ownership_points_field'][o]] for o in supp}
    return dict(pk=pk, atoms=atoms, gamma=gamma, pos=pos, supp=supp, owned=owned, mask=pk['mask'])


# ---------------------------------------------------------------- search

def _depth_fn(cx, cy, th):
    c, sn = math.cos(th), math.sin(th)

    def depth(px, py):          # grid units
        dx, dy = px / FT.Q - cx, py / FT.Q - cy
        return 0.5 - max(abs(dx * c + dy * sn), abs(-dx * sn + dy * c))
    return depth


def _cross(a, b, c):
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def refine(P, cx, cy, th):
    """A grid point of conv(P), near the point deepest in the square, with exact integer
    barycentric weights (w * sum = sum l_i P_i)."""
    depth = _depth_fn(cx, cy, th)
    n = len(P)
    if n == 1:
        return P[0], [1]
    if n == 2:
        (x0, y0), (x1, y1) = P
        dx, dy = x1 - x0, y1 - y0
        G = math.gcd(abs(dx), abs(dy))
        if G == 0:
            return P[0], [1, 0]
        best = max(range(0, 2001), key=lambda i: depth(x0 + dx * i / 2000, y0 + dy * i / 2000))
        lo, hi = max(0, best - 1) / 2000, min(2000, best + 1) / 2000
        for _ in range(60):     # ternary search on the concave depth
            a, b = lo + (hi - lo) / 3, hi - (hi - lo) / 3
            if depth(x0 + dx * a, y0 + dy * a) < depth(x0 + dx * b, y0 + dy * b):
                lo = a
            else:
                hi = b
        j = round((lo + hi) / 2 * G)
        return (x0 + dx // G * j, y0 + dy // G * j), [G - j, j]
    # 2D hull: coarse barycentric search, local refinement, round to the grid, exact barycentrics
    N = 64 if n == 3 else 16
    best = None
    def rec(i, left, lam):
        nonlocal best
        if i == n - 1:
            lam2 = lam + [left]
            px = sum(l * p[0] for l, p in zip(lam2, P)) / N
            py = sum(l * p[1] for l, p in zip(lam2, P)) / N
            v = depth(px, py)
            if best is None or v > best[0]:
                best = (v, [l / N for l in lam2])
            return
        for l in range(left + 1):
            rec(i + 1, left - l, lam + [l])
    rec(0, N, [])
    v0, lam = best
    step = 1 / N
    for _ in range(40):
        improved = False
        for i in range(n):
            for j in range(n):
                if i != j and lam[j] >= step:
                    cand = list(lam); cand[i] += step; cand[j] -= step
                    px = sum(l * p[0] for l, p in zip(cand, P)); py = sum(l * p[1] for l, p in zip(cand, P))
                    v = depth(px, py)
                    if v > v0:
                        v0, lam, improved = v, cand, True
        if not improved:
            step /= 2
    w = (round(sum(l * p[0] for l, p in zip(lam, P))), round(sum(l * p[1] for l, p in zip(lam, P))))
    for i, j, k in combinations(range(n), 3):
        a, b, c = P[i], P[j], P[k]
        det = _cross(a, b, c)
        if det == 0:
            continue
        la, lb, lc = _cross(w, b, c), _cross(a, w, c), _cross(a, b, w)
        if det < 0:
            det, la, lb, lc = -det, -la, -lb, -lc
        if la >= 0 and lb >= 0 and lc >= 0:
            full = [0] * n
            full[i], full[j], full[k] = la, lb, lc
            assert la + lb + lc == det
            assert all(det * w[t] == la * a[t] + lb * b[t] + lc * c[t] for t in (0, 1))
            return w, full
    return None


def make_leaf(idx, k):
    """The leaf test of cell (idx, k) and a fresh tree searcher."""
    d = cert_data(idx)
    C = cover_centres()
    atoms, need = d['atoms'], d['gamma'][k]
    others = [(o, p) for o in d['supp'] if o != k for p in d['owned'][o]]

    extra = {}

    def deepest(P, cx, cy, th):
        """A barycentric-lattice point (denominator FINE) of conv(P) deepest in the square."""
        c, sn = math.cos(th), math.sin(th)

        def depth(lam):
            px = sum(l * p[0] for l, p in zip(lam, P)) / FINE / FT.Q
            py = sum(l * p[1] for l, p in zip(lam, P)) / FINE / FT.Q
            dx, dy = px - cx, py - cy
            return 0.5 - max(abs(dx * c + dy * sn), abs(-dx * sn + dy * c))
        n = len(P)
        step = FINE if n <= 3 else 4
        best = None
        def rec(i, left, lam, st):
            nonlocal best
            if i == n - 1:
                lam2 = lam + [left]
                v = depth(lam2)
                if best is None or v > best[0]:
                    best = (v, lam2)
                return
            for l in range(0, left + 1, st):
                rec(i + 1, left - l, lam + [l], st)
        if n == 1:
            return [FINE]
        rec(0, FINE, [], FINE // step if n > 3 else 1)
        if n > 3:   # local refinement around the coarse optimum
            for _ in range(3):
                v0, lam0 = best
                for i in range(n):
                    for j in range(n):
                        for dlt in (1, 2, 4, 8):
                            if i != j and lam0[j] >= dlt:
                                lam = list(lam0); lam[i] += dlt; lam[j] -= dlt
                                v = depth(lam)
                                if v > best[0]:
                                    best = (v, lam)
        return best[1]

    def witness(ai, gi, g, tr, xl, xh, yl, yh):
        for (X, Y), lam in g:
            if FT.pt_ok(tr, xl, xh, yl, yh, X, Y):
                return (X, Y), lam
        for (X, Y), lam in extra.get((ai, gi), []):
            if FT.pt_ok(tr, xl, xh, yl, yh, X, Y):
                return (X, Y), lam
        info = atoms[ai][2]
        P = [info[2][j] for j in info[3][gi]]
        u = (Tref[0].cur_u[0] + Tref[0].cur_u[1]) / 2 / FT.R
        r = refine(P, (xl + xh) / 2 / FT.Q, (yl + yh) / 2 / FT.Q, 2 * math.atan(u))
        if r is None:
            return None
        w, lam = r
        if FT.pt_ok(tr, xl, xh, yl, yh, *w):
            extra.setdefault((ai, gi), []).append((w, tuple(lam)))
            return w, tuple(lam)
        return None

    Tref = [None]

    def leaf(tr, xl, xh, yl, yh):
        tot, sel = 0, []
        for ai, (w, groups, info) in enumerate(atoms):
            picks = []
            if info[0] == 'pt':
                if FT.pt_ok(tr, xl, xh, yl, yh, *info[1]):
                    picks = [(info[1], None)]
                else:
                    continue
            else:
                for gi, g in enumerate(info[4]):
                    r = witness(ai, gi, g, tr, xl, xh, yl, yh)
                    if r is None:
                        break
                    picks.append(r)
                else:
                    pass
                if len(picks) < len(info[4]):
                    continue
            tot += w
            sel.append((ai, tuple(picks)))
            if tot >= need:
                return 'atoms', tuple(sel)
        for o, p in others:
            if FT.pt_ok(tr, xl, xh, yl, yh, *p):
                return 'own', (o, p)
        return None

    T = FT.Tree(leaf, FT.cell_halfplanes(C, k), maxdepth=64)
    Tref[0] = T
    return leaf, T


def search_cell(args):
    idx, k = args
    out = f"{CACHE}/cov-{idx:02d}-{k}.pkl"
    if os.path.exists(out):
        return idx, k, 'cached'
    leaf, T = make_leaf(idx, k)
    t0 = time.time()
    t = T.go(0, FT.M, 0, FT.M, 0, FT.R)
    if not t or T.fail:
        open(f"{CACHE}/fail-{idx:02d}-{k}.txt", 'w').write(repr(T.fail) + "\n")
        return idx, k, 'FAIL', T.fail
    pickle.dump(dict(tree=t, leaves=T.leaves, kinds=T.kinds), open(out, 'wb'))
    return idx, k, T.leaves, T.kinds, round(time.time() - t0, 1)


def split_box(box):
    """The split rule of FT.Tree.go (axis and midpoint), without leaf tests."""
    x0, x1, y0, y1, u0, u1 = box
    wx, wy, wu = (x1 - x0) / FT.Q, (y1 - y0) / FT.Q, (u1 - u0) / FT.R * 2
    if wu >= wx and wu >= wy:
        m = (u0 + u1) // 2
        return 'U', (x0, x1, y0, y1, u0, m), (x0, x1, y0, y1, m, u1)
    if wx >= wy:
        m = (x0 + x1) // 2
        return 'X', (x0, m, y0, y1, u0, u1), (m, x1, y0, y1, u0, u1)
    m = (y0 + y1) // 2
    return 'Y', (x0, x1, y0, m, u0, u1), (x0, x1, m, y1, u0, u1)


def boxes_at(depth):
    out = [((), (0, FT.M, 0, FT.M, 0, FT.R))]
    for _ in range(depth):
        nxt = []
        for path, b in out:
            _, b1, b2 = split_box(b)
            nxt += [(path + (0,), b1), (path + (1,), b2)]
        out = nxt
    return out


def search_part(args):
    """Subtree of cell (idx, k) below the fixed top `depth` levels, at `path`."""
    idx, k, depth, path, box = args
    out = f"{CACHE}/part-{idx:02d}-{k}-{depth}-{''.join(map(str, path))}.pkl"
    if os.path.exists(out):
        return path, 'cached'
    leaf, T = make_leaf(idx, k)
    t = T.go(*box, depth=depth)
    if not t or T.fail:
        return path, 'FAIL', T.fail
    pickle.dump(dict(tree=t, leaves=T.leaves, kinds=T.kinds), open(out, 'wb'))
    return path, T.leaves


def assemble(idx, k, depth):
    parts = {tuple(int(c) for c in f.split('-')[4].split('.')[0]): f
             for f in os.listdir(CACHE) if f.startswith(f"part-{idx:02d}-{k}-{depth}-")}

    def rec(path, box):
        if len(path) == depth:
            return pickle.load(open(f"{CACHE}/{parts[path]}", 'rb'))['tree']
        ax, b1, b2 = split_box(box)
        return (ax, rec(path + (0,), b1), rec(path + (1,), b2))
    t = rec((), (0, FT.M, 0, FT.M, 0, FT.R))
    pickle.dump(dict(tree=t, leaves=None, kinds=None), open(f"{CACHE}/cov-{idx:02d}-{k}.pkl", 'wb'))


def owned_used(tree, acc):
    stack = [tree]
    while stack:
        t = stack.pop()
        if t[0] == 'L':
            if t[1] == 'own':
                acc.add(t[2])
        else:
            stack += [t[1], t[2]]


def own_point(args):
    o, p = args
    out = f"{CACHE}/own-{o}-{p[0]}-{p[1]}.pkl"
    if os.path.exists(out):
        return o, p, 'cached'
    C = cover_centres()
    T = FT.Tree(lambda tr, xl, xh, yl, yh: ('pt', (0, [0])) if FT.pt_ok(tr, xl, xh, yl, yh, *p) else None,
                FT.cell_halfplanes(C, o), maxdepth=64)
    t = T.go(0, FT.M, 0, FT.M, 0, FT.R)
    assert t and not T.fail, (o, p)
    pickle.dump(dict(tree=t, leaves=T.leaves, kinds=T.kinds), open(out, 'wb'))
    return o, p, T.leaves, T.kinds


def all_used_owned(idxs=None):
    """Owned points used by the cover trees (of the given certificates, or of all cached ones)."""
    acc = set()
    for f in sorted(os.listdir(CACHE)):
        if f.startswith('cov-') and (idxs is None or int(f.split('-')[1]) in idxs):
            owned_used(pickle.load(open(f"{CACHE}/{f}", 'rb'))['tree'], acc)
    return sorted(acc)


# ---------------------------------------------------------------- Lean emission

def encode(t, out, optmap):
    if t[0] == 'L':
        kind, pay = t[1], t[2]
        if kind == 'wall':
            out.append(0)
        elif kind == 'cell':
            out += [1, pay]
        elif kind == 'pt':
            out += [2, 0, 1, 0]
        else:
            i, ks = optmap(kind, pay)
            assert len(ks) < BASE and i < BASE and all(x < BASE for x in ks)
            out += [2, i, len(ks)] + list(ks)
        return
    out.append({'X': 3, 'Y': 4, 'U': 5}[t[0]])
    encode(t[1], out, optmap)
    encode(t[2], out, optmap)


def numeral(digits):
    n = 0
    for d in reversed(digits):
        n = n * BASE + d
    return n


_NL = {}


def nleaves(t):
    """Leaf count, memoized by node identity.  The memo keeps the node itself, so that an id
    reused by a later tree after garbage collection is never mistaken for the old node."""
    if t[0] == 'L':
        return 1
    hit = _NL.get(id(t))
    if hit is not None and hit[0] is t:
        return hit[1]
    v = nleaves(t[1]) + nleaves(t[2])
    _NL[id(t)] = (t, v)
    return v


def emit_tree(lines, name, t, box, hp, op, optmap, counter):
    x0, x1, y0, y1, u0, u1 = box
    stmt = f"CovF G.Q G.M G.R {hp} {op} {x0} {x1} {y0} {y1} {u0} {u1}"
    counter[0] += 1
    nm = f"{name}_{counter[0]}"
    if nleaves(t) <= CHUNK:
        digits = []
        encode(t, digits, optmap)
        lines.append(f"theorem {nm} : {stmt} :=\n  soundDec G.Q G.M G.R {BASE} {FUEL} {numeral(digits)} "
                     f"G.Q_pos G.R_pos {hp} {op} (by decide +kernel)\n")
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
    left = emit_tree(lines, name, t[1], b1, hp, op, optmap, counter)
    right = emit_tree(lines, name, t[2], b2, hp, op, optmap, counter)
    lines.append(f"theorem {nm} : {stmt} :=\n  CovF.split{ax} {m} {left} {right}\n")
    return nm


def lpts(g):
    return "[" + ", ".join(f"({x}, {y})" for x, y in g) + "]"


def lq(x):
    x = F(x)
    return f"({x.numerator} / {x.denominator} : ℝ)"


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w') as fh:
        fh.write(text)


def emit_shared(outdir):
    C = cover_centres()
    P = FT.unit_centres(C)
    L = ["import Sqpack.S11Opt.FieldBridge\nimport Sqpack.S11Opt.Cells\n",
         "/-! Generated by `scripts/s11opt/field_all.py`: the grid of the scaled world and the Voronoi",
         "half-planes of the 16 cells, shared by all field certificates. -/\n",
         "namespace SquarePacking.S11Opt.G\n\nopen FieldTree\n",
         f"def Q : ℕ := {FT.Q}\ndef M : ℕ := {FT.M}\ndef R : ℕ := {FT.R}\n",
         f"noncomputable def sc : ℝ := 1 - 1 / {FT.SDEN}\n",
         "lemma Q_pos : 0 < Q := by norm_num [Q]\nlemma R_pos : 0 < R := by norm_num [R]",
         "lemma sc_pos : 0 < sc := by norm_num [sc]\nlemma sc_lt : sc < 1 := by norm_num [sc]",
         "lemma UM : Ux / sc ≤ (M : ℝ) / Q := by norm_num [Ux, sc, M, Q]\n"]
    for k in range(16):
        hps = FT.cell_halfplanes(C, k)
        L.append(f"def hps{k} : List (ℤ × ℤ × ℤ) := [" + ", ".join(f"({a}, {b}, {c})" for a, b, c in hps) + "]")
    L.append("\nlemma vor_lin {c a b : ℝ × ℝ}\n    (h : (c.1 - a.1) ^ 2 + (c.2 - a.2) ^ 2 ≤ (c.1 - b.1) ^ 2 + (c.2 - b.2) ^ 2) :\n"
             "    2 * (b.1 - a.1) * c.1 + 2 * (b.2 - a.2) * c.2 ≤ b.1 ^ 2 + b.2 ^ 2 - a.1 ^ 2 - a.2 ^ 2 := by\n  nlinarith\n")
    for k in range(16):
        js = [j for j in range(16) if j != k]
        L.append(f"lemma cellHP{k} {{c : ℝ × ℝ}} (hc : InCellU {k} c) : ∀ h ∈ hps{k}, InHP Q h (c.1 / sc, c.2 / sc) := by")
        L.append("  intro h hh")
        L.append(f"  simp only [hps{k}, List.mem_cons, List.not_mem_nil, or_false] at hh")
        L.append("  rcases hh with " + " | ".join(["rfl"] * len(js)))
        for j in js:
            (ax, ay), (bx, by) = P[k], P[j]
            L.append(f"  · have h' : 2 * ({lq(bx)} - {lq(ax)}) * c.1 + 2 * ({lq(by)} - {lq(ay)}) * c.2")
            L.append(f"        ≤ {lq(bx)} ^ 2 + {lq(by)} ^ 2 - {lq(ax)} ^ 2 - {lq(ay)} ^ 2 := vor_lin (hc {j})")
            L.append("    norm_num [InHP, Q, sc]")
            L.append("    linarith")
        L.append("")
    L.append("end SquarePacking.S11Opt.G")
    write(f"{outdir}/Shared/Grid.lean", "\n".join(L) + "\n")


def okey(o, p):
    return f"o{o}_{p[0]}_{p[1]}"


def emit_own(outdir, reg):
    """Ownership trees, one file per point (named by owner and point, so that adding certificates
    never renames a checked file), the registry and the membership lemma."""
    L = ["import Sqpack.S11Opt.Shared.Grid\n", "namespace SquarePacking.S11Opt.Own\n",
         "/-- Registered owned points: owner cell, grid point. -/",
         "def reg : List (ℕ × (ℕ × ℕ)) := [" + ", ".join(f"({o}, ({x}, {y}))" for o, (x, y) in reg) + "]",
         "\nend SquarePacking.S11Opt.Own"]
    write(f"{outdir}/Own/Data.lean", "\n".join(L) + "\n")
    roots = {}
    for o, p in reg:
        key = okey(o, p)
        path = f"{outdir}/Own/{key}.lean"
        t = pickle.load(open(f"{CACHE}/own-{o}-{p[0]}-{p[1]}.pkl", 'rb'))['tree']
        lines = []
        rn = emit_tree(lines, f"t_{key}", t, (0, FT.M, 0, FT.M, 0, FT.R), f"G.hps{o}", f"opt_{key}", None, [0])
        roots[key] = rn
        if not os.path.exists(path):
            write(path, "import Sqpack.S11Opt.Shared.Grid\n\nnamespace SquarePacking.S11Opt.Own\n\nopen FieldTree\n\n"
                  f"def opt_{key} : List (List (List (ℕ × ℕ))) := [[[({p[0]}, {p[1]})]]]\n\n"
                  + "\n".join(lines) + "\nend SquarePacking.S11Opt.Own\n")
    M = [f"import Sqpack.S11Opt.Own.{okey(o, p)}" for o, p in reg]
    M += ["import Sqpack.S11Opt.Own.Data", "import Sqpack.S11Opt.FieldBridge\n", "namespace SquarePacking.S11Opt.Own\n\nopen FieldTree\n"]
    for o, p in reg:
        key = okey(o, p)
        M.append(f"lemma mem_{key} {{c : ℝ × ℝ}} {{θ : ℝ}} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU {o} c) :")
        M.append(f"    ptQ G.Q ({p[0]}, {p[1]}) ∈ ScSq G.sc c θ := by")
        M.append(f"  obtain ⟨op, hop, hg⟩ := bridge G.Q_pos G.R_pos {roots[key]} G.sc_pos G.sc_lt G.UM hin (G.cellHP{o} hc)")
        M.append(f"  simp only [opt_{key}, List.mem_singleton] at hop")
        M.append("  subst hop")
        M.append("  obtain ⟨p', hp', hm⟩ := hg _ (List.mem_singleton_self _)")
        M.append("  simp only [List.mem_singleton] at hp'")
        M.append("  subst hp'")
        M.append("  exact hm\n")
    M.append("theorem reg_mem : ∀ e ∈ reg, ∀ {c : ℝ × ℝ} {θ : ℝ}, sq c θ 1 ⊆ box Ux → InCellU e.1 c →")
    M.append("    ptQ G.Q e.2 ∈ ScSq G.sc c θ := by")
    M.append("  intro e he")
    M.append("  simp only [reg, List.mem_cons, List.not_mem_nil, or_false] at he")
    M.append("  rcases he with " + " | ".join(["rfl"] * len(reg)))
    for o, p in reg:
        M.append(f"  · exact fun hin hc => mem_{okey(o, p)} hin hc")
    M.append("\nend SquarePacking.S11Opt.Own")
    write(f"{outdir}/Own/Mem.lean", "\n".join(M) + "\n")


FILELIM = 50000


def emit_cov(base, ns, k, t, hp, op, optmap):
    """Cover tree of cell k: subtrees of <= FILELIM leaves in part files CovKPn (checked in
    parallel), glued in CovK."""
    head = f"import Sqpack.S11Opt.{ns}.Data\n\nnamespace SquarePacking.S11Opt.{ns}\n\nopen FieldTree\n\n"
    foot = f"\nend SquarePacking.S11Opt.{ns}\n"
    parts, glue, cnt = [], [], [0]

    def rec(t, box):
        if nleaves(t) <= FILELIM:
            mod = f"Cov{k}P{len(parts)}"
            lines = []
            rn = emit_tree(lines, f"cov{k}p{len(parts)}", t, box, hp, op, optmap, [0])
            write(f"{base}/{mod}.lean", head + "\n".join(lines) + foot)
            parts.append(mod)
            return rn
        x0, x1, y0, y1, u0, u1 = box
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
        left, right = rec(t[1], b1), rec(t[2], b2)
        cnt[0] += 1
        nm = f"cov{k}g{cnt[0]}"
        glue.append(f"theorem {nm} : CovF G.Q G.M G.R {hp} {op} {x0} {x1} {y0} {y1} {u0} {u1} :=\n"
                    f"  CovF.split{ax} {m} {left} {right}\n")
        return nm
    root = rec(t, (0, FT.M, 0, FT.M, 0, FT.R))
    imports = "".join(f"import Sqpack.S11Opt.{ns}.{mod}\n" for mod in parts)
    write(f"{base}/Cov{k}.lean", imports + f"\nnamespace SquarePacking.S11Opt.{ns}\n\nopen FieldTree\n\n"
          + "\n".join(glue) + foot)
    return root


def emit_cert(outdir, idx, reg):
    d = cert_data(idx)
    atoms, pos = d['atoms'], d['pos']
    ns = f"F{idx:02d}"
    base = f"{outdir}/{ns}"
    trees = {k: pickle.load(open(f"{CACHE}/cov-{idx:02d}-{k}.pkl", 'rb'))['tree'] for k in pos}
    # final witness lists: the lattice, then every refinement point found by any cover
    fin = {}
    for ai, (w, groups, info) in enumerate(atoms):
        if info[0] == 'maj':
            fin[ai] = [list(g) for g in info[4]]
    for k in pos:
        stack = [trees[k]]
        while stack:
            x = stack.pop()
            if x[0] == 'L':
                if x[1] == 'atoms':
                    for ai, picks in x[2]:
                        if ai in fin:
                            for gi, (pt, lam) in enumerate(picks):
                                if all(q != pt for q, _ in fin[ai][gi]):
                                    fin[ai][gi].append((pt, lam))
            else:
                stack += [x[1], x[2]]
    groupsOf = {ai: ([[info[1]]] if info[0] == 'pt' else [[q for q, _ in g] for g in fin[ai]])
                for ai, (_, _, info) in enumerate(atoms)}
    L = ["import Sqpack.S11Opt.Shared.Grid\n", f"/-! Generated by `scripts/s11opt/field_all.py`: the author's baseline field",
         f"certificate {idx} (mask {d['pk']['mask_index']}). -/\n", f"namespace SquarePacking.S11Opt.{ns}\n\nopen FieldTree\n"]
    L.append("set_option maxRecDepth 200000\n")
    for ai in range(len(atoms)):
        L.append(f"noncomputable def atom{ai} : List (List (ℕ × ℕ)) := [" +
                 ",\n  ".join(lpts(g) for g in groupsOf[ai]) + "]")
    L.append("/-- Atoms: groups of grid points (a point site is one group of one point). -/")
    L.append("noncomputable def atoms : List (List (List (ℕ × ℕ))) := [" +
             ", ".join(f"atom{ai}" for ai in range(len(atoms))) + "]")
    L.append("def wts : List ℕ := " + str([w for w, _, _ in atoms]))
    L.append("def gam : List ℕ := " + str(d['gamma']))
    L.append("def pos : List ℕ := " + str(pos))
    L.append("def supp : List ℕ := " + str(d['supp']))
    for ai, (w, groups, info) in enumerate(atoms):
        if info[0] == 'maj':
            _, k, pts, subs, _ = info
            L.append(f"def sites{ai} : List (ℕ × ℕ) := {lpts(pts)}")
            L.append(f"def subs{ai} : List (List ℕ) := " + str([list(I) for I in subs]))
            L.append(f"noncomputable def barys{ai} : List (List (List ℕ)) := " + str([[list(l) for _, l in g] for g in fin[ai]]))
    optinfo = {}
    for k in pos:
        t = trees[k]
        sets, used = [], []
        stack = [t]
        while stack:
            x = stack.pop()
            if x[0] == 'L':
                if x[1] == 'atoms':
                    S = tuple(a for a, _ in x[2])
                    if S not in sets:
                        sets.append(S)
                elif x[1] == 'own' and x[2] not in used:
                    used.append(x[2])
            else:
                stack += [x[1], x[2]]
        sets.sort()
        used.sort()
        optinfo[k] = (t, sets, used)
        L.append(f"def optSets{k} : List (List ℕ) := " + str([list(S) for S in sets]))
        L.append(f"def used{k} : List (ℕ × (ℕ × ℕ)) := [" + ", ".join(f"({o}, ({x}, {y}))" for o, (x, y) in used) + "]")
        L.append(f"noncomputable def opts{k} : List (List (List (ℕ × ℕ))) :=\n  optSets{k}.map (fun S => S.flatMap (fun a => atoms.getD a [])) ++ used{k}.map (fun e => [[e.2]])")
    L.append("def optSets : ℕ → List (List ℕ)\n" + "".join(f"  | {k} => optSets{k}\n" for k in pos) + "  | _ => []")
    L.append("def used : ℕ → List (ℕ × (ℕ × ℕ))\n" + "".join(f"  | {k} => used{k}\n" for k in pos) + "  | _ => []")
    L.append(f"\nend SquarePacking.S11Opt.{ns}")
    write(f"{base}/Data.lean", "\n".join(L) + "\n")
    roots = {}
    for k in pos:
        t, sets, used = optinfo[k]

        def optmap(kind, pay, sets=sets, used=used):
            if kind == 'atoms':
                S = tuple(a for a, _ in pay)
                picks = []
                for ai, ps in pay:
                    for gi, (pt, _) in enumerate(ps):
                        picks.append(groupsOf[ai][gi].index(pt))
                return sets.index(S), picks
            return len(sets) + used.index(pay), [0]
        roots[k] = emit_cov(base, ns, k, t, f"G.hps{k}", f"opts{k}", optmap)
    # Final
    Fl = [f"import Sqpack.S11Opt.{ns}.Cov{k}" for k in pos]
    Fl += ["import Sqpack.S11Opt.Own.Mem", "import Sqpack.S11Opt.FieldGen\n",
           f"namespace SquarePacking.S11Opt.{ns}\n\nopen FieldTree\n"]
    for k in pos:
        Fl.append(f"lemma cover{k} {{c : ℝ × ℝ}} {{θ : ℝ}} (hin : sq c θ 1 ⊆ box Ux) (hc : InCellU {k} c) :")
        Fl.append(f"    (∃ S ∈ optSets{k}, ∀ a ∈ S, AtomSat G.Q (ScSq G.sc c θ) (atoms.getD a [])) ∨")
        Fl.append(f"      ∃ e ∈ used{k}, ptQ G.Q e.2 ∈ ScSq G.sc c θ := by")
        Fl.append(f"  obtain ⟨o, ho, hg⟩ := bridge G.Q_pos G.R_pos {roots[k]} G.sc_pos G.sc_lt G.UM hin (G.cellHP{k} hc)")
        Fl.append(f"  simp only [opts{k}, List.mem_append, List.mem_map] at ho")
        Fl.append("  rcases ho with ⟨S, hS, rfl⟩ | ⟨e, he, rfl⟩")
        Fl.append("  · exact Or.inl ⟨S, hS, fun a ha g hg' => hg g (List.mem_flatMap.mpr ⟨a, ha, hg'⟩)⟩")
        Fl.append("  · obtain ⟨p, hp, hm⟩ := hg _ (List.mem_singleton_self _)")
        Fl.append("    simp only [List.mem_singleton] at hp")
        Fl.append("    subst hp")
        Fl.append("    exact Or.inr ⟨e, he, hm⟩\n")
    posalts = " | ".join(["rfl"] * len(pos))
    Fl.append("lemma hcov : ∀ k ∈ pos, ∀ (c : ℝ × ℝ) (θ : ℝ), sq c θ 1 ⊆ box Ux → InCellU k c →")
    Fl.append("    (∃ S ∈ optSets k, ∀ a ∈ S, AtomSat G.Q (ScSq G.sc c θ) (atoms.getD a [])) ∨")
    Fl.append("      ∃ e ∈ used k, ptQ G.Q e.2 ∈ ScSq G.sc c θ := by")
    Fl.append("  intro k hk c θ hin hc")
    Fl.append("  simp only [pos, List.mem_cons, List.not_mem_nil, or_false] at hk")
    Fl.append(f"  rcases hk with {posalts}")
    for k in pos:
        Fl.append(f"  · exact cover{k} hin hc")
    Fl.append("")
    Fl.append("lemma used_reg : ∀ k ∈ pos, ∀ e ∈ used k, e ∈ Own.reg := by decide +kernel\n")
    Fl.append("lemma hused : ∀ k ∈ pos, ∀ e ∈ used k, e.1 ∈ supp ∧ e.1 ≠ k := by decide +kernel\n")
    Fl.append("lemma hopt : ∀ k ∈ pos, ∀ S ∈ optSets k, S.Nodup ∧ (∀ a ∈ S, a < atoms.length) ∧\n"
              "    gam.getD k 0 ≤ (S.map (wts.getD · 0)).sum := by decide +kernel\n")
    # capacity per atom
    for ai, (w, groups, info) in enumerate(atoms):
        Fl.append(f"lemma cap{ai} {{A B : Set (ℝ × ℝ)}} (hAc : Convex ℝ A) (hAo : IsOpen A) (hBc : Convex ℝ B)")
        Fl.append(f"    (hBo : IsOpen B) (hAB : Disjoint A B) (hA : AtomSat G.Q A (atoms.getD {ai} []))")
        Fl.append(f"    (hB : AtomSat G.Q B (atoms.getD {ai} [])) : False := by")
        if info[0] == 'pt':
            p = info[1]
            Fl.append(f"  exact pt_capacity (Q := G.Q) (p := ({p[0]}, {p[1]})) hAB hA hB\n")
        else:
            Fl.append(f"  have hb := baryAll_spec (sites := sites{ai}) (subs := subs{ai})")
            Fl.append(f"    (groups := atoms.getD {ai} []) (barys := barys{ai}) (by decide +kernel)")
            Fl.append(f"  exact maj_capacity (Q := G.Q) (k := {info[1]}) (sites := sites{ai}) (subs := subs{ai})")
            Fl.append("    (by decide +kernel) (by decide +kernel)")
            Fl.append("    hb.1 hb.2 hAc hAo hBc hBo hAB hA hB\n")
    Fl.append("lemma hcap : ∀ a < atoms.length, ∀ {A B : Set (ℝ × ℝ)}, Convex ℝ A → IsOpen A → Convex ℝ B →")
    Fl.append("    IsOpen B → Disjoint A B → AtomSat G.Q A (atoms.getD a []) → AtomSat G.Q B (atoms.getD a []) →")
    Fl.append("      False := by")
    Fl.append("  intro a ha A B hAc hAo hBc hBo hAB hA hB")
    Fl.append("  have ha' : a < " + str(len(atoms)) + " := by simpa [atoms] using ha")
    Fl.append("  interval_cases a")
    for ai in range(len(atoms)):
        Fl.append(f"  · exact cap{ai} hAc hAo hBc hBo hAB hA hB")
    Fl.append("")
    Fl.append(f"/-- **Field certificate {idx}.**  For every list `P` of positive cells whose thresholds exceed")
    Fl.append("the total weight, the case `supp ++ P` is excluded. -/")
    Fl.append("theorem excluded (P : List ℕ) (hP : P.Nodup) (hPsub : ∀ k ∈ P, k ∈ pos)")
    Fl.append("    (hgap : ∑ a ∈ Finset.range atoms.length, wts.getD a 0 < (P.map (gam.getD · 0)).sum) :")
    Fl.append("    CaseExcluded (supp ++ P) :=")
    Fl.append("  field_generic atoms wts pos supp (gam.getD · 0) optSets used hcov")
    Fl.append("    (fun k hk e he _ _ hin hc => Own.reg_mem e (used_reg k hk e he) hin hc) hused hcap hopt P hP hPsub hgap\n")
    Fl.append("lemma pos_nodup : pos.Nodup := by decide\n")
    Fl.append("/-- The certificate applies to the case `J`: `J` contains the owners, and the positive cells")
    Fl.append("of `J` exceed the total weight. -/")
    Fl.append("noncomputable def applicable (J : List ℕ) : Bool :=")
    Fl.append("  supp.all (· ∈ J) &&")
    Fl.append("    decide ((∑ a ∈ Finset.range atoms.length, wts.getD a 0) <")
    Fl.append("      ((pos.filter (· ∈ J)).map (gam.getD · 0)).sum)\n")
    Fl.append("theorem applicable_sound {J : List ℕ} (h : applicable J = true) : CaseExcluded J := by")
    Fl.append("  simp only [applicable, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h")
    Fl.append("  exact excluded_of_applicable excluded pos_nodup h.1 h.2\n")
    Fl.append(f"end SquarePacking.S11Opt.{ns}")
    write(f"{base}/Final.lean", "\n".join(Fl) + "\n")


def emit_all(outdir, idxs):
    L = [f"import Sqpack.S11Opt.F{i:02d}.Final" for i in idxs] + ["import Sqpack.S11Opt.F00.Final\n"]
    L += ["/-! Generated by `scripts/s11opt/field_all.py`: the baseline field certificates together. -/\n",
          "namespace SquarePacking.S11Opt.FieldAll\n"]
    L.append("/-- field-00 (proved separately in `F00`) applies to `J` when `J` contains its owners. -/")
    L.append("def app00 (J : List ℕ) : Bool := F00.supp.all (· ∈ J)\n")
    L.append("theorem app00_sound {J : List ℕ} (h : app00 J = true) : CaseExcluded J := by")
    L.append("  simp only [app00, List.all_eq_true, decide_eq_true_eq] at h")
    L.append("  exact fun hR => F00.caseExcluded_supp (hR.mono h)\n")
    L.append("/-- Some baseline field certificate applies to `J`. -/")
    L.append("noncomputable def app (J : List ℕ) : Bool :=\n  app00 J" + "".join(f" ||\n  F{i:02d}.applicable J" for i in idxs))
    L.append("\ntheorem app_sound {J : List ℕ} (h : app J = true) : CaseExcluded J := by")
    L.append("  simp only [app, Bool.or_eq_true] at h")
    L.append("  rcases h with " + " | ".join(["h"] * (len(idxs) + 1)).replace("h | h", "h | h", 1))
    L[-1] = "  rcases h with " + "(" * len(idxs) + "h" + "".join(" | h)" for _ in idxs)
    L.append("  · exact app00_sound h")
    for i in idxs:
        L.append(f"  · exact F{i:02d}.applicable_sound h")
    L.append("")
    L.append("/-- The canonical cases excluded by the baseline field certificates (directly or through the")
    L.append("half-turn). -/")
    L.append("noncomputable def excludedField : List (List ℕ) := canonicalMasks.filter fun J => app J || app (hmask J)\n")
    L.append("/-- They are `1904`, as in the author's baseline. -/")
    L.append("lemma excludedField_length : excludedField.length = 1904 := by decide +kernel\n")
    L.append("/-- **The 59 baseline field certificates exclude 1904 of the 2184 canonical cases.** -/")
    L.append("theorem excludedField_all : ∀ J ∈ excludedField, CaseExcluded J := by")
    L.append("  intro J hJ")
    L.append("  simp only [excludedField, List.mem_filter, Bool.or_eq_true] at hJ")
    L.append("  obtain ⟨hJc, h | h⟩ := hJ")
    L.append("  · exact app_sound h")
    L.append("  · exact fun hR => app_sound h (hR.hmask (canonicalMasks_lt J hJc))")
    L.append("\nend SquarePacking.S11Opt.FieldAll")
    write(f"{outdir}/FieldAll.lean", "\n".join(L) + "\n")


def main():
    cmd = sys.argv[1]
    os.makedirs(CACHE, exist_ok=True)
    if cmd == 'search':
        idxs = [int(x) for x in sys.argv[2:]]
        jobs = [(i, k) for i in idxs for k in cert_data(i)['pos']]
        with Pool(PROCS) as pool:
            for r in pool.imap_unordered(search_cell, jobs):
                print(*r, flush=True)
    elif cmd == 'emitcert':         # one certificate only (shared files and ownership already emitted)
        outdir, i = sys.argv[2], int(sys.argv[3])
        emit_cert(outdir, i, None)
        print('emitted', i, flush=True)
    elif cmd == 'psearch':
        idx, k, depth = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        jobs = [(idx, k, depth, path, b) for path, b in boxes_at(depth)]
        with Pool(PROCS) as pool:
            for r in pool.imap_unordered(search_part, jobs):
                print(*r, flush=True)
        assemble(idx, k, depth)
        print('assembled', idx, k, flush=True)
    elif cmd == 'own':
        pts = all_used_owned()
        print(len(pts), 'owned points', flush=True)
        with Pool(PROCS) as pool:
            for r in pool.imap_unordered(own_point, pts):
                print(*r, flush=True)
    elif cmd == 'emit':
        outdir = sys.argv[2]
        idxs = [int(x) for x in sys.argv[3:]]
        reg = all_used_owned()
        emit_shared(outdir)
        emit_own(outdir, reg)
        ready = [i for i in idxs if all(os.path.exists(f"{CACHE}/cov-{i:02d}-{k}.pkl") for k in cert_data(i)['pos'])]
        print('emitting', len(ready), 'certificates; not ready:', sorted(set(idxs) - set(ready)), flush=True)
        for i in ready:
            emit_cert(outdir, i, reg)
        if os.environ.get('N11_EMIT_ALL'):
            emit_all(outdir, idxs)


if __name__ == '__main__':
    main()
