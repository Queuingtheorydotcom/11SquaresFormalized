"""Generator for U2Prior: exclude a canonical case by the owned-hull induction with box trees.

Owner step (owner o): a FieldTree over the pose space of cell o.  U-splits to `ROWS` angle rows,
then X/Y splits at floor midpoints (as `FieldTree.dec`).  Leaves:
  wall / cell j                        (FieldTree's own leaves)
  dead:  opt i [k]  — the k-th point of triangle option i (a lattice point of a fan triangle of
         another owner's owned hull) lies in every square of the box (`ptOk`);
  alive: opt T [0,...,0] — every target lies in every square of the box.
The targets (new owned hull of o, vertices on multiples of `BM`) are chosen from the intersection
of the ptOk regions (12 half-planes each) of the alive leaves.  A step with no alive leaf is terminal.

Lean: `U2P.owned_all_of_tris` (promotion) and `U2P.excluded_of_tris` (terminal).
"""
import sys, time, math, json, os
from fractions import Fraction as F
from itertools import combinations
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
import grid as FT                # ptOk, wlo, triples, cell half-planes (mirrors Shared/Grid.lean)
Q, R, M = FT.Q, FT.R, FT.M
BM = 65536                       # barycentric denominator (Lean `U2P.bm`)
BASE = 4096                      # digit base of the tree encoding
FUEL = 200
CHUNK = int(os.environ.get('U2P_CHUNK', 1500))   # leaves per Lean theorem (smaller: less kernel memory)
KMAX = int(os.environ.get('U2P_KMAX', 16))   # at most this many targets per step (0: no limit)
# Step parameters; `fine` is for cases the default does not close (env U2P_PROFILE).
PROFILES = {'default': dict(eps_min=0.0025, umin=2 ** 14, max_iter=60),
            'fine': dict(eps_min=0.001, umin=2 ** 12, max_iter=200)}
PROFILE = os.environ.get('U2P_PROFILE', 'default')


HPS = [FT.cell_halfplanes(k) for k in range(16)]
H = lambda J: tuple(sorted(15 - i for i in J))
CAN = sorted({min(J, H(J)) for J in combinations(range(16), 11)})


# ---------------------------------------------------------------- geometry helpers
def region_hps(tr, xl, xh, yl, yh):
    """ptOk region of a box: half-planes (A, B, C) with A X + B Y <= C (exact ints)."""
    out = []
    for a, b, g in tr:
        G = g * Q
        out.append((a, b, G + a * xl + b * yl))
        out.append((-a, -b, G - a * xh - b * yh))
        out.append((-b, a, G + a * yl - b * xh))
        out.append((b, -a, G + b * xl - a * yh))
    return out


def clip(poly, h):
    A, B, Cc = h
    out = []
    n = len(poly)
    for i in range(n):
        p = poly[i]; q = poly[(i + 1) % n]
        fp = A * p[0] + B * p[1] - Cc; fq = A * q[0] + B * q[1] - Cc
        if fp <= 0:
            out.append(p)
        if (fp < 0 < fq) or (fq < 0 < fp):
            t = fp / (fp - fq)
            out.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
    return out


def hull(pts):
    pts = sorted(set(pts))
    if len(pts) < 3:
        return pts
    def cr(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    lo, hi = [], []
    for p in pts:
        while len(lo) >= 2 and cr(lo[-2], lo[-1], p) <= 0:
            lo.pop()
        lo.append(p)
    for p in reversed(pts):
        while len(hi) >= 2 and cr(hi[-2], hi[-1], p) <= 0:
            hi.pop()
        hi.append(p)
    return lo[:-1] + hi[:-1]


def simplify(h, kmax):
    """Drop vertices of the convex polygon h (ccw), least area loss first, until at most kmax
    remain; the result is inside h."""
    h = list(h)
    while kmax and len(h) > max(kmax, 3):
        best = None
        n = len(h)
        for i in range(n):
            a, b, c = h[i - 1], h[i], h[(i + 1) % n]
            loss = abs((b[0] - a[0]) * (c[1] - a[1]) - (c[0] - a[0]) * (b[1] - a[1]))
            if best is None or loss < best[0]:
                best = (loss, i)
        h.pop(best[1])
    return h


def area(h):
    if len(h) < 3:
        return 0.0
    return abs(sum(h[i][0] * h[(i + 1) % len(h)][1] - h[(i + 1) % len(h)][0] * h[i][1]
                   for i in range(len(h)))) / 2 / Q / Q


def bary_int(p, a, b, c):
    """integer barycentric weights (sum BM) of the float point p in triangle abc, or None."""
    det = (b[0] - a[0]) * (c[1] - a[1]) - (c[0] - a[0]) * (b[1] - a[1])
    if det == 0:
        return None
    l1 = ((p[0] - a[0]) * (c[1] - a[1]) - (c[0] - a[0]) * (p[1] - a[1])) / det
    l2 = ((b[0] - a[0]) * (p[1] - a[1]) - (p[0] - a[0]) * (b[1] - a[1])) / det
    l0 = 1 - l1 - l2
    if min(l0, l1, l2) < -1e-9:
        return None
    L1 = max(0, min(BM, round(l1 * BM))); L2 = max(0, min(BM - L1, round(l2 * BM)))
    L0 = BM - L1 - L2
    return (L0, L1, L2)


class Owned:
    """An owned hull: (step id, owner, ccw vertices on multiples of BM) with fan triangles."""
    def __init__(self, sid, owner, verts):
        self.sid, self.owner, self.verts = sid, owner, verts
        v = verts
        self.tris = [(v[0], v[i], v[i + 1]) for i in range(1, len(v) - 1)] if len(v) >= 3 else []
        self.bbox = (min(p[0] for p in v), max(p[0] for p in v), min(p[1] for p in v), max(p[1] for p in v))


# ---------------------------------------------------------------- one owner step
class Node:
    __slots__ = ('box', 'kind', 'pay', 'ax', 'l', 'r', 'reg')

    def __init__(self, box):
        self.box = box
        self.kind = None
        self.pay = None
        self.ax = None
        self.l = self.r = None
        self.reg = None


class Step:
    """One owner step: build a coarse tree, then refine the alive leaves that bind the core."""
    def __init__(self, sid, o, others, rows_depth=5, eps=0.04, eps_min=None, umin=None,
                 max_iter=None, bind_tol=2e-5, conds=()):
        pr = PROFILES[PROFILE]
        eps_min = pr['eps_min'] if eps_min is None else eps_min
        umin = pr['umin'] if umin is None else umin
        max_iter = pr['max_iter'] if max_iter is None else max_iter
        self.sid, self.o, self.others = sid, o, [h for h in others if h.tris]
        self.hps = HPS[o] + list(conds)
        self.rows_depth, self.eps, self.eps_min, self.umin = rows_depth, eps * Q, eps_min * Q, umin
        self.max_iter, self.bind_tol = max_iter, bind_tol * Q
        self.dead_used = {}      # (sid, tri index) -> {w: weights}

    # -- leaf classification
    def dead(self, tr, xl, xh, yl, yh):
        r = 0.75 * Q
        for hO in self.others:
            ax, bx, ay, by = hO.bbox
            if ax > xh + r or bx < xl - r or ay > yh + r or by < yl - r:
                continue
            for (sid, ti), ws in self.dead_used.items():
                if sid != hO.sid:
                    continue
                for w in ws:
                    if FT.pt_ok(tr, xl, xh, yl, yh, w[0], w[1]):
                        return (sid, ti), w
            P = [(float(p[0]), float(p[1])) for p in hO.verts]
            for hp in region_hps(tr, xl, xh, yl, yh):
                P = clip(P, (float(hp[0]), float(hp[1]), float(hp[2])))
                if not P:
                    break
            if not P:
                continue
            cx = sum(p[0] for p in P) / len(P); cy = sum(p[1] for p in P) / len(P)
            cands = [(cx, cy)] + [(0.5 * cx + 0.5 * p[0], 0.5 * cy + 0.5 * p[1]) for p in P]
            for pt in cands:
                for ti, (a, b, c) in enumerate(hO.tris):
                    lam = bary_int(pt, a, b, c)
                    if lam is None:
                        continue
                    w = ((lam[0] * a[0] + lam[1] * b[0] + lam[2] * c[0]) // BM,
                         (lam[0] * a[1] + lam[1] * b[1] + lam[2] * c[1]) // BM)
                    if FT.pt_ok(tr, xl, xh, yl, yh, w[0], w[1]):
                        key = (hO.sid, ti)
                        self.dead_used.setdefault(key, {})[w] = list(lam)
                        return key, w
                    break
        return None

    def maybe(self, xl, xh, yl, yh):
        r = 0.7072 * Q
        for hO in self.others:
            ax, bx, ay, by = hO.bbox
            dx = max(xl - bx, 0, ax - xh); dy = max(yl - by, 0, ay - yh)
            if dx * dx + dy * dy <= r * r:
                return True
        return False

    def classify(self, nd, eps):
        """Leaf kind of nd, or None (split further)."""
        x0, x1, y0, y1, u0, u1 = nd.box
        wl = FT.wlo(u0, u1)
        xl, xh, yl, yh = max(x0, wl), min(x1, M - wl), max(y0, wl), min(y1, M - wl)
        if xh < xl or yh < yl:
            nd.kind = 'wall'
            return True
        j = FT.outside(self.hps, xl, xh, yl, yh)
        if j is not None:
            nd.kind, nd.pay = 'cell', j
            return True
        tr = FT.triples(u0, u1)
        d = self.dead(tr, xl, xh, yl, yh)
        if d:
            nd.kind, nd.pay = 'dead', d
            return True
        inside = all(A * (xh if A >= 0 else xl) + B * (yh if B >= 0 else yl) <= Cc for A, B, Cc in self.hps)
        if (inside and not self.maybe(xl, xh, yl, yh)) or max(xh - xl, yh - yl) <= eps:
            nd.kind = 'alive'
            nd.reg = [(float(A), float(B), float(C)) for A, B, C in region_hps(tr, xl, xh, yl, yh)]
            nd.pay = (tr, xl, xh, yl, yh)
            return True
        return False

    def split(self, nd, ax):
        x0, x1, y0, y1, u0, u1 = nd.box
        if ax == 'X':
            m = (x0 + x1) // 2; b1, b2 = (x0, m, y0, y1, u0, u1), (m, x1, y0, y1, u0, u1)
        elif ax == 'Y':
            m = (y0 + y1) // 2; b1, b2 = (x0, x1, y0, m, u0, u1), (x0, x1, m, y1, u0, u1)
        else:
            m = (u0 + u1) // 2; b1, b2 = (x0, x1, y0, y1, u0, m), (x0, x1, y0, y1, m, u1)
        nd.ax = ax
        nd.kind = nd.pay = nd.reg = None
        nd.l, nd.r = Node(b1), Node(b2)
        return nd.l, nd.r

    def grow(self, nd, depth, eps):
        """Build below nd (coarse)."""
        stack = [(nd, depth)]
        while stack:
            n, dp = stack.pop()
            x0, x1, y0, y1, u0, u1 = n.box
            if dp < self.rows_depth:
                l, r = self.split(n, 'U')
                stack += [(l, dp + 1), (r, dp + 1)]
                continue
            if self.classify(n, eps):
                continue
            l, r = self.split(n, 'X' if x1 - x0 >= y1 - y0 else 'Y')
            stack += [(l, dp + 1), (r, dp + 1)]

    def leaves(self, kinds=None):
        out = []
        stack = [self.root]
        while stack:
            n = stack.pop()
            if n.ax:
                stack += [n.l, n.r]
            elif kinds is None or n.kind in kinds:
                out.append(n)
        return out

    def core_of(self, alive):
        poly = [(0.0, 0.0), (float(M), 0.0), (float(M), float(M)), (0.0, float(M))]
        for n in alive:
            for h in n.reg:
                poly = clip(poly, h)
                if not poly:
                    return []
        return poly

    def run(self):
        self.root = Node((0, M, 0, M, 0, R))
        self.grow(self.root, 0, self.eps)
        for it in range(self.max_iter):
            alive = self.leaves({'alive'})
            if not alive:
                break
            core = self.core_of(alive)
            if len(core) < 3:
                break
            # binding leaves: a half-plane nearly tight at some core vertex
            bind = []
            for n in alive:
                for A, B, C in n.reg:
                    nr = math.hypot(A, B)
                    if nr and min(C - A * x - B * y for x, y in core) / nr < self.bind_tol:
                        bind.append(n)
                        break
            done = 0
            for n in bind:
                x0, x1, y0, y1, u0, u1 = n.box
                wxy = max(x1 - x0, y1 - y0)
                wu = (u1 - u0) / R * 2 * Q          # angle width, in grid units of length
                if wu >= wxy and u1 - u0 > self.umin:
                    ax = 'U'
                elif wxy > self.eps_min:
                    ax = 'X' if x1 - x0 >= y1 - y0 else 'Y'
                elif u1 - u0 > self.umin:
                    ax = 'U'
                else:
                    continue
                l, r = self.split(n, ax)
                for c in (l, r):
                    self.classify(c, float('inf'))       # one level at a time
                done += 1
            if not done:
                break
        self.alive = [n.pay for n in self.leaves({'alive'})]
        allv = self.leaves()
        self.nleaves = len(allv)
        self.kinds = {}
        for n in allv:
            self.kinds[n.kind] = self.kinds.get(n.kind, 0) + 1
        self.tree = self.to_tuple(self.root)
        return self

    def to_tuple(self, nd):
        if nd.ax:
            return (nd.ax, self.to_tuple(nd.l), self.to_tuple(nd.r))
        if nd.kind == 'alive':
            return ('L', 'alive', None)
        return ('L', nd.kind, nd.pay)

    def core(self):
        return self.core_of(self.leaves({'alive'}))

    def targets(self, h=0.005, shrink=2e-6, inset=3e-5):
        """Vertices of the core, moved inwards by `inset` and rounded to multiples of BM, kept if
        ptOk holds on every alive leaf (the grid spacing `h` is the fallback)."""
        poly = self.core()
        if len(poly) < 3:
            return []
        cx = sum(p[0] for p in poly) / len(poly); cy = sum(p[1] for p in poly) / len(poly)
        cand = []
        for x, y in poly:
            d = math.hypot(cx - x, cy - y)
            if d == 0:
                continue
            t = min(1.0, inset * Q / d)
            X = int(round((x + t * (cx - x)) / BM)) * BM
            Y = int(round((y + t * (cy - y)) / BM)) * BM
            cand.append((X, Y))
        good = [p for p in hull(cand)
                if all(FT.pt_ok(tr, xl, xh, yl, yh, p[0], p[1]) for tr, xl, xh, yl, yh in self.alive)]
        if len(good) >= 3:
            return simplify(hull(good), KMAX)
        return self.grid_targets(poly, h, shrink)

    def grid_targets(self, poly, h, shrink):
        st = max(BM, int(h * Q) // BM * BM)
        xs = [p[0] for p in poly]; ys = [p[1] for p in poly]
        pts = []
        X = math.ceil(min(xs) / st) * st
        while X <= max(xs):
            Y = math.ceil(min(ys) / st) * st
            while Y <= max(ys):
                ok = True
                n = len(poly)
                for i in range(n):
                    a = poly[i]; b = poly[(i + 1) % n]
                    L = math.hypot(b[0] - a[0], b[1] - a[1])
                    if L == 0:
                        continue
                    if ((b[0] - a[0]) * (Y - a[1]) - (b[1] - a[1]) * (X - a[0])) / L < shrink * Q:
                        ok = False
                        break
                if ok:
                    pts.append((X, Y))
                Y += st
            X += st
        hv = [p for p in hull(pts)
              if all(FT.pt_ok(tr, xl, xh, yl, yh, p[0], p[1]) for tr, xl, xh, yl, yh in self.alive)]
        return simplify(hull(hv), KMAX)


# ---------------------------------------------------------------- driver
def exclude(ci, h=0.005, eps=0.02, rows_depth=6, max_rounds=30, log=print):
    J = CAN[ci]
    cur = {}                       # owner -> Owned
    steps = []                     # (Step, Owned or None)
    t0 = time.time()
    for rnd in range(max_rounds):
        progress = False
        for o in J:
            others = [cur[o2] for o2 in J if o2 != o and o2 in cur]
            st = Step(len(steps), o, others).run()
            if not st.alive:
                steps.append((st, None))
                log(f'rnd {rnd} owner {o}: TERMINAL leaves {st.nleaves} {st.kinds} ({time.time() - t0:.0f}s)')
                return J, steps
            tg = st.targets(h)
            nalive = len(st.alive)
            st.root = None                   # keep only the encoded tree (memory)
            st.alive = None
            new = None
            if len(tg) >= 3 and area(tg) > (area(cur[o].verts) if o in cur else 0) + 1e-6:
                new = Owned(st.sid, o, tg)
                cur[o] = new
                progress = True
            steps.append((st, new))
            log(f'rnd {rnd} owner {o}: leaves {st.nleaves} alive {nalive} {st.kinds} '
                f'hull {len(tg)} area {area(cur[o].verts) if o in cur else 0:.4f} ({time.time() - t0:.0f}s)')
        if not progress:
            log('no progress')
            return J, None
    return J, None


def needed(steps):
    """step ids in the dependency closure of the terminal step."""
    need = set()
    stack = [steps[-1][0].sid]
    while stack:
        s = stack.pop()
        if s in need:
            continue
        need.add(s)
        for (sid, ti) in steps[s][0].dead_used:
            stack.append(sid)
    return sorted(need)


# ---------------------------------------------------------------- Lean output
def encode(t, opt_index, T_index, ntg, out):
    if t[0] == 'L':
        kind, pay = t[1], t[2]
        if kind == 'wall':
            out.append(0)
        elif kind == 'cell':
            out += [1, pay]
        elif kind == 'dead':
            key, w = pay
            i, k = opt_index[key][0], opt_index[key][1][w]
            out += [2, i, 1, k]
        else:
            out += [2, T_index, ntg] + [0] * ntg
        return
    out.append({'X': 3, 'Y': 4, 'U': 5}[t[0]])
    encode(t[1], opt_index, T_index, ntg, out)
    encode(t[2], opt_index, T_index, ntg, out)


def numeral(digits):
    n = 0
    for d in reversed(digits):
        assert 0 <= d < BASE, d
        n = n * BASE + d
    return n


def nleaves(t):
    return 1 if t[0] == 'L' else nleaves(t[1]) + nleaves(t[2])


def pts(g):
    return "[" + ", ".join(f"({x}, {y})" for x, y in g) + "]"


def emit_case(ci, J, steps, outdir, prefix="U2P"):
    """Lean files for case ci under outdir/C{ci}/ (modules `Sqpack.S11Opt.Split.<prefix>.C<ci>`)."""
    ns = f"SquarePacking.S11Opt.Split.{prefix}.C{ci}"
    mod = f"Sqpack.S11Opt.Split.{prefix}.C{ci}"
    opn = "" if prefix == "U2P" else "open SquarePacking.S11Opt.Split.U2P\n"
    d = os.path.join(outdir, f"C{ci}")
    os.makedirs(d, exist_ok=True)
    keep = needed(steps)
    ren = {s: n for n, s in enumerate(keep)}
    owned_of = {st.sid: new for st, new in steps}
    data = [f"import Sqpack.S11Opt.Split.U2P.Rules\n",
            f"/-! Generated by `scripts/u2p/gen_u2p.py`: case {ci}, cells {list(J)}. -/\n",
            "set_option linter.style.longLine false\n", "set_option maxRecDepth 100000\n",
            f"namespace {ns}\n", "open FieldTree\n" + opn,
            f"def J : List ℕ := {list(J)}\n"]
    stepinfo = []
    for s in keep:
        st, new = steps[s]
        n = ren[s]
        # options: used triangles, in a fixed order
        keys = sorted(st.dead_used)
        opt_index = {}
        tri_lines = []
        for i, key in enumerate(keys):
            sid, ti = key
            hO = owned_of[sid]
            a, b, c = hO.tris[ti]
            ws = sorted(st.dead_used[key])
            opt_index[key] = (i, {w: k for k, w in enumerate(ws)})
            tri_lines.append(f"({hO.owner}, ({a[0]}, {a[1]}), ({b[0]}, {b[1]}), ({c[0]}, {c[1]}), {pts(ws)}, "
                             f"[{', '.join('[' + ', '.join(map(str, st.dead_used[key][w])) + ']' for w in ws)}])")
        data.append(f"/-- Step {n}: owner {st.o}. -/")
        data.append(f"def tris{n} : List Tri := [{', '.join(tri_lines)}]")
        tg = new.verts if new else []
        if new:
            data.append(f"def tgt{n} : List (ℕ × ℕ) := {pts(tg)}")
            data.append(f"def opts{n} : List (List (List (ℕ × ℕ))) := stepOpts tris{n} tgt{n}\n")
        else:
            data.append(f"def opts{n} : List (List (List (ℕ × ℕ))) := triOpts tris{n}\n")
        stepinfo.append((n, st, new, keys, opt_index, len(keys), len(tg)))
    data.append(f"end {ns}\n")
    open(os.path.join(d, "Data.lean"), "w").write("\n".join(data))
    # trees
    for n, st, new, keys, opt_index, T_index, ntg in stepinfo:
        lines = [f"import {mod}.Data\n", "set_option linter.style.longLine false\n",
                 f"namespace {ns}\n", "open FieldTree\n" + opn]
        cnt = [0]

        def chunks(t, box):
            x0, x1, y0, y1, u0, u1 = box
            stmt = f"CovF G.Q G.M G.R (hpsC {st.o}) opts{n} {x0} {x1} {y0} {y1} {u0} {u1}"
            cnt[0] += 1
            nm = f"cov{n}_{cnt[0]}"
            if nleaves(t) <= CHUNK:
                dg = []
                encode(t, opt_index, T_index, ntg, dg)
                lines.append(f"theorem {nm} : {stmt} :=\n  soundDec G.Q G.M G.R {BASE} {FUEL} {numeral(dg)} "
                             f"G.Q_pos G.R_pos (hpsC {st.o}) opts{n} (by decide +kernel)\n")
                return nm
            ax = t[0]
            if ax == 'X':
                m = (x0 + x1) // 2; b1, b2 = (x0, m, y0, y1, u0, u1), (m, x1, y0, y1, u0, u1)
            elif ax == 'Y':
                m = (y0 + y1) // 2; b1, b2 = (x0, x1, y0, m, u0, u1), (x0, x1, m, y1, u0, u1)
            else:
                m = (u0 + u1) // 2; b1, b2 = (x0, x1, y0, y1, u0, m), (x0, x1, y0, y1, m, u1)
            l = chunks(t[1], b1)
            r = chunks(t[2], b2)
            lines.append(f"theorem {nm} : {stmt} :=\n  CovF.split{ax} {m} {l} {r}\n")
            return nm
        root = chunks(st.tree, (0, M, 0, M, 0, R))
        lines.append(f"theorem cov{n} : CovF G.Q G.M G.R (hpsC {st.o}) opts{n} 0 {M} 0 {M} 0 {R} := {root}\n")
        lines.append(f"end {ns}\n")
        open(os.path.join(d, f"S{n}.lean"), "w").write("\n".join(lines))
    # main
    L = [f"import {mod}.S{n}" for n, *_ in stepinfo]
    L += ["\nset_option linter.style.longLine false\nset_option maxRecDepth 100000\n", f"namespace {ns}\n", "open FieldTree\n" + opn,
          f"lemma hJ : J = maskAt {ci} := by decide +kernel\n"]
    # owned facts
    def tri_valid_proof(n, st, keys):
        if not keys:
            return "by intro t ht; simp [tris%d] at ht" % n
        out = [f"by", f"    intro t ht",
               f"    simp only [tris{n}, List.mem_cons, List.not_mem_nil, or_false] at ht",
               f"    rcases ht with " + " | ".join("rfl" for _ in keys)]
        for key in keys:
            sid = key[0]
            m = ren[sid]
            out.append(f"    · exact ⟨by decide, by decide, own{m} _ (by decide), own{m} _ (by decide), "
                       f"own{m} _ (by decide), by decide +kernel⟩")
        return "\n".join(out)
    for n, st, new, keys, opt_index, T_index, ntg in stepinfo:
        if new:
            L.append(f"theorem own{n} : ∀ p ∈ tgt{n}, Owned Ux J {st.o} p :=\n"
                     f"  owned_all_of_tris le_rfl (by norm_num [Ux]) (by decide) (by decide)\n"
                     f"    ({tri_valid_proof(n, st, keys)}) cov{n}\n")
        else:
            L.append(f"theorem notIn : ¬ RealizesIn Ux J :=\n"
                     f"  excluded_of_tris le_rfl (by norm_num [Ux]) (by decide) (by decide)\n"
                     f"    ({tri_valid_proof(n, st, keys)}) cov{n}\n")
    L.append(f"theorem excluded : CaseExcluded (maskAt {ci}) := by\n  rw [← hJ]; exact caseExcluded_of_not_in notIn\n")
    L.append(f"end {ns}\n")
    open(os.path.join(d, "Main.lean"), "w").write("\n".join(L))
    tot = sum(nleaves(st.tree) for _, st, *_ in stepinfo)
    return len(keep), tot


if __name__ == '__main__':
    # python3 gen_u2p.py CASE OUTDIR [PREFIX] [KMAX]   (CASE: the author's canonical index, as `maskAt`)
    ci = int(sys.argv[1]); outdir = sys.argv[2]
    prefix = sys.argv[3] if len(sys.argv) > 3 else "U2P"
    if len(sys.argv) > 4:
        KMAX = int(sys.argv[4])
    J, steps = exclude(ci, log=lambda s: print(s, flush=True))
    if steps is None:
        print('FAILED'); sys.exit(1)
    k, tot = emit_case(ci, J, steps, outdir, prefix)
    print(f'case {ci}: {len(steps)} steps searched, {k} kept, {tot} leaves in the certificate')
