"""Emit Lean certificates for one archived capture step as an `ExtStep` (untrusted).

Prototype: far15y-self-300, step 7 (owner cell 8), whose rows are all forbidden.
Inputs are the author's JSON files, read locally; nothing of them is committed.

    python3 gen_step.py <far15y-self-300.json> <root-self-240.json> <out dir>
"""
import json, sys, os
from fractions import Fraction as F
from geom import hull, halfplanes, contains, vertices, implies_mu, empty_mu, bary

ROLE_CELL = [3, 15, 8, 0, 4, 1, 2, 11, 9, 10, 13]
OWNER = {c: i for i, c in enumerate(ROLE_CELL)}
COVER = F(387708359002281417731, 10 ** 20)


def cs(t):
    return ((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))


def envelope(lo, hi):
    """The author's support factor M for the reference axes at the mid parameter."""
    t = (lo + hi) / 2
    c, s = cs(t)
    rel = []
    for a in (lo, hi):
        ca, sa = cs(a)
        rel.append((c * ca + s * sa, c * sa - s * ca))
    narrow = all(d >= abs(x) for d, x in rel)
    M = max(d + abs(x) for d, x in rel) if narrow else F(3, 2)
    return (c, s), M


# --- mirrors of the Lean Boolean checks (to fail early) -----------------------
def qv(c0, c1, c2, t):
    return c0 + c1 * t + c2 * t * t


def nnQ(c0, c1, c2, a, b):
    if qv(c0, c1, c2, a) < 0 or qv(c0, c1, c2, b) < 0:
        return False
    if c2 > 0 and c1 + 2 * c2 * a < 0 < c1 + 2 * c2 * b:
        return 4 * c0 * c2 - c1 * c1 >= 0
    return True


def posQ(c0, c1, c2, a, b):
    if qv(c0, c1, c2, a) <= 0 or qv(c0, c1, c2, b) <= 0:
        return False
    if c2 > 0 and c1 + 2 * c2 * a < 0 < c1 + 2 * c2 * b:
        return 4 * c0 * c2 - c1 * c1 > 0
    return True


def supportB(n1, n2, M, a, b):
    return (nnQ(M - n1 - n2, -2 * n2 + 2 * n1, M + n1 + n2, a, b) and
            nnQ(M - n1 + n2, -2 * n2 - 2 * n1, M + n1 - n2, a, b) and
            nnQ(M + n1 - n2, 2 * n2 + 2 * n1, M - n1 + n2, a, b) and
            nnQ(M + n1 + n2, 2 * n2 - 2 * n1, M - n1 - n2, a, b))


def coreVB(a, b, v):
    return (posQ(F(1, 2) - v[0], -2 * v[1], F(1, 2) + v[0], a, b) and
            posQ(F(1, 2) + v[0], 2 * v[1], F(1, 2) - v[0], a, b) and
            posQ(F(1, 2) - v[1], 2 * v[0], F(1, 2) + v[1], a, b) and
            posQ(F(1, 2) + v[1], -2 * v[0], F(1, 2) - v[1], a, b))


def wallB(h, a, b):
    return nnQ(1 - 2 * h, F(2), -1 - 2 * h, a, b)


def wall_halves(h):
    return [(F(-1), F(0), -h), (F(1), F(0), COVER - h), (F(0), F(-1), -h), (F(0), F(1), COVER - h)]


# --- cover trees --------------------------------------------------------------
class Region:
    """A forbidden triangle: vertices w_m = k_m - v_m."""

    def __init__(self, owner, ks, vs):
        self.owner, self.ks, self.vs = owner, ks, vs
        self.w = [(k[0] - v[0], k[1] - v[1]) for k, v in zip(ks, vs)]
        H = hull(self.w)
        assert len(H) == 3
        self.hs = halfplanes(H)
        self.lam = bary(self.w)


def minkowski_regions(owner, K, Q):
    """Fan-triangulate hull(K) - hull(Q); every vertex is some k - v."""
    pairs = {}
    for k in K:
        for v in Q:
            pairs.setdefault((k[0] - v[0], k[1] - v[1]), (k, v))
    H = hull(list(pairs))
    out = []
    for m in range(1, len(H) - 1):
        tri = [H[0], H[m], H[m + 1]]
        out.append(Region(owner, [pairs[p][0] for p in tri], [pairs[p][1] for p in tri]))
    return out


def centroid(V):
    n = len(V)
    return (sum(p[0] for p in V) / n, sum(p[1] for p in V) / n)


def build(hs, regions, stats, depth=0):
    V = vertices(hs)
    if not V:
        mu = empty_mu(hs)
        assert mu is not None, 'empty polygon without a Farkas certificate'
        stats['empty'] += 1
        return ('empty', mu)
    for R in regions:
        if all(contains(h, p) for h in R.hs for p in V):
            mus = []
            for (a, b, c) in R.lam:
                mu = implies_mu(hs, (-a, -b, c), V)
                assert mu is not None
                mus.append(mu)
            stats['forbid'] += 1
            return ('forbid', R, mus)
    assert depth < 60, 'cover tree too deep'
    c = centroid(V)
    cand = [R for R in regions if all(contains(h, c) for h in R.hs)]
    assert cand, 'centroid not covered: the archived cover does not cover this polygon'
    R = cand[0]
    for e in R.hs:
        if any(not contains(e, p) for p in V):
            stats['split'] += 1
            ne = (-e[0], -e[1], -e[2])
            return ('split', e, build([e] + hs, regions, stats, depth + 1),
                    build([ne] + hs, regions, stats, depth + 1))
    raise AssertionError('unreachable')


# --- Lean emission ------------------------------------------------------------
def q(x):
    x = F(x)
    return f"({x.numerator})" if x.denominator == 1 else f"({x.numerator}/{x.denominator})"


def qp(p):
    return f"({q(p[0])}, {q(p[1])})"


def half(h):
    return f"⟨{q(h[0])}, {q(h[1])}, {q(h[2])}⟩"


def lst(xs):
    return "[" + ", ".join(xs) + "]"


def tree_lean(t):
    if t[0] == 'empty':
        return f"(.empty {lst(q(m) for m in t[1])})"
    if t[0] == 'forbid':
        R, mus = t[1], t[2]
        lam = lst(f"({q(a)}, {q(b)}, {q(c)})" for a, b, c in R.lam)
        return (f"(.forbid {R.owner} ⟨{lst(qp(k) for k in R.ks)}, {lst(qp(v) for v in R.vs)}, {lam}, "
                f"{lst(lst(q(m) for m in mu) for mu in mus)}⟩)")
    return f"(.split {half(t[1])}\n    {tree_lean(t[2])}\n    {tree_lean(t[3])})"


def main(far_path, root_path, out_dir):
    far = json.load(open(far_path))
    root = json.load(open(root_path))
    B = F(far['B'])

    def phys(p):
        return (F(p[0]) / B, F(p[1]) / B)

    step = far['steps'][7]
    cell = step['owner']
    i = OWNER[cell]
    prior = json.loads(step['prior_owned_hulls']) if isinstance(step['prior_owned_hulls'], str) \
        else step['prior_owned_hulls']
    owned = {OWNER[int(c)]: hull([phys(p) for p in pts]) for c, pts in prior.items()}
    old = {json.dumps(r['reference'], sort_keys=True): r for r in root['final_state']['cells'][str(cell)]}
    rows, certs = [], []
    stats = dict(empty=0, forbid=0, split=0)
    for r in step['rows']:
        o = old[json.dumps(r['prior_reference'], sort_keys=True)]
        if not o['residual_polygons']:
            continue
        a, b = map(F, r['interval'])
        oa, ob = map(F, o['interval'])
        assert (a, b) == (oa, ob)
        centers = hull([phys(p) for poly in o['residual_polygons'] for p in poly])
        row_hs = halfplanes(centers)
        rows.append((oa, ob, row_hs))
        # self cuts
        (c, s), M = envelope(a, b)
        own = owned[i]
        cuts = []
        for n in ((c, s), (-s, c)):
            assert supportB(n[0], n[1], M, a, b)
            vmin = min(own, key=lambda v: n[0] * v[0] + n[1] * v[1])
            vmax = max(own, key=lambda v: n[0] * v[0] + n[1] * v[1])
            cuts.append((n, M, False, vmin, n[0] * vmin[0] + n[1] * vmin[1] + M / 2))
            cuts.append((n, M, True, vmax, -(n[0] * vmax[0] + n[1] * vmax[1]) + M / 2))
        cut_hs = [((-1 if neg else 1) * n[0], (-1 if neg else 1) * n[1], u) for n, M_, neg, v, u in cuts]
        h = min(sum(cs(a)), sum(cs(b))) / 2
        assert wallB(h, a, b)
        core = [phys(v) for v in r['core_vertices']]
        assert all(coreVB(a, b, v) for v in core)
        regions = []
        for j, K in owned.items():
            if j != i and K:
                regions += minkowski_regions(j, K, core)
        poly = row_hs + cut_hs + wall_halves(h)
        tree = build(poly, regions, stats)
        certs.append(dict(a=a, b=b, cuts=cuts, h=h, core=core, tree=tree))
    print(f"owner {i} (cell {cell}): {len(rows)} rows; leaves {stats}", file=sys.stderr)

    L = ["import ElevenSquare.Tasks.T07.Ext.Check", "import ElevenSquare.Tasks.T07.CaptureTraceCombinators", "",
         "/-! Generated by `scripts/wand125_u5/gen_step.py` from the author's far15y-self-300.json,",
         "step 7.  Do not edit by hand. -/", "",
         "namespace ElevenSquare.Tasks.T07.Ext.Far15S7",
         "open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext", "",
         "set_option maxRecDepth 100000", ""]
    for n, (lo, hi, hs) in enumerate(rows):
        L.append(f"def row{n} : PoseRow := {{ lo := {q(lo)}, hi := {q(hi)}, centers := {lst(half(x) for x in hs)} }}")
    L.append("")
    L.append(f"def oldRows : List PoseRow := {lst(f'row{n}' for n in range(len(rows)))}")
    L.append("def owned : Owner → List QPoint := ![" + ", ".join(
        lst(qp(p) for p in owned.get(j, [])) for j in range(11)) + "]")
    L.append(f"def state : PoseState where\n  rows j := if j = {i} then oldRows else []\n  owned := owned\n")
    for n, ct in enumerate(certs):
        cuts = lst(f"⟨{q(nv[0])}, {q(nv[1])}, {q(M_)}, {'true' if neg else 'false'}, {qp(v)}, {q(u)}⟩"
                   for nv, M_, neg, v, u in ct['cuts'])
        L.append(f"def sub{n} : Sub := ⟨{q(ct['a'])}, {q(ct['b'])}, {cuts}, {q(ct['h'])}, "
                 f"{lst(qp(v) for v in ct['core'])},\n  {tree_lean(ct['tree'])}⟩\n")
    L.append(f"def certs : List (List Sub) := {lst(f'[sub{n}]' for n in range(len(certs)))}\n")
    L.append(f"theorem step_ok : stepB state {i} [] certs = true := by decide +kernel\n")
    L.append("/-- The archived step 7 of the far15 branch empties the rows of its owner. -/")
    L.append(f"theorem step_terminal : ExtTrace state (replaceRows state {i} []) ∧ Terminal (replaceRows state {i} []) :=")
    L.append(f"  ⟨ExtTrace.cons (stepB_sound step_ok) (ExtTrace.refl _),")
    L.append(f"    terminal_of_empty_owner _ {i} (by simp [replaceRows])⟩\n")
    open(os.path.join(out_dir, "Far15S7.lean"), "w").write("\n".join(L) + "\nend ElevenSquare.Tasks.T07.Ext.Far15S7\n")


if __name__ == "__main__":
    main(*sys.argv[1:4])
