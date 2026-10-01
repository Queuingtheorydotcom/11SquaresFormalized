"""Exact rational planar geometry for the U5 certificate emitter (untrusted).

Half-plane (a, b, c) means a*x + b*y <= c.  Polygons are convex; a polygon is
kept both as a half-plane list (what Lean sees) and as its vertex list.
"""
from fractions import Fraction as F
from itertools import combinations


def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def hull(points):
    """Convex hull, counter-clockwise, collinear points removed."""
    pts = sorted(set(points))
    if len(pts) <= 2:
        return pts
    lower, upper = [], []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def halfplanes(H):
    """Half-planes of a counter-clockwise convex polygon with >= 3 vertices."""
    out = []
    n = len(H)
    for k in range(n):
        p, q = H[k], H[(k + 1) % n]
        # interior on the left: (q - p) x (x - p) >= 0  <=>  a x + b y <= c
        a = q[1] - p[1]
        b = p[0] - q[0]
        c = a * p[0] + b * p[1]
        out.append((a, b, c))
    return out


def contains(h, p):
    return h[0] * p[0] + h[1] * p[1] <= h[2]


def vertices(hs):
    """Vertices of the (bounded) intersection of half-planes; [] if empty."""
    pts = set()
    for (a1, b1, c1), (a2, b2, c2) in combinations(hs, 2):
        det = a1 * b2 - a2 * b1
        if det == 0:
            continue
        x = (c1 * b2 - c2 * b1) / det
        y = (a1 * c2 - a2 * c1) / det
        p = (x, y)
        if all(contains(h, p) for h in hs):
            pts.add(p)
    return hull(list(pts)) if len(pts) > 2 else sorted(pts)


def implies_mu(hs, g, V=None):
    """Multipliers mu >= 0 (len(hs)) with sum mu*h = (g.a, g.b, <= g.c), or None."""
    V = vertices(hs) if V is None else V
    if not V:
        return None
    best = max(V, key=lambda p: g[0] * p[0] + g[1] * p[1])
    if g[0] * best[0] + g[1] * best[1] > g[2]:
        return None
    tight = [k for k, h in enumerate(hs) if h[0] * best[0] + h[1] * best[1] == h[2]]
    # a single parallel tight half-plane
    for k in tight:
        a, b, _ = hs[k]
        if a * g[1] - b * g[0] == 0:
            lam = (g[0] / a) if a != 0 else (g[1] / b) if b != 0 else None
            if lam is not None and lam >= 0 and (a * lam, b * lam) == (g[0], g[1]):
                mu = [F(0)] * len(hs)
                mu[k] = lam
                return mu
    for k1, k2 in combinations(tight, 2):
        a1, b1, _ = hs[k1]
        a2, b2, _ = hs[k2]
        det = a1 * b2 - a2 * b1
        if det == 0:
            continue
        m1 = (g[0] * b2 - g[1] * a2) / det
        m2 = (a1 * g[1] - b1 * g[0]) / det
        if m1 >= 0 and m2 >= 0:
            mu = [F(0)] * len(hs)
            mu[k1] += m1
            mu[k2] += m2
            return mu
    if g[0] == 0 and g[1] == 0 and g[2] >= 0:
        return [F(0)] * len(hs)
    return None


def empty_mu(hs):
    """Farkas multipliers proving the half-planes have no common point."""
    n = len(hs)
    for k1, k2 in combinations(range(n), 2):
        a1, b1, c1 = hs[k1]
        a2, b2, c2 = hs[k2]
        if a1 * b2 - a2 * b1 != 0:
            continue
        # parallel: need opposite directions
        if a1 != 0:
            lam = -a2 / a1
        elif b1 != 0:
            lam = -b2 / b1
        else:
            if c1 < 0:
                mu = [F(0)] * n
                mu[k1] = F(1)
                return mu
            continue
        if lam > 0 and lam * c1 + c2 < 0:
            mu = [F(0)] * n
            mu[k1] = lam
            mu[k2] = F(1)
            return mu
    for k in range(n):
        a, b, c = hs[k]
        if a == 0 and b == 0 and c < 0:
            mu = [F(0)] * n
            mu[k] = F(1)
            return mu
    for k1, k2, k3 in combinations(range(n), 3):
        (a1, b1, c1), (a2, b2, c2), (a3, b3, c3) = hs[k1], hs[k2], hs[k3]
        # null vector of [[a1 a2 a3],[b1 b2 b3]]
        m1 = a2 * b3 - a3 * b2
        m2 = a3 * b1 - a1 * b3
        m3 = a1 * b2 - a2 * b1
        for s in (1, -1):
            u1, u2, u3 = s * m1, s * m2, s * m3
            if u1 >= 0 and u2 >= 0 and u3 >= 0 and (u1, u2, u3) != (0, 0, 0):
                if u1 * c1 + u2 * c2 + u3 * c3 < 0:
                    mu = [F(0)] * n
                    mu[k1], mu[k2], mu[k3] = u1, u2, u3
                    return mu
    return None


def bary(w):
    """Affine barycentric coordinates (alpha, beta, gamma) of a triangle w0 w1 w2."""
    (x0, y0), (x1, y1), (x2, y2) = w
    det = (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)
    assert det != 0
    # lambda1 = ((x - x0)(y2 - y0) - (x2 - x0)(y - y0)) / det
    a1 = (y2 - y0) / det
    b1 = -(x2 - x0) / det
    c1 = (-x0 * (y2 - y0) + (x2 - x0) * y0) / det
    a2 = -(y1 - y0) / det
    b2 = (x1 - x0) / det
    c2 = (x0 * (y1 - y0) - (x1 - x0) * y0) / det
    a0, b0, c0 = -a1 - a2, -b1 - b2, 1 - c1 - c2
    return [(a0, b0, c0), (a1, b1, c1), (a2, b2, c2)]
