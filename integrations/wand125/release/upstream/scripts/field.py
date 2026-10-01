"""Exact arithmetic in Q(u0), u0 the root of P in (9/25, 37/100).

Elements are coefficient lists over Fraction, low degree first, reduced mod P (degree <= 7).
"""
from fractions import Fraction as F

P = [F(c) for c in (-1, 2, 2, -6, 12, 14, -2, -10, 5)]  # low -> high: 5u^8-10u^7-2u^6+14u^5+12u^4-6u^3+2u^2+2u-1


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def add(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def neg(a):
    return [-x for x in a]


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    if not a or not b:
        return []
    r = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return trim(r)


def divmod_(a, b):
    """a = q*b + r."""
    a = trim(a)
    b = trim(b)
    q = [F(0)] * max(len(a) - len(b) + 1, 1)
    r = list(a)
    while len(r) >= len(b) and r:
        d = len(r) - len(b)
        c = r[-1] / b[-1]
        q[d] = c
        r = sub(r, [F(0)] * d + [c * x for x in b])
    return trim(q), trim(r)


def red(a):
    return divmod_(a, P)[1]


def inv(a):
    # extended Euclid: s*a + t*P = g (constant)
    r0, r1 = trim(P), trim(a)
    s0, s1 = [], [F(1)]
    while len(r1) > 1:
        q, r = divmod_(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, sub(s0, mul(q, s1))
    assert len(r1) == 1
    return red([x / r1[0] for x in s1])


def const(x):
    return trim([F(x)])


def ev(a, x):
    acc = F(0)
    for c in reversed(a):
        acc = acc * x + c
    return acc


def horner_iv(a, lo, hi):
    """Mirror of the Lean `hIv`: interval enclosure of a on [lo, hi]."""
    l = h = F(0)
    for c in reversed(a):
        prods = [lo * l, lo * h, hi * l, hi * h]
        l, h = c + min(prods), c + max(prods)
    return l, h


def root_interval(bits=200):
    lo, hi = F(9, 25), F(37, 100)
    assert ev(P, lo) < 0 < ev(P, hi)
    # bisect to a dyadic-ish interval of width 2^-bits
    for _ in range(bits):
        m = (lo + hi) / 2
        if ev(P, m) < 0:
            lo = m
        else:
            hi = m
    return lo, hi
