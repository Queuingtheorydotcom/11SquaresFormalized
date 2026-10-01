"""The scaled grid of the box trees and evand's containment test `ptOk`, in exact integers.

Mirrors `Shared/Grid.lean` (`G.Q`, `G.M`, `G.R`, `G.sc`, the cell half-planes `G.hps0 … G.hps15`)
and `BoxTree.ptOk`/`wlo`, after 9c's `scripts/s11opt/field_tree.py`.  The sites are read from
`lean/Sqpack/S11Opt/Cells.lean` (`PU`), so no file of the author is needed.
"""
import os
import re
from fractions import Fraction as F
from math import ceil, gcd

U = F(387708359002281417731, 10 ** 20)
Q = 2 ** 32
R = 2 ** 24
s = 1 - F(1, 2 ** 20)
M = ceil(Q * U / s)


def _sites():
    here = os.path.dirname(os.path.abspath(__file__))
    src = open(os.path.join(here, '..', '..', 'lean', 'Sqpack', 'S11Opt', 'Cells.lean')).read()
    m = re.search(r'def PU : Fin 16 → ℝ × ℝ := !\[(.*?)\]\n', src, re.S)
    v = [F(int(a), int(b)) for a, b in re.findall(r'\((\d+) / (\d+) : ℝ\)', m.group(1))]
    return [(v[2 * i], v[2 * i + 1]) for i in range(16)]


PU = _sites()


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


def cell_halfplanes(k):
    """Cell k as integer half-planes (A, B, C): A X + B Y <= C on the scaled grid."""
    pk = PU[k]
    out = []
    for j, pj in enumerate(PU):
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
    """Index of a half-plane excluding the rectangle (mirror of `FieldTree.outOk`)."""
    for j, (A, Bc, Cc) in enumerate(hps):
        if Cc < A * (xl if A >= 0 else xh) + Bc * (yl if Bc >= 0 else yh):
            return j
    return None
