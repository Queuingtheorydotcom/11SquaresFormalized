"""U4 local isolation: rows, remainder constants, dual certificates (exact integer check).

Mirrors the Lean checker in Sqpack/S11Opt/Split/U4/Dual.lean.  Perturbation coordinates:
h[3i], h[3i+1] = centre offsets of square i, h[3i+2] = angle offset (radians).
Rows are `sum_k A_k h_k / DA + tau * kt / DK >= 0`.
"""
import os, sys, json, ast, itertools
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from field import P, add, sub, mul, red, const, neg, horner_iv, ev, root_interval
from construct import build

DA = 10 ** 20   # row coefficients
DL = 10 ** 12   # dual multipliers
DK = 10 ** 20   # remainder constants
DR = 10 ** 10   # radii
DIGITS = 40

d = build()
cA, sA, T, SQS = d['c'], d['s'], d['T'], d['sq']
X = [sq[0][0] for sq in SQS]; Y = [sq[0][1] for sq in SQS]
TILT = [sq[1] == 'a' for sq in SQS]
l0, _ = root_interval(4 * DIGITS)
LO = F(int(l0 * 10 ** DIGITS), 10 ** DIGITS); HI = LO + F(1, 10 ** DIGITS)
assert ev(P, LO) < 0 < ev(P, HI)

RADII_STR = ['18767167/10000000000', '4435327/2000000000', '5670363/2500000000', '1636033/1000000000', '6880181/5000000000', '1764113/1000000000', '8962451/10000000000', '5212397/5000000000', '5670363/2500000000', '1635053/1000000000', '10683139/10000000000', '1890121/1250000000', '4087019/2500000000', '13962901/10000000000', '20161291/10000000000', '12900283/10000000000', '534153/500000000', '1890121/1250000000', '678279/500000000', '4124329/5000000000', '35312013/10000000000', '11182451/10000000000', '3232837/5000000000', '8824483/2500000000', '9356857/10000000000', '8671199/10000000000', '7549783/5000000000', '293551/400000000', '10335557/10000000000', '40352153/10000000000', '1920157/2500000000', '8222903/2500000000', '67647473/10000000000']
R = [F(x) for x in RADII_STR]
RI = [int(x * DR) for x in R]
assert all(F(ri, DR) == x for ri, x in zip(RI, R))

ONE = const(1)
def cneg(p): return neg(p)
# cos/sin of ang_i + m*pi/2 as polynomials in u
def trig(tilted, m):
    c0, s0 = (cA, sA) if tilted else (ONE, [])
    return [(c0, s0), (cneg(s0), c0), (cneg(c0), cneg(s0)), (s0, cneg(c0))][m % 4]
# cos/sin of (ang p - ang o) - m*pi/2
def trig_diff(tp, to, m):
    if tp == to: c0, s0 = ONE, []
    elif tp: c0, s0 = cA, sA           # +a
    else: c0, s0 = cA, cneg(sA)       # -a
    # cos(t - m pi/2), sin(t - m pi/2)
    return [(c0, s0), (s0, cneg(c0)), (cneg(c0), cneg(s0)), (cneg(s0), c0)][m % 4]

def enc(p):
    """Interval of an (unreduced) polynomial on [LO, HI], as the Lean `hIv`."""
    if not p: return F(0), F(0)
    return horner_iv(p, LO, HI)
def iszero(p): return red(p) == []
def sign(p):
    if iszero(p): return 0
    lo, hi = enc(red(p)); assert lo > 0 or hi < 0; return 1 if lo > 0 else -1

def approx(p):
    """Integer N with |p - N/DA| <= e; e rounded up to a multiple of 1/(10*DA)."""
    lo, hi = enc(p)
    N = round((lo + hi) / 2 * DA)
    e = max(abs(lo - F(N, DA)), abs(hi - F(N, DA)))
    e = F(-((-e * 10 * DA).numerator // (e * 10 * DA).denominator), 10 * DA) if e else F(0)
    return N, e
def absbound(p):
    lo, hi = enc(p); b = max(abs(lo), abs(hi))
    q = 10 ** 15
    return F(-((-b * q).numerator // (b * q).denominator), q)

SIGNS = [(1, 1), (1, -1), (-1, 1), (-1, -1)]

def pair_corner(o, p, m, s):
    s1, s2 = s
    C0, S0 = trig(TILT[o], m)
    cph, sph = trig_diff(TILT[p], TILT[o], m)
    Dx, Dy = sub(X[p], X[o]), sub(Y[p], Y[o])
    Pv = add(mul(C0, Dx), mul(S0, Dy))
    Pd = add(mul(cneg(S0), Dx), mul(C0, Dy))
    z0 = [x / 2 for x in sub(mul(const(s1), cph), mul(const(s2), sph))]
    zd = [x / 2 for x in sub(mul(const(-s1), sph), mul(const(s2), cph))]
    g0 = sub(add(Pv, z0), const(F(1, 2)))
    G = sub(Pd, zd)
    q = dict(kind='pair', o=o, p=p, m=m, s=s, C0=C0, S0=S0, Pv=Pv, Pd=Pd, z0=z0, zd=zd, g0=g0, G=G)
    (Cn, eC), (Sn, eS), (Gn, eG), (Zn, eZ) = approx(C0), approx(S0), approx(G), approx(zd)
    bP, bPd, bz, bzd = absbound(Pv), absbound(Pd), absbound(z0), absbound(zd)
    Rx = R[3*o] + R[3*p]; Ry = R[3*o+1] + R[3*p+1]; wo = R[3*o+2]; wp = R[3*p+2]
    K = (bP * wo**2 / 2 + bPd * wo**3 / 6 + (Rx + Ry) * wo**2 / 2 + (Rx + Ry) * wo
         + bz * (wo + wp)**2 / 2 + bzd * (wo + wp)**3 / 6 + eC * Rx + eS * Ry + eG * wo + eZ * wp)
    q.update(Cn=Cn, eC=eC, Sn=Sn, eS=eS, Gn=Gn, eG=eG, Zn=Zn, eZ=eZ, bP=bP, bPd=bPd, bz=bz, bzd=bzd, K=K)
    q['sparse'] = [(3*p, Cn), (3*o, -Cn), (3*p+1, Sn), (3*o+1, -Sn), (3*o+2, Gn), (3*p+2, Zn)]
    return q

def wall(i, coord, side, s):
    s1, s2 = s
    C0, S0 = trig(TILT[i], 0)
    Fv = add(mul(const(s1), C0), mul(const(s2), S0))
    Fd = add(mul(const(-s1), S0), mul(const(s2), C0))
    base = X[i] if coord == 0 else Y[i]
    sig, kap = (1, []) if side == 'lo' else (-1, T)
    g0 = sub(add(mul(const(sig), base), kap), [x / 2 for x in Fv])
    W = [-x / 2 for x in Fd]
    Wn, eW = approx(W)
    bF, bFd = absbound(Fv), absbound(Fd)
    w = R[3*i+2]
    K = bF * w**2 / 4 + bFd * w**3 / 12 + eW * w
    return dict(kind='wall', i=i, coord=coord, side=side, s=s, g0=g0, Fv=Fv, Fd=Fd, W=W, Wn=Wn, eW=eW,
                bF=bF, bFd=bFd, K=K, sparse=[(3*i+coord, sig * DA), (3*i+2, Wn)])

def kt_of(K): return -((-K * DK).numerator // (K * DK).denominator) if K else 0

def analyse():
    walls = [wall(i, c, sd, s) for i in range(11) for c in (0, 1) for sd in ('lo', 'hi') for s in SIGNS]
    for w_ in walls: assert sign(w_['g0']) >= 0
    tied_walls = [w_ for w_ in walls if iszero(w_['g0'])]
    contacts, feats = [], {}
    for o, p in itertools.combinations(range(11), 2):
        fl = []
        for own, oth, code0 in ((o, p, 0), (p, o, 4)):
            for m in range(4):
                fl.append((code0 + m, own, oth, m, [pair_corner(own, oth, m, s) for s in SIGNS]))
        best = max(min(sign(c['g0']) for c in f[4]) for f in fl)
        assert best >= 0
        if best == 0:
            contacts.append((o, p)); feats[(o, p)] = fl
    avail, unavail = {}, []
    for pr in contacts:
        avail[pr] = []
        for code, own, oth, m, corners in feats[pr]:
            if min(sign(c['g0']) for c in corners) >= 0:
                avail[pr].append((code, own, oth, m, [c for c in corners if iszero(c['g0'])]))
            else:
                unavail.append((pr, code, own, oth, m, corners))
    return tied_walls, contacts, avail, unavail

def unavail_proof(corners):
    """A corner with g0 + sum |A_k| r_k + K < 0; returns (corner, margin)."""
    best = None
    for c in corners:
        if sign(c['g0']) >= 0: continue
        g0hi = enc(c['g0'])[1]
        lin = sum(abs(F(a, DA)) * R[k] for k, a in c['sparse'])
        # the approximation errors of the linear form are already in K
        m = g0hi + lin + c['K']
        if best is None or m < best[1]: best = (c, m)
    assert best[1] < 0, best[1]
    return best

if __name__ == '__main__':
    tw, contacts, avail, unavail = analyse()
    print('tied walls', len(tw), 'contacts', len(contacts), 'avail', sum(len(v) for v in avail.values()), 'unavail', len(unavail))
    worst = max(unavail_proof(u[5])[1] for u in unavail); print('worst unavailable margin', float(worst))
