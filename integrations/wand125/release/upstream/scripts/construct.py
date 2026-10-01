"""Trump's 11-square packing in Q(u0), transcribed from the author's
recovered-checkpoint/research/jlevy/packing/cases/trump11/packing.py (jlevy/squares c55726e).
Returns centres (x, y) and angle tag (0 or 'a') for each square, all as reduced elements."""
from fractions import Fraction as F
from field import add, sub, mul, inv, red, const, neg

U = [F(0), F(1)]


def div(a, b):
    return red(mul(a, inv(b)))


def build():
    u = U
    one = const(1)
    opu2 = add(one, mul(u, u))
    c = div(sub(one, mul(u, u)), opu2)
    s = div(mul(const(2), u), opu2)
    assert red(sub(add(mul(c, c), mul(s, s)), one)) == []
    T = div(add(mul(const(6), u), const(4)), sub(add(one, mul(const(2), u)), mul(u, u)))
    K = const
    r1 = sub(one, red(mul(sub(T, K(3)), c)))
    u1 = div(sub(red(mul(add(one, r1), c)), one), s)
    v1 = sub(c, s)
    v2 = sub(sub(div(sub(T, one), s), r1), red(mul(add(K(3), u1), div(c, s))))
    x0 = sub(add(one, div(K(2), c)), red(mul(sub(T, K(2)), div(s, c))))

    def axis(x, y):
        return (add(x, K(F(1, 2))), add(y, K(F(1, 2)))), 0

    def tilted(ox, oy):
        # centre of the unit square with lower-left (ox, oy - r1) in block coords, mapped by
        # translate(1,1) . rotate(a)
        px = add(ox, K(F(1, 2)))
        py = sub(add(oy, K(F(1, 2))), r1)
        X = add(one, red(sub(mul(c, px), mul(s, py))))
        Y = add(one, red(add(mul(s, px), mul(c, py))))
        return (X, Y), 'a'

    Z = []
    sq = [
        axis(Z, Z),
        axis(sub(T, one), Z),
        axis(x0, sub(T, one)),
        axis(Z, sub(T, one)),
        axis(one, sub(T, one)),
        axis(Z, sub(T, K(2))),
        tilted(Z, Z),
        tilted(u1, neg(one)),
        tilted(one, v1),
        tilted(add(u1, one), sub(v1, one)),
        tilted(add(u1, K(2)), neg(v2)),
    ]
    return dict(c=c, s=s, T=T, sq=sq)
