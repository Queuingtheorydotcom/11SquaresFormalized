"""Generate the U4 Lean files: row lemmas, feature lemmas, pair case splits, data, certificates.

Usage: python gen_lean.py <out dir = lean/Sqpack/S11Opt/Split/U4>   (needs numpy, scipy)

Every number the Lean proofs use is derived here in the same way the proofs derive it:
atom enclosures of cA, sA (hIv), polynomial enclosures of the projections Pv, Pd (hIv on the
unreduced polynomial), and interval arithmetic by `linarith` for the rest.
"""
import os, sys, itertools, math
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
import core
from core import DA, DL, DK, DR, RI, R, LO, HI, cA, sA, T, X, Y, TILT, SIGNS
from field import P, add, sub, mul, divmod_, red, const, neg, horner_iv

G30 = 10 ** 30


def fl(x, g=G30):
    return F((x.numerator * g) // x.denominator, g)


def ce(x, g=G30):
    return F(-((-x.numerator * g) // x.denominator), g)


def rq(q):
    q = F(q)
    return f"{q.numerator}" if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def rr(q):
    """A real literal."""
    q = F(q)
    if q.denominator == 1:
        return f"({q.numerator} : ℝ)"
    return f"({q.numerator} / {q.denominator} : ℝ)"


def qlist(p):
    return "[" + ", ".join(rq(c) for c in p) + "]"


def pencl(p):
    if not p:
        return F(0), F(0)
    lo, hi = horner_iv(p, LO, HI)
    return fl(lo), ce(hi)


def ineg(i):
    return (-i[1], -i[0])


def iadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def iscale(c, a):
    return (c * a[0], c * a[1]) if c >= 0 else (c * a[1], c * a[0])


CAI, SAI = pencl(cA), pencl(sA)
# atoms: (lean expression, interval, polynomial)
A_ONE = ("1", (F(1), F(1)), const(1))
A_ZERO = ("0", (F(0), F(0)), [])
A_NONE = ("-1", (F(-1), F(-1)), const(-1))
A_CA = ("cA", CAI, cA)
A_SA = ("sA", SAI, sA)
A_NCA = ("-cA", ineg(CAI), neg(cA))
A_NSA = ("-sA", ineg(SAI), neg(sA))


def aneg(at):
    return {"1": A_NONE, "-1": A_ONE, "0": A_ZERO, "cA": A_NCA, "-cA": A_CA, "sA": A_NSA, "-sA": A_SA}[at[0]]


def trig(tilted, m):
    c0, s0 = (A_CA, A_SA) if tilted else (A_ONE, A_ZERO)
    return [(c0, s0), (aneg(s0), c0), (aneg(c0), aneg(s0)), (s0, aneg(c0))][m]


def trig_diff(tp, to, m):
    if tp == to:
        c0, s0 = A_ONE, A_ZERO
    elif tp:
        c0, s0 = A_CA, A_SA
    else:
        c0, s0 = A_CA, A_NSA
    return [(c0, s0), (s0, aneg(c0)), (aneg(c0), aneg(s0)), (aneg(s0), c0)][m]


def approx(iv):
    """Integer N and error e (multiple of 1/(10 DA)) with the interval inside N/DA ± e."""
    N = round((iv[0] + iv[1]) / 2 * DA)
    e = max(abs(iv[0] - F(N, DA)), abs(iv[1] - F(N, DA)))
    return N, ce(e, 10 * DA)


def absb(iv):
    return ce(max(abs(iv[0]), abs(iv[1])), 10 ** 15)


def kt_of(K):
    return -((-K * DK).numerator // (K * DK).denominator)


ALLDEFS = "cA, sA, TA, " + ", ".join(f"x{i}, y{i}" for i in range(11)) + ", pe, List.foldr, peQ_cons, peQ_nil"
TRIG = "cos_zero, sin_zero, cos_a, sin_a, sub_zero, zero_sub, sub_self, cos_neg, sin_neg, neg_neg"
CORNERS = [".1", ".2.1", ".2.2.1", ".2.2.2"]


def sname(v):
    return "p" if v == 1 else "m"


class Pair:
    """A corner gap of the feature (owner o, other p, quarter turn m) at corner s."""

    def __init__(self, o, p, m, s):
        self.o, self.p, self.m, self.s = o, p, m, s
        s1, s2 = s
        self.C0, self.S0 = trig(TILT[o], m)
        self.cph, self.sph = trig_diff(TILT[p], TILT[o], m)
        Dx, Dy = sub(X[p], X[o]), sub(Y[p], Y[o])
        self.Pv = add(mul(self.C0[2], Dx), mul(self.S0[2], Dy))
        self.Pd = add(mul(neg(self.S0[2]), Dx), mul(self.C0[2], Dy))
        self.PvI, self.PdI = pencl(self.Pv), pencl(self.Pd)
        # z0 = (s1 cph - s2 sph)/2,  zd = (-s1 sph - s2 cph)/2
        self.z0I = iscale(F(1, 2), iadd(iscale(s1, self.cph[1]), iscale(-s2, self.sph[1])))
        self.zdI = iscale(F(1, 2), iadd(iscale(-s1, self.sph[1]), iscale(-s2, self.cph[1])))
        self.GI = iadd(self.PdI, ineg(self.zdI))
        self.Cn, self.eC = approx(self.C0[1])
        self.Sn, self.eS = approx(self.S0[1])
        self.Gn, self.eG = approx(self.GI)
        self.Zn, self.eZ = approx(self.zdI)
        self.bP, self.bPd, self.bz, self.bzd = absb(self.PvI), absb(self.PdI), absb(self.z0I), absb(self.zdI)
        self.Rx = R[3 * o] + R[3 * p]
        self.Ry = R[3 * o + 1] + R[3 * p + 1]
        self.wo, self.wp = R[3 * o + 2], R[3 * p + 2]
        wo, wp = self.wo, self.wp
        self.K = (self.bP * wo ** 2 / 2 + self.bPd * wo ** 3 / 6 + (self.Rx + self.Ry) * wo ** 2 / 2
                  + (self.Rx + self.Ry) * wo + self.bz * (wo + wp) ** 2 / 2 + self.bzd * (wo + wp) ** 3 / 6
                  + self.eC * self.Rx + self.eS * self.Ry + self.eG * wo + self.eZ * wp)
        # exact base gap g0 = Pv + z0 - 1/2 (unreduced polynomial)
        z0p = [x / 2 for x in sub(mul(const(s1), self.cph[2]), mul(const(s2), self.sph[2]))]
        self.g0 = sub(add(self.Pv, z0p), const(F(1, 2)))
        self.g0I = iadd(iadd(self.PvI, self.z0I), (F(-1, 2), F(-1, 2)))
        self.sparse = [(3 * p, self.Cn), (3 * o, -self.Cn), (3 * p + 1, self.Sn), (3 * o + 1, -self.Sn),
                       (3 * o + 2, self.Gn), (3 * p + 2, self.Zn)]
        self.name = f"{o}_{p}_{m}_{sname(s1)}{sname(s2)}"

    def tied(self):
        return red(self.g0) == []

    def setup(self):
        """Lean lines shared by the tied and the unavailable lemma."""
        o, p, m = self.o, self.p, self.m
        s1, s2 = self.s
        al = f"ang {o} + {m} * (π / 2)"
        be = f"ang {p}"
        L = []
        w = L.append
        for k in (3 * o, 3 * o + 1, 3 * o + 2, 3 * p, 3 * p + 1, 3 * p + 2):
            w(f"  have b{k} := H.bd (k := {k}) (by norm_num) (r := {rr(R[k])}) (by rw [show rI.getD {k} 0 = {RI[k]} from rfl]; norm_num [DR])")
        w(f"  have v{3*o} : hvOf c θ {3*o} = (c {o}).1 - (ctr {o}).1 := hv_x c θ {o}")
        w(f"  have v{3*o+1} : hvOf c θ {3*o+1} = (c {o}).2 - (ctr {o}).2 := hv_y c θ {o}")
        w(f"  have v{3*o+2} : hvOf c θ {3*o+2} = θ {o} - ang {o} := hv_t c θ {o}")
        w(f"  have v{3*p} : hvOf c θ {3*p} = (c {p}).1 - (ctr {p}).1 := hv_x c θ {p}")
        w(f"  have v{3*p+1} : hvOf c θ {3*p+1} = (c {p}).2 - (ctr {p}).2 := hv_y c θ {p}")
        w(f"  have v{3*p+2} : hvOf c θ {3*p+2} = θ {p} - ang {p} := hv_t c θ {p}")
        w(f"  have hdx : |((c {p}).1 - (c {o}).1) - ((ctr {p}).1 - (ctr {o}).1)| ≤ τ * {rr(self.Rx)} := by")
        w(f"    rw [show ((c {p}).1 - (c {o}).1) - ((ctr {p}).1 - (ctr {o}).1) = hvOf c θ {3*p} - hvOf c θ {3*o} by rw [v{3*p}, v{3*o}]; ring]")
        w(f"    exact le_trans (abs_sub _ _) (by linarith)")
        w(f"  have hdy : |((c {p}).2 - (c {o}).2) - ((ctr {p}).2 - (ctr {o}).2)| ≤ τ * {rr(self.Ry)} := by")
        w(f"    rw [show ((c {p}).2 - (c {o}).2) - ((ctr {p}).2 - (ctr {o}).2) = hvOf c θ {3*p+1} - hvOf c θ {3*o+1} by rw [v{3*p+1}, v{3*o+1}]; ring]")
        w(f"    exact le_trans (abs_sub _ _) (by linarith)")
        w(f"  have hx : |θ {o} - ang {o}| ≤ τ * {rr(self.wo)} := by rw [← v{3*o+2}]; exact b{3*o+2}")
        w(f"  have hy : |θ {p} - ang {p}| ≤ τ * {rr(self.wp)} := by rw [← v{3*p+2}]; exact b{3*p+2}")
        w(f"  have hca : cos ({al}) = {self.C0[0]} := by rw [cos_q{m}, ang_{o}]; simp [{TRIG}]")
        w(f"  have hsa : sin ({al}) = {self.S0[0]} := by rw [sin_q{m}, ang_{o}]; simp [{TRIG}]")
        w(f"  have hcd : cos ({be} - ({al})) = {self.cph[0]} := by rw [cos_dq{m}, ang_{o}, ang_{p}]; simp [{TRIG}]")
        w(f"  have hsd : sin ({be} - ({al})) = {self.sph[0]} := by rw [sin_dq{m}, ang_{o}, ang_{p}]; simp [{TRIG}]")
        pvx = f"cos ({al}) * ((ctr {p}).1 - (ctr {o}).1) + sin ({al}) * ((ctr {p}).2 - (ctr {o}).2)"
        pdx = f"-sin ({al}) * ((ctr {p}).1 - (ctr {o}).1) + cos ({al}) * ((ctr {p}).2 - (ctr {o}).2)"
        for nm, ex, poly, iv in (("hPv", pvx, self.Pv, self.PvI), ("hPd", pdx, self.Pd, self.PdI)):
            w(f"  have {nm} : {rr(iv[0])} ≤ {ex} ∧ {ex} ≤ {rr(iv[1])} := by")
            w(f"    have e : {ex} = peQ {qlist(poly)} u₀ := by")
            w(f"      rw [hca, hsa, ctr_{o}, ctr_{p}]; simp only [{ALLDEFS}]; push_cast; ring")
            w(f"    rw [e]; have := encl {qlist(poly)} ({rq(iv[0])}) ({rq(iv[1])}) (by decide +kernel)")
            w(f"    push_cast at this; exact this")
        zd = f"(-({s1} : ℝ) * sin ({be} - ({al})) - ({s2} : ℝ) * cos ({be} - ({al}))) / 2"
        z0 = f"(({s1} : ℝ) * cos ({be} - ({al})) - ({s2} : ℝ) * sin ({be} - ({al}))) / 2"
        at = "[hcAe.1, hcAe.2, hsAe.1, hsAe.2]"
        ab = "rw [abs_le]; constructor <;> linarith"
        C, S, G, Z = (rr(F(n, DA)) for n in (self.Cn, self.Sn, self.Gn, self.Zn))
        key = (f"  have key := pgap_approx (co := ctr {o}) (cp := ctr {p}) (co' := c {o}) (cp' := c {p})\n"
               f"    (α := {al}) (β := {be}) (x := θ {o} - ang {o}) (y := θ {p} - ang {p})\n"
               f"    (s1 := ({s1} : ℝ)) (s2 := ({s2} : ℝ)) (C := {C}) (S := {S}) (G := {G}) (Z := {Z})\n"
               f"    (eC := {rr(self.eC)}) (eS := {rr(self.eS)}) (eG := {rr(self.eG)}) (eZ := {rr(self.eZ)})\n"
               f"    (bP := {rr(self.bP)}) (bPd := {rr(self.bPd)}) (bz := {rr(self.bz)}) (bzd := {rr(self.bzd)})\n"
               f"    H.τ0 H.τ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hdx hdy hx hy\n"
               f"    (by rw [hca]; {ab} {at}) (by rw [hsa]; {ab} {at})\n"
               f"    (by rw [hcd, hsd]; {ab} [hPd.1, hPd.2, hcAe.1, hcAe.2, hsAe.1, hsAe.2])\n"
               f"    (by rw [hcd, hsd]; {ab} {at})\n"
               f"    (by {ab} [hPv.1, hPv.2]) (by {ab} [hPd.1, hPd.2])\n"
               f"    (by rw [hcd, hsd]; {ab} {at}) (by rw [hcd, hsd]; {ab} {at})")
        w(key)
        w(f"  rw [show ({al}) + (θ {o} - ang {o}) = θ {o} + {m} * (π / 2) by ring,")
        w(f"    show {be} + (θ {p} - ang {p}) = θ {p} by ring] at key")
        return L

    def lemma_tied(self, rid, kt):
        o, p, m = self.o, self.p, self.m
        s1, s2 = self.s
        al = f"ang {o} + {m} * (π / 2)"
        q, r = divmod_(self.g0, P)
        assert r == []
        L = [f"lemma row_{self.name} {{c : Fin 11 → ℝ × ℝ}} {{θ : Fin 11 → ℝ}} {{τ : ℝ}} (H : Pert c θ τ)",
             f"    (hF : 0 ≤ pgap (c {o}) (c {p}) (θ {o} + {m} * (π / 2)) (θ {p}) ({s1} : ℝ) ({s2} : ℝ)) :",
             f"    RowOK (rowsS.getD {rid} []) (kts.getD {rid} 0) (hvOf c θ) τ := by"]
        L += self.setup()
        w = L.append
        w(f"  have hbase : pgap (ctr {o}) (ctr {p}) ({al}) (ang {p}) ({s1} : ℝ) ({s2} : ℝ) = 0 := by")
        w(f"    unfold pgap; rw [hca, hsa, hcd, hsd, ctr_{o}, ctr_{p}]; simp only [{ALLDEFS}]")
        w(f"    linear_combination {pexpr(q)} * P_u₀'")
        w(f"  rw [hbase] at key")
        w(f"  have hK : τ * {rr(self.K)} ≤ τ * ({kt} / 100000000000000000000 : ℝ) :=")
        w(f"    mul_le_mul_of_nonneg_left (by norm_num) H.τ0")
        w(f"  have hk := (abs_le.mp key).2")
        w(f"  rw [row_{rid}, kt_{rid}]")
        w(f"  unfold RowOK spVal")
        w(f"  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, v{3*o}, v{3*o+1}, v{3*o+2}, v{3*p}, v{3*p+1}, v{3*p+2}]")
        w(f"  norm_num [DA, DK]")
        w(f"  linarith")
        return "\n".join(L) + "\n"

    def lemma_unavail(self, code, corner_idx):
        """The feature (o, p, m) is impossible: this corner stays negative."""
        o, p, m = self.o, self.p, self.m
        s1, s2 = self.s
        al = f"ang {o} + {m} * (π / 2)"
        M = (abs(F(self.Cn, DA)) * self.Rx + abs(F(self.Sn, DA)) * self.Ry + abs(F(self.Gn, DA)) * self.wo
             + abs(F(self.Zn, DA)) * self.wp + self.K)
        assert self.g0I[1] + M < 0, (self.name, float(self.g0I[1] + M))
        L = [f"lemma featU_{o}_{p}_{m} {{c : Fin 11 → ℝ × ℝ}} {{θ : Fin 11 → ℝ}} {{τ : ℝ}} (H : Pert c θ τ) :",
             f"    ¬ Feat (c {o}) (c {p}) (θ {o} + {m} * (π / 2)) (θ {p}) := by",
             f"  intro hFeat",
             f"  have hF := hFeat{CORNERS[corner_idx]}"]
        L += self.setup()
        w = L.append
        w(f"  have hg0 : pgap (ctr {o}) (ctr {p}) ({al}) (ang {p}) ({s1} : ℝ) ({s2} : ℝ) ≤ {rr(self.g0I[1])} := by")
        w(f"    unfold pgap; rw [hcd, hsd]; linarith [hPv.1, hPv.2, hcAe.1, hcAe.2, hsAe.1, hsAe.2]")
        C, S, G, Z = (rr(F(n, DA)) for n in (self.Cn, self.Sn, self.Gn, self.Zn))
        w(f"  have hl := lin4_le (C := {C}) (S := {S}) (G := {G}) (Z := {Z}) hdx hdy hx hy")
        w(f"  have hk := (abs_le.mp key).2")
        w(f"  have hM : τ * (|{C}| * {rr(self.Rx)} + |{S}| * {rr(self.Ry)} + |{G}| * {rr(self.wo)} + |{Z}| * {rr(self.wp)}) + τ * {rr(self.K)}")
        w(f"      ≤ {rr(M)} := by")
        w(f"    rw [← mul_add]; exact le_trans (mul_le_of_le_one_left (by norm_num) H.τ1) (by norm_num)")
        w(f"  linarith")
        return "\n".join(L) + "\n"


class Wall:
    def __init__(self, i, coord, side, s):
        self.i, self.coord, self.side, self.s = i, coord, side, s
        s1, s2 = s
        c0, s0 = trig(TILT[i], 0)
        self.c0, self.s0 = c0, s0
        self.FI = iadd(iscale(s1, c0[1]), iscale(s2, s0[1]))
        self.FdI = iadd(iscale(-s1, s0[1]), iscale(s2, c0[1]))
        self.WI = iscale(F(-1, 2), self.FdI)
        self.Wn, self.eW = approx(self.WI)
        self.bF, self.bFd = absb(self.FI), absb(self.FdI)
        self.w = R[3 * i + 2]
        self.K = self.bF * self.w ** 2 / 4 + self.bFd * self.w ** 3 / 12 + self.eW * self.w
        base = X[i] if coord == 0 else Y[i]
        self.sig, kap = (1, []) if side == 'lo' else (-1, T)
        Fv = add(mul(const(s1), c0[2]), mul(const(s2), s0[2]))
        self.g0 = sub(add(mul(const(self.sig), base), kap), [x / 2 for x in Fv])
        self.sparse = [(3 * i + coord, self.sig * DA), (3 * i + 2, self.Wn)]
        self.name = f"{i}_{'xy'[coord]}{side}_{sname(s1)}{sname(s2)}"

    def tied(self):
        return red(self.g0) == []

    def lemma(self, rid, kt):
        i, coord = self.i, self.coord
        s1, s2 = self.s
        cq = f"(c {i}).{coord + 1}"
        cq0 = f"(ctr {i}).{coord + 1}"
        sig = "1" if self.sig == 1 else "(-1)"
        kap = "0" if self.side == 'lo' else "T"
        part = {('0', 'lo'): ".1", ('0', 'hi'): ".2.1", ('1', 'lo'): ".2.2.1", ('1', 'hi'): ".2.2.2"}[(str(coord), self.side)]
        q, r = divmod_(self.g0, P)
        assert r == []
        at = "[hcAe.1, hcAe.2, hsAe.1, hsAe.2]"
        ab = "rw [abs_le]; constructor <;> linarith"
        v = 3 * i + coord
        L = [f"lemma wrow_{self.name} {{c : Fin 11 → ℝ × ℝ}} {{θ : Fin 11 → ℝ}} {{τ : ℝ}} (H : Pert c θ τ)",
             f"    (hA : Adm T (c {i}) (θ {i})) :",
             f"    RowOK (rowsS.getD {rid} []) (kts.getD {rid} 0) (hvOf c θ) τ := by",
             f"  have hF := (wgap_nonneg hA (s1 := ({s1} : ℝ)) (s2 := ({s2} : ℝ)) (by norm_num) (by norm_num)){part}",
             f"  have b{3*i+2} := H.bd (k := {3*i+2}) (by norm_num) (r := {rr(R[3*i+2])}) (by rw [show rI.getD {3*i+2} 0 = {RI[3*i+2]} from rfl]; norm_num [DR])",
             f"  have v{v} : hvOf c θ {v} = {cq} - {cq0} := {'hv_x' if coord == 0 else 'hv_y'} c θ {i}",
             f"  have v{3*i+2} : hvOf c θ {3*i+2} = θ {i} - ang {i} := hv_t c θ {i}",
             f"  have hx : |θ {i} - ang {i}| ≤ τ * {rr(self.w)} := by rw [← v{3*i+2}]; exact b{3*i+2}",
             f"  have hc : cos (ang {i}) = {self.c0[0]} := by rw [ang_{i}]; simp [{TRIG}]",
             f"  have hs : sin (ang {i}) = {self.s0[0]} := by rw [ang_{i}]; simp [{TRIG}]",
             f"  have key := wgap_approx (cq := {cq0}) (cq' := {cq}) (σ := {sig}) (κ := {kap}) (θ := ang {i})",
             f"    (x := θ {i} - ang {i}) (s1 := ({s1} : ℝ)) (s2 := ({s2} : ℝ)) (W := {rr(F(self.Wn, DA))})",
             f"    (eW := {rr(self.eW)}) (bF := {rr(self.bF)}) (bF' := {rr(self.bFd)})",
             f"    H.τ0 H.τ1 (by norm_num) hx",
             f"    (by rw [hc, hs]; {ab} {at}) (by rw [hc, hs]; {ab} {at}) (by rw [hc, hs]; {ab} {at})",
             f"  rw [show ang {i} + (θ {i} - ang {i}) = θ {i} by ring] at key",
             f"  have hbase : wgap {cq0} {sig} {kap} (ang {i}) ({s1} : ℝ) ({s2} : ℝ) = 0 := by",
             f"    unfold wgap; rw [hc, hs, ctr_{i}]; simp only [T_eq, {ALLDEFS}]",
             f"    linear_combination {pexpr(q)} * P_u₀'",
             f"  rw [hbase] at key",
             f"  have hK : τ * {rr(self.K)} ≤ τ * ({kt} / 100000000000000000000 : ℝ) :=",
             f"    mul_le_mul_of_nonneg_left (by norm_num) H.τ0",
             f"  have hk := (abs_le.mp key).2",
             f"  rw [row_{rid}, kt_{rid}]",
             f"  unfold RowOK spVal",
             f"  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, v{v}, v{3*i+2}]",
             f"  norm_num [DA, DK]",
             f"  linarith"]
        return "\n".join(L) + "\n"


def pexpr(p, x="u₀"):
    if not p:
        return "0"
    terms = []
    for i, c in enumerate(p):
        if c == 0:
            continue
        terms.append(rr(c) + ("" if i == 0 else (f" * {x}" if i == 1 else f" * {x} ^ {i}")))
    return "(" + " + ".join(terms) + ")"


def analyse():
    walls = [Wall(i, c, sd, s) for i in range(11) for c in (0, 1) for sd in ('lo', 'hi') for s in SIGNS]
    tied_walls = [w_ for w_ in walls if w_.tied()]
    contacts, feats = [], {}
    for o, p in itertools.combinations(range(11), 2):
        fl_ = []
        for own, oth, code0 in ((o, p, 0), (p, o, 4)):
            for m in range(4):
                fl_.append((code0 + m, own, oth, m, [Pair(own, oth, m, s) for s in SIGNS]))
        signs = []
        for f_ in fl_:
            signs.append(min(core.sign(c.g0) for c in f_[4]))
        if max(signs) == 0:
            contacts.append((o, p))
            feats[(o, p)] = [(f_, sg) for f_, sg in zip(fl_, signs)]
    return tied_walls, contacts, feats


HEADER = """import Sqpack.S11Opt.Split.U4.{imp}

/-! Generated by `scripts/u4/gen_lean.py`.  Do not edit by hand. -/

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open Real SquarePacking.S11Opt

namespace SquarePacking.S11Opt.Split.U4
"""
FOOTER = "\nend SquarePacking.S11Opt.Split.U4\n"


def main(out):
    tied_walls, contacts, feats = analyse()
    # row catalogue
    rows, index = [], {}

    def rid(obj):
        key = tuple(sorted(obj.sparse))
        kt = kt_of(obj.K)
        if key not in index:
            index[key] = len(rows)
            rows.append(dict(sparse=list(key), kt=kt))
        rows[index[key]]['kt'] = max(rows[index[key]]['kt'], kt)
        return index[key]

    wall_ids = [rid(w_) for w_ in tied_walls]
    feat_rows, feat_info = [], []
    for pr in contacts:
        fr, fi = [], []
        for (code, own, oth, m, corners), sg in feats[pr]:
            if sg == 0:
                ids = []
                used = []
                for ci, c in enumerate(corners):
                    if c.tied():
                        r_ = rid(c)
                        if r_ not in ids:
                            ids.append(r_)
                            used.append((ci, c, r_))
                fr.append(ids)
                fi.append((code, own, oth, m, used))
            else:
                fi.append((code, own, oth, m, None))
        feat_rows.append(fr)
        feat_info.append(fi)
    for r_ in rows:
        r_['dense'] = [0] * 33
        for k, a in r_['sparse']:
            r_['dense'][k] += a
    print(f"rows {len(rows)} walls {len(wall_ids)}", file=sys.stderr)

    # branches and certificates
    def sections(L):
        # the order of Lean's `List.sections`: the first coordinate varies fastest
        if not L:
            return [[]]
        return [[a] + t for t in sections(L[1:]) for a in L[0]]
    sels = sections([list(range(len(f))) for f in feat_rows])
    branches, sel_branch = {}, []
    for s in sels:
        ids = set(wall_ids)
        for q, t in enumerate(s):
            ids |= set(feat_rows[q][t])
        key = tuple(sorted(ids))
        if key not in branches:
            branches[key] = len(branches)
        sel_branch.append(branches[key])
    blist = sorted(branches, key=branches.get)
    certs, worst = [], F(0)
    for b in blist:
        A = np.array([[a / DA for a in rows[i]['dense']] for i in b])
        K = np.array([rows[i]['kt'] / DK for i in b])
        cb = []
        for t in range(66):
            j, sg = t // 2, (1 if t % 2 else -1)
            e = np.zeros(33)
            e[j] = sg
            res = linprog(K, A_eq=A.T, b_eq=e, bounds=(0, None), method='highs')
            assert res.status == 0
            lam = [max(0, int(round(x * DL))) for x in res.x]
            S = [0] * 33
            for l_, i in zip(lam, b):
                for k, a in enumerate(rows[i]['dense']):
                    S[k] += l_ * a
            tt = sg * DA * DL
            lhs = sum(abs(S[k] - (tt if k == j else 0)) * RI[k] for k in range(33)) * DK \
                + sum(l_ * rows[i]['kt'] for l_, i in zip(lam, b)) * DA * DR
            rhs = RI[j] * DA * DL * DK
            assert lhs < rhs
            worst = max(worst, F(lhs, rhs))
            cb.append(lam)
        certs.append(cb)
    print(f"selections {len(sels)} branches {len(blist)} worst {float(worst)}", file=sys.stderr)

    # --- Atoms.lean: enclosures of cA, sA
    A = [HEADER.format(imp="Basis")]
    for nm, poly, iv in (("cA", cA, CAI), ("sA", sA, SAI)):
        A.append(f"lemma h{nm}e : {rr(iv[0])} ≤ {nm} ∧ {nm} ≤ {rr(iv[1])} := by")
        A.append(f"  have e : {nm} = peQ {qlist(poly)} u₀ := by simp only [{nm}, pe, List.foldr, peQ_cons, peQ_nil]; push_cast; ring")
        A.append(f"  rw [e]; have := encl {qlist(poly)} ({rq(iv[0])}) ({rq(iv[1])}) (by decide +kernel)")
        A.append(f"  push_cast at this; exact this\n")
    # data
    A.append("/-- The rows (sparse). -/")
    A.append("def rowsS : List (List (ℕ × ℤ)) := [" + ",\n  ".join(
        "[" + ", ".join(f"({k}, {a})" for k, a in r_['sparse']) + "]" for r_ in rows) + "]\n")
    A.append("/-- The rows (dense). -/")
    A.append("def rowsD : List (List ℤ) := [" + ",\n  ".join(
        "[" + ", ".join(str(a) for a in r_['dense']) + "]" for r_ in rows) + "]\n")
    A.append("def kts : List ℕ := [" + ", ".join(str(r_['kt']) for r_ in rows) + "]\n")
    for i, r_ in enumerate(rows):
        A.append(f"lemma row_{i} : rowsS.getD {i} [] = [" + ", ".join(f"({k}, {a})" for k, a in r_['sparse']) + "] := rfl")
        A.append(f"lemma kt_{i} : kts.getD {i} 0 = {r_['kt']} := rfl")
    A.append("")
    A.append("def wallIds : List ℕ := [" + ", ".join(map(str, wall_ids)) + "]\n")
    A.append("def featRows : List (List (List ℕ)) := [" + ",\n  ".join(
        "[" + ", ".join("[" + ", ".join(map(str, ids)) + "]" for ids in fr) + "]" for fr in feat_rows) + "]\n")
    A.append("def branches : List (List ℕ) := [" + ",\n  ".join(
        "[" + ", ".join(map(str, b)) + "]" for b in blist) + "]\n")
    A.append("def selBranch : List ℕ := [" + ", ".join(map(str, sel_branch)) + "]\n")
    A.append("theorem rowsD_eq : rowsD = rowsS.map densify := by decide +kernel\n")
    A.append("theorem rowsS_lt : ∀ sp ∈ rowsS, ∀ e ∈ sp, e.1 < 33 := by decide +kernel\n")
    A.append("theorem selOK_true : selOK featRows wallIds branches selBranch = true := by decide +kernel\n")
    open(os.path.join(out, "Data.lean"), "w").write("\n".join(A) + FOOTER)

    # --- Rows: tied corners, unavailable features, walls (split in files)
    lemmas_tied, lemmas_unav, lemmas_wall = [], [], []
    for pr, fi in zip(contacts, feat_info):
        for (code, own, oth, m, used), ((_, _, _, _, corners), sg) in zip(fi, feats[pr]):
            if used is None:
                # pick the corner with the most negative bound
                best = None
                for ci, c in enumerate(corners):
                    if core.sign(c.g0) >= 0:
                        continue
                    Mv = (c.g0I[1] + abs(F(c.Cn, DA)) * c.Rx + abs(F(c.Sn, DA)) * c.Ry
                          + abs(F(c.Gn, DA)) * c.wo + abs(F(c.Zn, DA)) * c.wp + c.K)
                    if best is None or Mv < best[0]:
                        best = (Mv, ci, c)
                lemmas_unav.append(best[2].lemma_unavail(code, best[1]))
            else:
                for ci, c, r_ in used:
                    lemmas_tied.append(c.lemma_tied(r_, rows[r_]['kt']))
    for w_, r_ in zip(tied_walls, wall_ids):
        lemmas_wall.append(w_.lemma(r_, rows[r_]['kt']))
    groups = [("RowsT", lemmas_tied), ("RowsW", lemmas_wall)]
    nU = 4
    for g in range(nU):
        groups.append((f"RowsU{g}", lemmas_unav[g::nU]))
    for nm, ls in groups:
        open(os.path.join(out, nm + ".lean"), "w").write(HEADER.format(imp="Data") + "\n" + "\n".join(ls) + FOOTER)
    print(f"tied {len(lemmas_tied)} walls {len(lemmas_wall)} unavailable {len(lemmas_unav)}", file=sys.stderr)

    # --- Pairs.lean: the case split of every contacting pair
    PL = [HEADER.format(imp="RowsT").replace("import Sqpack.S11Opt.Split.U4.RowsT",
          "\n".join(f"import Sqpack.S11Opt.Split.U4.{nm}" for nm, _ in groups))]
    for q, (pr, fi) in enumerate(zip(contacts, feat_info)):
        i, j = pr
        t = 0
        for code, own, oth, m, used in fi:
            if used is None:
                continue
            PL.append(f"lemma featA_{own}_{oth}_{m} {{c : Fin 11 → ℝ × ℝ}} {{θ : Fin 11 → ℝ}} {{τ : ℝ}} (H : Pert c θ τ)")
            PL.append(f"    (hF : Feat (c {own}) (c {oth}) (θ {own} + {m} * (π / 2)) (θ {oth})) :")
            PL.append(f"    ∀ id ∈ (featRows.getD {q} []).getD {t} [], RowOK (rowsS.getD id []) (kts.getD id 0) (hvOf c θ) τ := by")
            ids = [r_ for _, _, r_ in used]
            PL.append(f"  intro id hid")
            PL.append(f"  rw [show (featRows.getD {q} []).getD {t} [] = [{', '.join(map(str, ids))}] from rfl] at hid")
            PL.append(f"  simp only [List.mem_cons, List.not_mem_nil, or_false] at hid")
            PL.append(f"  rcases hid with " + " | ".join("rfl" for _ in ids))
            for ci, c, r_ in used:
                PL.append(f"  · exact row_{c.name} H hF{CORNERS[ci]}")
            PL.append("")
            t += 1
        PL.append(f"lemma pair_{q} {{c : Fin 11 → ℝ × ℝ}} {{θ : Fin 11 → ℝ}} {{τ : ℝ}} (H : Pert c θ τ)")
        PL.append(f"    (hd : Disjoint (sqInt (c {i}) (θ {i}) 1) (sqInt (c {j}) (θ {j}) 1)) :")
        PL.append(f"    ∃ t < (featRows.getD {q} []).length, ∀ id ∈ (featRows.getD {q} []).getD t [],")
        PL.append(f"      RowOK (rowsS.getD id []) (kts.getD id 0) (hvOf c θ) τ := by")
        PL.append(f"  obtain ⟨k, hk | hk⟩ := sat_necessary hd")
        for side, (a, b) in enumerate(((i, j), (j, i))):
            PL.append(f"  · have h4 := feat_mod4 k hk")
            PL.append(f"    rcases mod4_cases k with e | e | e | e <;> rw [e] at h4")
            t = 0
            tmap = {}
            for code, own, oth, m, used in fi:
                if used is not None:
                    tmap[code] = t
                    t += 1
            for m in range(4):
                code = 4 * side + m
                if code in tmap:
                    PL.append(f"    · exact ⟨{tmap[code]}, by decide, featA_{a}_{b}_{m} H h4⟩")
                else:
                    PL.append(f"    · exact absurd h4 (featU_{a}_{b}_{m} H)")
        PL.append("")
    PL.append(f"theorem pairs_all {{c : Fin 11 → ℝ × ℝ}} {{θ : Fin 11 → ℝ}} {{τ : ℝ}} (H : Pert c θ τ)")
    PL.append(f"    (hd : ∀ i j : Fin 11, i ≠ j → Disjoint (sqInt (c i) (θ i) 1) (sqInt (c j) (θ j) 1)) :")
    PL.append(f"    ∀ q < featRows.length, ∃ t < (featRows.getD q []).length, ∀ id ∈ (featRows.getD q []).getD t [],")
    PL.append(f"      RowOK (rowsS.getD id []) (kts.getD id 0) (hvOf c θ) τ := by")
    PL.append(f"  intro q hq")
    PL.append(f"  have hq' : q < {len(contacts)} := hq")
    PL.append(f"  interval_cases q")
    for q, (i, j) in enumerate(contacts):
        PL.append(f"  · exact pair_{q} H (hd {i} {j} (by decide))")
    PL.append("")
    PL.append(f"theorem walls_all {{c : Fin 11 → ℝ × ℝ}} {{θ : Fin 11 → ℝ}} {{τ : ℝ}} (H : Pert c θ τ)")
    PL.append(f"    (hA : ∀ i : Fin 11, Adm T (c i) (θ i)) :")
    PL.append(f"    ∀ id ∈ wallIds, RowOK (rowsS.getD id []) (kts.getD id 0) (hvOf c θ) τ := by")
    PL.append(f"  intro id hid")
    PL.append(f"  simp only [wallIds, List.mem_cons, List.not_mem_nil, or_false] at hid")
    PL.append(f"  rcases hid with " + " | ".join("rfl" for _ in wall_ids))
    for w_ in tied_walls:
        PL.append(f"  · exact wrow_{w_.name} H (hA {w_.i})")
    open(os.path.join(out, "Pairs.lean"), "w").write("\n".join(PL) + "\n" + FOOTER)

    # --- certificates: one definition and one kernel check per branch, 8 files
    NG = 8
    per = (len(blist) + NG - 1) // NG
    for g in range(NG):
        lo_, hi_ = g * per, min(len(blist), (g + 1) * per)
        C = [HEADER.format(imp="Data")]
        for bi in range(lo_, hi_):
            C.append(f"def cb{bi} : List (List ℕ) := [" + ",\n  ".join(
                "[" + ", ".join(map(str, lam)) + "]" for lam in certs[bi]) + "]\n")
            C.append(f"theorem cb{bi}_ok : branchOK rowsD kts rI (branches.getD {bi} []) cb{bi} = true := by\n"
                     f"  decide +kernel\n")
        open(os.path.join(out, f"Cert{g}.lean"), "w").write("\n".join(C) + FOOTER)
    K = ["\n".join(f"import Sqpack.S11Opt.Split.U4.Cert{g}" for g in range(NG)),
         "", "/-! Generated by `scripts/u4/gen_lean.py`.  Do not edit by hand. -/", "",
         "namespace SquarePacking.S11Opt.Split.U4", "",
         "/-- The certificates of every branch. -/",
         "def certList : List (List (List ℕ)) := [" + ", ".join(f"cb{bi}" for bi in range(len(blist))) + "]", "",
         "theorem all_branches :",
         "    ∀ bi < branches.length, branchOK rowsD kts rI (branches.getD bi []) (certList.getD bi []) = true := by",
         "  intro bi hbi",
         f"  have hlen : branches.length = {len(blist)} := rfl",
         "  rw [hlen] at hbi",
         "  interval_cases bi",
         ] + [f"  · exact cb{bi}_ok" for bi in range(len(blist))] + ["", "end SquarePacking.S11Opt.Split.U4", ""]
    open(os.path.join(out, "Certs.lean"), "w").write("\n".join(K))
    print(f"certificate files {NG}, {per} branches each", file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1])
