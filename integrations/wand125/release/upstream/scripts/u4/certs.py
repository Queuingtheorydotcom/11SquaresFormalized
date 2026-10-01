"""Row catalogue, branches and dual certificates for U4 (needs numpy, scipy)."""
import itertools, json, sys, pickle
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
import core
from core import DA, DL, DK, DR, RI, kt_of

def catalogue():
    tw, contacts, avail, unavail = core.analyse()
    rows, index = [], {}
    def rid(q):
        key = tuple(sorted(q['sparse']))
        kt = kt_of(q['K'])
        if key not in index:
            index[key] = len(rows); rows.append(dict(sparse=list(key), kt=kt, srcs=[]))
        r = rows[index[key]]; r['kt'] = max(r['kt'], kt); r['srcs'].append(q)
        return index[key]
    wall_ids = sorted(set(rid(w) for w in tw))
    feat = []   # per contact pair: list of (code, own, oth, m, [row ids])
    for pr in contacts:
        feat.append([(code, own, oth, m, sorted(set(rid(c) for c in cs))) for code, own, oth, m, cs in avail[pr]])
    return rows, wall_ids, contacts, feat, unavail

def dense(sp):
    v = [0] * 33
    for k, a in sp: v[k] += a
    return v

def cert_ok(rows, b, j, sg, lam):
    S = [0] * 33
    for l, i in zip(lam, b):
        for k, a in enumerate(rows[i]['dense']): S[k] += l * a
    S[j] -= sg * DA * DL
    lhs = sum(abs(s) * r for s, r in zip(S, RI)) * DK + sum(l * rows[i]['kt'] for l, i in zip(lam, b)) * DA * DR
    rhs = RI[j] * DA * DL * DK
    return lhs < rhs, F(lhs, rhs)

def main(out):
    rows, wall_ids, contacts, feat, unavail = catalogue()
    for r in rows: r['dense'] = dense(r['sparse'])
    sels = list(itertools.product(*[range(len(f)) for f in feat]))
    branches, sel_branch = {}, []
    for s in sels:
        ids = set(wall_ids)
        for q, t in enumerate(s): ids |= set(feat[q][t][4])
        key = tuple(sorted(ids))
        if key not in branches: branches[key] = len(branches)
        sel_branch.append(branches[key])
    blist = sorted(branches, key=branches.get)
    print('rows', len(rows), 'walls', len(wall_ids), 'selections', len(sels), 'branches', len(blist),
          'rows/branch', sorted(set(map(len, blist))), file=sys.stderr)
    certs, worst = [], F(0)
    for bi, b in enumerate(blist):
        A = np.array([[a / DA for a in rows[i]['dense']] for i in b])
        K = np.array([rows[i]['kt'] / DK for i in b])
        cb = []
        for t in range(66):
            j, sg = t // 2, (1 if t % 2 else -1)
            e = np.zeros(33); e[j] = sg
            res = linprog(K, A_eq=A.T, b_eq=e, bounds=(0, None), method='highs')
            assert res.status == 0, (bi, j, sg)
            lam = [max(0, int(round(x * DL))) for x in res.x]
            ok, ratio = cert_ok(rows, b, j, sg, lam)
            assert ok, (bi, j, sg, float(ratio))
            worst = max(worst, ratio)
            cb.append(lam)
        certs.append(cb)
    print('worst ratio', float(worst), file=sys.stderr)
    pickle.dump(dict(rows=rows, wall_ids=wall_ids, contacts=contacts, feat=feat, unavail=unavail,
                     sels=sels, sel_branch=sel_branch, branches=blist, certs=certs), open(out, 'wb'))

if __name__ == '__main__':
    main(sys.argv[1])
