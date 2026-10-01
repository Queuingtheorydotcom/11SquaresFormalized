"""Emit a whole archived capture node as a chain of `ExtStep`s (untrusted).

    python3 gen_chain.py <node.json> <parent.json> <out dir> <Name> [rows per file]

Writes <out dir>/<Name>/Init.lean (the initial state), and for every step k the
files S<k>D (data), S<k>P (partner covers), S<k>R<g> (row checks) and S<k>
(the step), then <Name>.lean with the composed trace.  The state after a step
is defined from the state before it (`replaceRows`, then `replaceHull`), so the
chain is consistent by definition.
"""
import json, sys, os
from fractions import Fraction as F
from geom import hull, halfplanes, contains, vertices, implies_mu, empty_mu, round_in, round_out, round_core, mink_ok, mink_labels, bary, mink_slack
import os
DIAG = bool(os.environ.get('U5_DIAG'))
from gen_step import OWNER, cs, coreVB, wallB, wall_halves, Region, minkowski_regions, q, qp, half, lst
from gen_node import Node, canon, self_cuts, cut_hs, Keep, Coll, build, tree_lean, cuts_lean, regs_lean, zp

NS = "ElevenSquare.Tasks.T07.Ext"
HDR = ("open ElevenSquare ElevenSquare.Pending ElevenSquare.Tasks.T07 ElevenSquare.Tasks.T07.Ext\n\n"
       "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n")


def row_lean(r):
    lo, hi, hs = r
    return f"{{ lo := {q(lo)}, hi := {q(hi)}, centers := {lst(half(x) for x in hs)} }}"


def live_rows(st):
    """The new rows of a step: rows with a residual, once per reference.  A row
    may appear several times with a `sub_interval`, once for every old row it
    absorbs."""
    if not st['complete']:
        return []
    out, seen = [], set()
    for r in st['rows']:
        key = canon(r['reference'])
        if r['residual_polygons'] and key not in seen:
            seen.add(key)
            out.append(r)
    return out


def in_triangle(tri, p):
    return all(contains(h, p) for h in halfplanes(hull(tri))) if len(hull(tri)) == 3 else False


class Chain:
    def __init__(self, node, parent, name, per):
        self.node, self.name, self.per = node, name, per
        self.N = Node(node, parent)
        self.rows, self.refs = {}, {}
        for c, rs in self.N.cells.items():
            o = OWNER[c]
            self.rows[o] = [self.N.fan_row(c, r) for r in rs]
            self.refs[o] = [canon(r['reference']) for r in rs]
        prior = node['steps'][0]['prior_owned_hulls']
        prior = json.loads(prior) if isinstance(prior, str) else prior
        self.owned = {o: [] for o in range(11)}
        for c, pts in prior.items():
            self.owned[OWNER[int(c)]] = hull([self.N.phys(p) for p in pts])

    def check_owned(self, step):
        prior = step['prior_owned_hulls']
        prior = json.loads(prior) if isinstance(prior, str) else prior
        for c, pts in prior.items():
            o = OWNER[int(c)]
            assert set(hull([self.N.phys(p) for p in pts])) == set(self.owned[o]), f'owned drift at owner {o}'

    def step(self, k, out):
        st = self.node['steps'][k]
        self.check_owned(st)
        N, cell = self.N, st['owner']
        i = OWNER[cell]
        if not st['complete']:
            # an interrupted archive step leaves the state unchanged
            self.emit_skip(k, out)
            print(f"{self.name} step {k}: owner {i} incomplete, state kept", file=sys.stderr)
            return i, True
        owned = self.owned
        live = live_rows(st)
        rs_new = [N.fan_row(cell, r) for r in live]
        new_idx = {canon(r['reference']): m for m, r in enumerate(live)}
        stats = dict(empty=0, forbid=0, keep=0, collide=0, split=0)
        # partner covers
        pcov = {}
        for jc, crow in (st.get('prior_partner_pose_covers') or {}).items():
            j = OWNER[int(jc)]
            by_ref = {}
            for r in crow:
                by_ref.setdefault(canon(r['reference']), []).append(r)
            tab = []
            for m, (lo, hi, R_hs) in enumerate(self.rows[j]):
                pieces = []
                for r in sorted(by_ref.get(self.refs[j][m], []), key=lambda r: F(r['interval'][0])):
                    a, b = map(F, r['interval'])
                    cuts = self_cuts(owned[j], a, b)
                    h = min(sum(cs(a)), sum(cs(b))) / 2
                    poly = R_hs + cut_hs(cuts) + wall_halves(h)
                    V = vertices(poly)
                    if not V:
                        pieces.append(dict(a=a, b=b, cuts=cuts, h=h, core=[], dverts=[], dmus=[empty_mu(poly)]))
                        continue
                    core = round_core([N.phys(v) for v in r['core']], lambda v: coreVB(a, b, v))
                    assert all(coreVB(a, b, v) for v in core)
                    Dv = round_out(V)
                    dmus = [implies_mu(poly, g, V) for g in halfplanes(Dv)]
                    assert all(m_ is not None for m_ in dmus)
                    pieces.append(dict(a=a, b=b, cuts=cuts, h=h, core=core, dverts=Dv, dmus=dmus,
                                       core_exact=hull([N.phys(v) for v in r['core']]), V_exact=V))
                tab.append(pieces)
            pcov[j] = tab
        # sub-rows of the old rows
        by_prior = {}
        for r in st['rows']:
            by_prior.setdefault(canon(r['prior_reference']), []).append(r)
        certs = []
        for m, (lo, hi, row_hs) in enumerate(self.rows[i]):
            subs = []
            for r in sorted(by_prior.get(self.refs[i][m], []), key=lambda r: F(r.get('sub_interval', r['interval'])[0])):
                a, b = map(F, r.get('sub_interval', r['interval']))
                cuts = self_cuts(owned[i], a, b)
                h = min(sum(cs(a)), sum(cs(b))) / 2
                core = hull([N.phys(v) for v in r['core_vertices']])
                assert all(coreVB(a, b, v) for v in core)
                ccore = round_core(core, lambda v: coreVB(a, b, v)) if core else []
                regions, regs = [], []
                for j, K in owned.items():
                    if j != i and K and core:
                        regions += minkowski_regions(j, K, core)
                for g in r.get('collision_regions') or []:
                    verts = round_out([N.phys(p) for p in g['vertices']])
                    jj = OWNER[g['partner']]
                    for ps in (x for row in pcov[jj] for x in row):
                        if ps['dverts'] and not mink_ok(ps['core'], ccore, verts, ps['dverts']):
                            exact = mink_ok(ps['core_exact'], core, [N.phys(p) for p in g['vertices']], ps['V_exact'])
                            if DIAG:
                                Rx = [N.phys(p) for p in g['vertices']]
                                print('DIAG', k, i, jj, ps['a'], ps['b'], 'exact', float(mink_slack(ps['core_exact'], core, Rx, ps['V_exact'])),
                                      'pcore', float(mink_slack(ps['core'], core, Rx, ps['V_exact'])),
                                      'ccore', float(mink_slack(ps['core_exact'], ccore, Rx, ps['V_exact'])),
                                      'reg', float(mink_slack(ps['core_exact'], core, verts, ps['V_exact'])),
                                      'dv', float(mink_slack(ps['core_exact'], core, Rx, ps['dverts'])), flush=True)
                                continue
                            raise AssertionError(f'collision margin lost (exact data {"passes" if exact else "fails"}): '
                                                 f'step {k} owner {i} partner {jj} piece {ps["a"]}..{ps["b"]}')
                    ms = [mink_labels(ps['core'], ccore) if ps['dverts'] else [] for row in pcov[jj] for ps in row]
                    regs.append((jj, verts, ms))
                    regions.append(Coll(len(regs) - 1, verts))
                if r['residual_polygons']:
                    mm = new_idx[canon(r['reference'])]
                    for piece in r['residual_polygons']:
                        regions.append(Keep(mm, halfplanes(hull([N.phys(p) for p in piece]))))
                poly = row_hs + cut_hs(cuts) + wall_halves(h)
                tree = build(poly, regions, [x[2] for x in rs_new], stats)
                subs.append(dict(a=a, b=b, cuts=cuts, h=h, core=core, ccore=ccore, regs=regs, tree=tree))
            certs.append(subs)
        # promotion
        promo = None
        if live:
            kern = [N.phys(p) for p in (json.loads(st['common_owned_kernel'])
                                        if isinstance(st['common_owned_kernel'], str) else st['common_owned_kernel'])]
            prs = []
            for r, (lo, hi, hs) in zip(live, rs_new):
                core = hull([N.phys(v) for v in r['core_vertices']])
                cv = hull([N.phys(p) for poly in r['residual_polygons'] for p in poly])
                mus = [implies_mu(hs, g) for g in halfplanes(cv)]
                assert all(m_ is not None for m_ in mus)
                if not all(ea * kp[0] + eb * kp[1] + max(-ea * c[0] - eb * c[1] for c in cv) <= ec
                           for kp in kern for (ea, eb, ec) in halfplanes(core)):
                    # the exact core of the kernel: every difference of a kernel point and a centre vertex
                    core = hull([(kp[0] - c[0], kp[1] - c[1]) for kp in kern for c in cv])
                    assert all(coreVB(lo, hi, v) for v in core), 'kernel point outside a square'
                for kp in kern:
                    for (ea, eb, ec) in halfplanes(core):
                        assert ea * kp[0] + eb * kp[1] + max(-ea * c[0] - eb * c[1] for c in cv) <= ec, 'kernel point'
                prs.append(dict(core=core, cv=cv, mus=mus))
            g = st['inner_grid_compression']
            g = json.loads(g) if isinstance(g, str) else g
            pts = json.loads(g['vertices']) if isinstance(g['vertices'], str) else g['vertices']
            pts = [N.phys(p) for p in pts]
            vs = hull(owned[i] + pts)
            H0 = hull(owned[i] + kern)
            combs = []
            for v in vs:
                if v in owned[i] or v in kern:
                    combs.append((v, [(v, F(1)), (v, F(0)), (v, F(0))]))
                    continue
                for t in range(1, len(H0) - 1):
                    tri = [H0[0], H0[t], H0[t + 1]]
                    if in_triangle(tri, v):
                        lam = bary(tri)
                        w = [a_ * v[0] + b_ * v[1] + c_ for a_, b_, c_ in lam]
                        assert all(x >= 0 for x in w) and sum(w) == 1
                        combs.append((v, list(zip(tri, w))))
                        break
                else:
                    raise AssertionError('promoted point outside the hull')
            promo = dict(kern=kern, prs=prs, combs=combs, vs=vs)
        print(f"{self.name} step {k}: owner {i} rows {len(self.rows[i])} -> {len(rs_new)}, "
              f"partners { {j: len(t) for j, t in pcov.items()} }, leaves {stats}", file=sys.stderr)
        self.emit(k, i, rs_new, pcov, certs, promo, out)
        # advance the state
        self.rows[i] = rs_new
        self.refs[i] = [canon(r['reference']) for r in live]
        if promo:
            owned[i] = promo['vs']
        return i, bool(live)

    def step_quiet(self, k):
        """Advance the tracked state through step k without emitting certificates."""
        st = self.node['steps'][k]
        self.check_owned(st)
        N, cell = self.N, st['owner']
        i = OWNER[cell]
        if not st['complete']:
            return i, True
        live = live_rows(st)
        self.rows[i] = [N.fan_row(cell, r) for r in live]
        self.refs[i] = [canon(r['reference']) for r in live]
        if live:
            g = st['inner_grid_compression']
            g = json.loads(g) if isinstance(g, str) else g
            pts = json.loads(g['vertices']) if isinstance(g['vertices'], str) else g['vertices']
            self.owned[i] = hull(self.owned[i] + [N.phys(p) for p in pts])
        return i, bool(live)

    def emit(self, k, i, rs_new, pcov, certs, promo, out):
        base = f"{NS}.{self.name}"
        prev = f"{base}.S{k - 1}.next" if k else f"{base}.st0"
        prev_mod = f"{NS}.Gen.{self.name}.S{k - 1}D" if k else f"{NS}.Gen.{self.name}.Init"
        sn = f"{base}.S{k}"
        mod = f"ElevenSquare.Tasks.T07.Ext.Gen.{self.name}"
        # S<k>C holds the certificate data and does not depend on the earlier steps;
        # S<k>D defines the states (prev, mid, next) and imports only S<k-1>D.
        D = ["import ElevenSquare.Tasks.T07.Ext.Promote\n", f"namespace {sn}", HDR,
             f"def rs : List PoseRow := {lst(row_lean(r) for r in rs_new)}\n"]
        for j, tab in pcov.items():
            D.append(f"def pc{j} : List (List PartnerPiece) := " + lst(
                lst(f"⟨{q(ps['a'])}, {q(ps['b'])}, {cuts_lean(ps['cuts'])}, {q(ps['h'])}, "
                    f"{lst(zp(v) for v in ps['core'])}, {lst(zp(v) for v in ps['dverts'])}, "
                    f"{lst(lst(q(x) for x in mu) for mu in ps['dmus'])}⟩" for ps in pieces)
                for pieces in tab) + "\n")
        body = " else ".join(f"if j = {j} then pc{j}" for j in pcov)
        D.append(f"def pcov (j : ℕ) : List (List PartnerPiece) := {body + ' else []' if pcov else '[]'}\n")
        for m, subs in enumerate(certs):
            D.append(f"def cert{m} : List Sub := " + lst(
                f"⟨{q(u['a'])}, {q(u['b'])}, {cuts_lean(u['cuts'])}, {q(u['h'])}, {lst(qp(v) for v in u['core'])}, "
                f"{lst(zp(v) for v in u['ccore'])}, {regs_lean(u['regs'])},\n  {tree_lean(u['tree'])}⟩"
                for u in subs) + "\n")
        D.append(f"def certs : List (List Sub) := {lst(f'cert{m}' for m in range(len(certs)))}\n")
        M = [f"import {mod}.S{k}C\nimport {prev_mod.replace(NS, 'ElevenSquare.Tasks.T07.Ext')}\n",
             f"namespace {sn}", HDR, f"abbrev prev : PoseState := {prev}\n",
             f"def mid : PoseState := replaceRows prev {i} rs\n"]
        if promo:
            D.append(f"def kern : List QPoint := {lst(qp(p) for p in promo['kern'])}\n")
            D.append("def prs : List PRow := " + lst(
                f"⟨{lst(qp(v) for v in pr['core'])}, {lst(qp(v) for v in pr['cv'])}, "
                f"{lst(lst(q(x) for x in mu) for mu in pr['mus'])}⟩" for pr in promo['prs']) + "\n")
            D.append("def combs : List Comb := " + lst(
                f"⟨{qp(v)}, {lst(f'({qp(p)}, {q(w)})' for p, w in ws)}⟩" for v, ws in promo['combs']) + "\n")
            M.append(f"def next : PoseState := replaceHull mid {i} (combs.map Comb.v)\n")
        else:
            M.append("def next : PoseState := mid\n")
        D.append(f"end {sn}\n")
        M.append(f"end {sn}\n")
        d = os.path.join(out, self.name)
        os.makedirs(d, exist_ok=True)
        open(os.path.join(d, f"S{k}C.lean"), "w").write("\n".join(D))
        open(os.path.join(d, f"S{k}D.lean"), "w").write("\n".join(M))
        # partner covers
        P = [f"import {mod}.S{k}D\n", f"namespace {sn}", HDR]
        for j in pcov:
            P.append(f"theorem pc{j}_ok : pcovB prev {j} pc{j} = true := by decide +kernel\n")
        P.append("theorem pcov_ok : ∀ j, pcov j ≠ [] → pcovB prev j (pcov j) = true := by\n  intro j hj")
        for j in pcov:
            P.append(f"  by_cases h{j} : j = {j}\n  · subst h{j}; exact pc{j}_ok")
        P.append(f"  simp [pcov, {', '.join(f'h{j}' for j in pcov)}] at hj\n" if pcov else "  simp [pcov] at hj\n")
        P.append(f"end {sn}\n")
        open(os.path.join(d, f"S{k}P.lean"), "w").write("\n".join(P))
        # rows in groups
        n_rows = len(certs)
        groups = [list(range(a, min(n_rows, a + self.per))) for a in range(0, n_rows, self.per)] or [[]]
        for gi, grp in enumerate(groups):
            R = [f"import {mod}.S{k}D\n", f"namespace {sn}", HDR]
            for n in grp:
                R.append(f"theorem row{n}_ok : rowB prev {i} rs pcov ((prev.rows {i}).getD {n} ⟨0, 0, []⟩) "
                         f"(certs.getD {n} []) = true := by decide +kernel\n")
            R.append(f"end {sn}\n")
            open(os.path.join(d, f"S{k}R{gi}.lean"), "w").write("\n".join(R))
        # the step
        S = ["import Mathlib.Tactic.IntervalCases", f"import {mod}.S{k}P"] + \
            [f"import {mod}.S{k}R{gi}" for gi in range(len(groups))] + ["",
             f"namespace {sn}", HDR,
             f"theorem nrows : (prev.rows {i}).length = {n_rows} := by decide +kernel\n",
             f"theorem step_ok : stepB prev {i} rs pcov certs = true := by",
             f"  refine stepB_of_rows (by rw [nrows]; rfl) (fun n hn => ?_)",
             f"  rw [nrows] at hn"]
        if n_rows:
            S.append("  interval_cases n")
            S += [f"  · exact row{n}_ok" for n in range(n_rows)]
        else:
            S.append("  omega")
        S.append("")
        S.append("theorem prune : ExtStep prev mid := stepB_sound pcov_ok step_ok\n")
        if promo:
            S.append(f"theorem promote_ok : promoteB mid {i} kern prs combs = true := by decide +kernel\n")
            S.append("theorem trace : ExtTrace prev next :=\n"
                     "  ExtTrace.cons prune (ExtTrace.cons (ExtStep.base (promoteB_sound promote_ok)) (ExtTrace.refl _))\n")
        else:
            S.append("theorem trace : ExtTrace prev next := ExtTrace.cons prune (ExtTrace.refl _)\n")
        S.append(f"end {sn}\n")
        open(os.path.join(d, f"S{k}.lean"), "w").write("\n".join(S))

    def emit_skip(self, k, out):
        base = f"{NS}.{self.name}"
        prev = f"{base}.S{k - 1}.next" if k else f"{base}.st0"
        prev_mod = f"{NS}.Gen.{self.name}.S{k - 1}D" if k else f"{NS}.Gen.{self.name}.Init"
        M = [f"import ElevenSquare.Tasks.T07.Ext.Promote\nimport {prev_mod.replace(NS, 'ElevenSquare.Tasks.T07.Ext')}\n",
             f"namespace {base}.S{k}", HDR, f"abbrev prev : PoseState := {prev}\n",
             "def next : PoseState := prev\n", f"end {base}.S{k}\n"]
        S = [f"import ElevenSquare.Tasks.T07.Ext.Gen.{self.name}.S{k}D\n", f"namespace {base}.S{k}", HDR,
             "theorem trace : ExtTrace prev next := ExtTrace.refl _\n", f"end {base}.S{k}\n"]
        d = os.path.join(out, self.name)
        os.makedirs(d, exist_ok=True)
        open(os.path.join(d, f"S{k}D.lean"), "w").write("\n".join(M))
        open(os.path.join(d, f"S{k}.lean"), "w").write("\n".join(S))

    def emit_init(self, out):
        d = os.path.join(out, self.name)
        os.makedirs(d, exist_ok=True)
        L = ["import ElevenSquare.Tasks.T07.Ext.Promote\n", f"namespace {NS}.{self.name}", HDR]
        for o in range(11):
            L.append(f"def rows{o} : List PoseRow := {lst(row_lean(r) for r in self.rows.get(o, []))}\n")
        L.append("def st0 : PoseState where\n  rows := ![" + ", ".join(f"rows{o}" for o in range(11)) +
                 "]\n  owned := ![" + ", ".join(lst(qp(p) for p in self.owned.get(o, [])) for o in range(11)) + "]\n")
        L.append(f"end {NS}.{self.name}\n")
        open(os.path.join(d, "Init.lean"), "w").write("\n".join(L))


def main(node_path, parent_path, out, name, per=40):
    node = json.load(open(node_path))
    parent = json.load(open(parent_path))
    ch = Chain(node, parent, name, int(per))
    ch.emit_init(out)
    last = None
    for k in range(len(node['steps'])):
        last = ch.step(k, out)
    n = len(node['steps'])
    mod = f"ElevenSquare.Tasks.T07.Ext.Gen.{name}"
    base = f"{NS}.{name}"
    T = [f"import {mod}.S{n - 1}\nimport ElevenSquare.Tasks.T07.CaptureTraceCombinators\n", f"namespace {base}", HDR]
    T.append(f"theorem trace : ExtTrace st0 S{n - 1}.next := by")
    expr = f"S{n - 1}.trace"
    for k in range(n - 2, -1, -1):
        expr = f"(ExtTrace.trans S{k}.trace {expr})"
    T.append(f"  exact {expr}\n")
    if node.get('contradiction'):
        i, _ = last
        T.append(f"theorem terminal : Terminal S{n - 1}.next :=\n"
                 f"  terminal_of_empty_owner _ {i} (by simp [S{n - 1}.next, S{n - 1}.mid, replaceRows, S{n - 1}.rs])\n")
    T.append(f"end {base}\n")
    open(os.path.join(out, f"{name}.lean"), "w").write("\n".join(T))


if __name__ == "__main__":
    main(*sys.argv[1:])
