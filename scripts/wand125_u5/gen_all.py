"""Drive the phase-2 chain and the capture tree step by step, in parallel (untrusted).

    python3 gen_all.py states <json dir> <work dir> <out dir>
        Replays every node without certificates (cheap) and saves the state
        before every step as <work dir>/<Name>_<k>.pkl, plus the node files
        (Init.lean, <Name>.lean) and the list of jobs <work dir>/jobs.txt.
    python3 gen_all.py step <json dir> <work dir> <out dir> <Name> <k>
        Emits the certificates of one step from its saved state.
    python3 gen_all.py near <repo root> <work dir> <out dir>
        Emits NearConn.lean from the final near state.

Every step depends only on the state before it, so the jobs can run in any
order, e.g. `xargs -P 30` over jobs.txt.  The emitted files are the same as a
sequential run of gen_p2.py and gen_tree.py with U5_P2STATE.
"""
import json, os, pickle, sys
from fractions import Fraction as F
from gen_chain import Chain, HDR, NS
from gen_node import Node, canon
from gen_tree import TREE, LEAN_CUT, apply_cut, lean_value, root_state
from gen_p2 import build_steps, seed_polygon, physical_site, ROLE_CELL

PER = 40
_P2_CACHE = {}


def p2_node(jdir):
    if 'node' not in _P2_CACHE:
        p2 = json.load(open(os.path.join(jdir, "p2.json")))
        seed = json.load(open(os.path.join(jdir, "seed.json")))
        B = F(json.load(open(os.path.join(jdir, "root240.json")))['B'])
        _P2_CACHE['node'] = {'B': str(B), 'constraints': [], 'steps': build_steps(p2, seed, B)}
    return _P2_CACHE['node']


def load_node(jdir, name):
    if name == "P2":
        return p2_node(jdir)
    fn = next(fn for nm, fn, _, _ in TREE if nm == name)
    return json.load(open(os.path.join(jdir, fn)))


def chain(node, name, state):
    ch = Chain.__new__(Chain)
    ch.node, ch.name, ch.per = node, name, PER
    ch.N = Node(node, {'final_state': {'cells': {}}})
    ch.rows, ch.refs, ch.owned = state
    return ch


def save(path, obj):
    with open(path, 'wb') as f:
        pickle.dump(obj, f)


def load(path):
    with open(path, 'rb') as f:
        return pickle.load(f)


def write(path, lines):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, "w").write("\n".join(lines))


def final_file(out, name, n, terminal_owner):
    mod = f"ElevenSquare.Tasks.T07.Ext.Gen.{name}"
    base = f"{NS}.{name}"
    # every step's trace: the step modules do not import each other
    T = ["\n".join(f"import {mod}.S{k}" for k in range(n)) + "\nimport ElevenSquare.Tasks.T07.CaptureTraceCombinators\n",
         f"namespace {base}", HDR, f"def final : PoseState := S{n - 1}.next\n",
         "theorem trace : ExtTrace st0 final := by"]
    expr = f"S{n - 1}.trace"
    for k in range(n - 2, -1, -1):
        expr = f"(ExtTrace.trans S{k}.trace {expr})"
    T.append(f"  exact {expr}\n")
    if terminal_owner is not None:
        i = terminal_owner
        T.append(f"theorem terminal : Terminal final :=\n"
                 f"  terminal_of_empty_owner _ {i} (by simp [final, S{n - 1}.next, S{n - 1}.mid, replaceRows, S{n - 1}.rs])\n")
    T.append(f"end {base}\n")
    write(os.path.join(out, f"{name}.lean"), T)


def replay(ch, node, name, work, jobs):
    n = len(node['steps'])
    last = None
    for k in range(n):
        save(os.path.join(work, f"{name}_{k}.pkl"), (ch.rows, ch.refs, ch.owned))
        jobs.append(f"{name} {k}")
        last = ch.step_quiet(k)
    print(f"== {name}: {n} steps", file=sys.stderr, flush=True)
    return n, last


def states(jdir, work, out):
    os.makedirs(work, exist_ok=True)
    jobs = []
    # phase 2 from the closed-cell seed
    node = p2_node(jdir)
    st = ({o: [(F(0), F(1), seed_polygon(ROLE_CELL[o]))] for o in range(11)},
          {o: [canon({"kind": "seed"})] for o in range(11)},
          {o: [physical_site(ROLE_CELL[o])] for o in range(11)})
    ch = chain(node, "P2", st)
    write(os.path.join(out, "P2", "Init.lean"),
          ["import ElevenSquare.Tasks.T07.Ext.Promote\nimport ElevenSquare.Tasks.T07.ShortcutSiteCore\n"
           "import ElevenSquare.Tasks.T07.RoleAssignmentFinite\n", f"namespace {NS}.P2", HDR,
           "def st0 : PoseState := siteSeedFor roleCell\n", f"end {NS}.P2\n"])
    n, _ = replay(ch, node, "P2", work, jobs)
    final_file(out, "P2", n, None)
    finals = {"P2": (ch.rows, ch.refs, ch.owned)}
    steps_of = {"P2": n}
    # the capture tree
    for name, fn, parent, cut in TREE:
        node = json.load(open(os.path.join(jdir, fn)))
        if parent is None:
            rows, refs, owned = root_state(json.load(open(os.path.join(jdir, "p2.json"))), node['steps'][0], F(node['B']))
            prows, prefs, powned = finals["P2"]
            assert all(prows[o] == rows[o] for o in range(11)), 'phase-2 rows differ from the root rows'
            assert all(prefs[o] == refs[o] for o in range(11)), 'phase-2 references differ'
            assert all(set(powned[o]) == set(owned[o]) for o in range(11)), 'phase-2 hulls differ'
            st = (rows, refs, powned)
            np_ = steps_of["P2"]
            init = [f"import ElevenSquare.Tasks.T07.Ext.Gen.P2.S{np_ - 1}D\n", f"namespace {NS}.{name}", HDR,
                    f"def st0 : PoseState := {NS}.P2.S{np_ - 1}.next\n", f"end {NS}.{name}\n"]
        else:
            prows, prefs, powned = finals[parent]
            rows = {o: list(v) for o, v in prows.items()}
            refs = {o: list(v) for o, v in prefs.items()}
            owned = {o: list(v) for o, v in powned.items()}
            # the parent's last state module, not its proofs
            np_ = steps_of[parent]
            expr = f"{NS}.{parent}.S{np_ - 1}.next"
            if cut:
                apply_cut(rows, refs, cut)
                kind, o, v = cut
                expr = f"{LEAN_CUT[kind]} {expr} {o} {lean_value(v)}"
            st = (rows, refs, owned)
            init = [f"import ElevenSquare.Tasks.T07.Ext.Gen.{parent}.S{np_ - 1}D\nimport ElevenSquare.Tasks.T07.Ext.Compose\n",
                    f"namespace {NS}.{name}", HDR, f"def st0 : PoseState := {expr}\n", f"end {NS}.{name}\n"]
        write(os.path.join(out, name, "Init.lean"), init)
        ch = chain(node, name, st)
        n, last = replay(ch, node, name, work, jobs)
        final_file(out, name, n, last[0] if node.get('contradiction') else None)
        finals[name] = (ch.rows, ch.refs, ch.owned)
        steps_of[name] = n
        save(os.path.join(work, f"{name}_final.pkl"), finals[name])
    open(os.path.join(work, "jobs.txt"), "w").write("\n".join(jobs) + "\n")
    print(f"{len(jobs)} jobs", file=sys.stderr)


def step(jdir, work, out, name, k):
    k = int(k)
    node = load_node(jdir, name)
    ch = chain(node, name, load(os.path.join(work, f"{name}_{k}.pkl")))
    ch.step(k, out)


def near(root, work, out):
    import gen_near
    gen_near.main(root, os.path.join(work, "Near_final.pkl"), out)


if __name__ == "__main__":
    mode, *args = sys.argv[1:]
    {"states": states, "step": step, "near": near}[mode](*args)
