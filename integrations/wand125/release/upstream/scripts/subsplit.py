"""Finish missing parts of a psearch (field 25, cell 10, depth 8) by splitting each missing part `extra` more levels."""
import os, pickle, sys
from multiprocessing import Pool
import field_all as A

idx, k, depth, extra = 25, 10, 8, 4
C = A.CACHE
have = set(os.listdir(C))
miss = [(p, b) for p, b in A.boxes_at(depth)
        if f"part-{idx:02d}-{k}-{depth}-{''.join(map(str, p))}.pkl" not in have]
jobs = []
for p, b in miss:
    subs = [((), b)]
    for _ in range(extra):
        nxt = []
        for q, bb in subs:
            _, b1, b2 = A.split_box(bb)
            nxt += [(q + (0,), b1), (q + (1,), b2)]
        subs = nxt
    jobs += [(idx, k, depth + extra, p + q, bb) for q, bb in subs]
print(len(miss), 'missing parts ->', len(jobs), 'sub-parts', flush=True)
with Pool(int(os.environ.get('N11_PROCS', '12'))) as pool:
    for r in pool.imap_unordered(A.search_part, jobs):
        print(*r, flush=True)
for p, b in miss:
    def rec(q, bb):
        if len(q) == extra:
            return pickle.load(open(f"{C}/part-{idx:02d}-{k}-{depth + extra}-{''.join(map(str, p + q))}.pkl", 'rb'))['tree']
        ax, b1, b2 = A.split_box(bb)
        return (ax, rec(q + (0,), b1), rec(q + (1,), b2))
    t = rec((), b)
    pickle.dump(dict(tree=t, leaves=None, kinds=None),
                open(f"{C}/part-{idx:02d}-{k}-{depth}-{''.join(map(str, p))}.pkl", 'wb'))
    print('assembled part', p, flush=True)
A.assemble(idx, k, depth)
print('assembled cell', idx, k, flush=True)
