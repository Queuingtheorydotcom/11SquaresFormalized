import pickle, itertools
labels,V,D=pickle.load(open('dist.pkl','rb'))
N=len(labels)
diff=lambda a,b: all(a[g]!=b[g] for g in range(4))
BANS={(i,j) for (i,j),v in D.items() if v<1 and diff(labels[i],labels[j])}
M={999:(0,1,2,4,6,7,9,10,12,14,15),1462:(0,1,3,5,6,8,9,11,12,13,14),1659:(0,2,3,4,5,6,7,11,12,13,14)}
ht=lambda J: tuple(sorted(15-j for j in J))
six=sorted(set(M.values())|{ht(J) for J in M.values()})
def compat_masks(bans):
    C=[]
    for r in range(N):
        m=0
        for s in range(N):
            if s!=r and diff(labels[r],labels[s]) and (min(r,s),max(r,s)) not in bans: m|=1<<s
        C.append(m)
    return C
def search(J0,T,C,used=None):
    nodes=0
    dom={o:[r for r in range(N) if labels[r][0]==o and all(labels[r][g] in T[g-1] for g in (1,2,3))] for o in J0}
    def ext(avail,rest):
        nonlocal nodes; nodes+=1
        if not rest: return True
        o=rest[0]
        for r in dom[o]:
            if not (avail>>r)&1: continue
            if used is not None:
                for o2 in rest[1:]:
                    for s in dom[o2]:
                        if (avail>>s)&1 and not (C[r]>>s)&1 and diff(labels[r],labels[s]): used.add((min(r,s),max(r,s)))
            if ext(avail & C[r], rest[1:]): return True
        return False
    return ext((1<<N)-1,list(J0)),nodes
if __name__=='__main__':
    C=compat_masks(BANS)
    tot=0; used=set()
    for J0 in six:
        for T in itertools.product(six,repeat=3):
            res,n=search(J0,T,C,used); tot+=n
            assert not res,(J0,T)
    print('all UNSAT, total nodes',tot,'used bans',len(used))
    C2=compat_masks(used)
    tot2=0
    for J0 in six:
        for T in itertools.product(six,repeat=3):
            res,n=search(J0,T,C2); tot2+=n; assert not res
    print('UNSAT with used bans only; nodes',tot2)
    pickle.dump((six,used),open('fixed_used.pkl','wb'))
