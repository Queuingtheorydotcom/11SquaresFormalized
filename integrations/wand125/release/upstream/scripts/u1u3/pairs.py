from geo import *
import pickle, itertools
# pairwise view intersections: views g<h, labels a,b
P={}
for g,h in itertools.combinations(range(4),2):
    for a in range(16):
        for b in range(16):
            C=list(BOX)+[pull(g,c) for c in cell_cons(a)]+[pull(h,c) for c in cell_cons(b)]
            V=vertices(C)
            P[(g,h,a,b)]=V
pickle.dump(P,open('pairs.pkl','wb'))
ne={k for k,v in P.items() if v}
print('nonempty pairs',len(ne),'of',len(P))
cnt=0
for t in itertools.product(range(16),repeat=4):
    if all((g,h,t[g],t[h]) in ne for g,h in itertools.combinations(range(4),2)): cnt+=1
print('pairwise-consistent 4-tuples',cnt)
