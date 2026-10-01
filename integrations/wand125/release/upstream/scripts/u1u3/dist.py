import pickle, sys
from fractions import Fraction as F
from itertools import combinations
regs=pickle.load(open('regs.pkl','rb'))
labels=sorted(regs); V=[regs[l] for l in labels]
def d2(a,b): return (a[0]-b[0])**2+(a[1]-b[1])**2
N=len(labels)
D={}
for i in range(N):
    for j in range(i+1,N):
        D[(i,j)]=max(d2(p,q) for p in V[i] for q in V[j])
bans={k for k,v in D.items() if v<1}
print('bans',len(bans))
pickle.dump((labels,V,D),open('dist.pkl','wb'))
