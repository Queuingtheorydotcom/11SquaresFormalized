import numpy as np, pickle
from scipy.optimize import linprog
from fractions import Fraction as F
from geo import *
def facets(ls, V):
    """indices of region constraints (list from region_cons) tight on the region: tight at >=2 vertices, or all tight ones for a point"""
    C=region_cons(ls)
    out=[]; seen=set()
    for i,(a,b,c) in enumerate(C):
        tight=[v for v in V if a*v[0]+b*v[1]+c==0]
        if (len(V)>1 and len(tight)>=2) or (len(V)==1 and tight):
            # dedupe parallel identical constraint
            key=None
            g=max(abs(a),abs(b))
            key=(a/g,b/g,c/g)
            if key in seen: continue
            seen.add(key); out.append(i)
    return C,out
mons=[(0,0,0,0)]+[tuple(int(i==j) for i in range(4)) for j in range(4)]
mons+= [tuple((i==a)+(i==b) for i in range(4)) for a in range(4) for b in range(a,4)]
idx={m:i for i,m in enumerate(mons)}
def lin(a,b,c,w):
    v=np.zeros(len(mons)); v[0]=float(c)
    e=[0]*4;e[2*w]=1;v[idx[tuple(e)]]+=float(a)
    e=[0]*4;e[2*w+1]=1;v[idx[tuple(e)]]+=float(b)
    return v
def mul(u,v):
    r=np.zeros(len(mons))
    for i,m1 in enumerate(mons):
        if u[i]==0: continue
        for j,m2 in enumerate(mons):
            if v[j]==0: continue
            m=tuple(x+y for x,y in zip(m1,m2))
            if sum(m)<=2: r[idx[m]]+=u[i]*v[j]
    return r
TGT=np.zeros(len(mons)); TGT[0]=1
for w in range(2): pass
# 1 - (x-u)^2 - (y-v)^2
TGT[idx[(2,0,0,0)]]=-1;TGT[idx[(0,0,2,0)]]=-1;TGT[idx[(1,0,1,0)]]=2
TGT[idx[(0,2,0,0)]]=-1;TGT[idx[(0,0,0,2)]]=-1;TGT[idx[(0,1,0,1)]]=2
def solve(Cp,Cq):
    P=[lin(a,b,c,0) for a,b,c in Cp]; Q=[lin(a,b,c,1) for a,b,c in Cq]
    cols=[];names=[]
    for i in range(len(P)):
        for j in range(len(Q)): cols.append(mul(P[i],Q[j]));names.append(('pq',i,j))
    for i in range(len(P)):
        for j in range(i,len(P)): cols.append(mul(P[i],P[j]));names.append(('pp',i,j))
    for i in range(len(Q)):
        for j in range(i,len(Q)): cols.append(mul(Q[i],Q[j]));names.append(('qq',i,j))
    for i in range(len(P)): cols.append(P[i]);names.append(('p',i))
    for j in range(len(Q)): cols.append(Q[j]);names.append(('q',j))
    A=np.array(cols).T
    e0=np.zeros(len(mons));e0[0]=1
    r=linprog(np.r_[np.zeros(A.shape[1]),-1],A_eq=np.hstack([A,e0[:,None]]),b_eq=TGT,bounds=[(0,None)]*A.shape[1]+[(None,1)],method='highs')
    if r.status!=0: return -1,[]
    lam=r.x[:-1]
    return r.x[-1],[(names[i],lam[i]) for i in range(len(lam)) if lam[i]>1e-12]
