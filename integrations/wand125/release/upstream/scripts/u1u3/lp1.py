import numpy as np
from scipy.optimize import linprog
from fractions import Fraction as F
from cells import *
CEN={0:(F(401,500),F(883,1000)),1:(F(787,500),F(631,1000)),2:(F(2323,1000),F(899,1000)),3:(F(299,100),F(199,250)),4:(F(797,1000),F(413,250)),5:(F(196,125),F(7,5)),6:(F(291,125),F(1697,1000)),7:(F(3063,1000),F(293,200))}
for k in range(8,16):
    x,y=CEN[15-k]; CEN[k]=(Ux-x,Ux-y)
# monomials 1,x,y,x2,xy,y2
def lin(a,b,c): return np.array([c,a,b,0,0,0],dtype=float)
def mul(l1,l2):
    c1,a1,b1=l1[:3];c2,a2,b2=l2[:3]
    return np.array([c1*c2,a1*c2+a2*c1,b1*c2+b2*c1,a1*a2,a1*b2+a2*b1,b1*b2])
def solve(C,cen,r2=F(6,25)):
    L=[lin(float(a),float(b),float(c)) for (a,b,c) in C]
    cols=[];names=[]
    for i in range(len(L)):
        for j in range(i,len(L)):
            cols.append(mul(L[i],L[j]));names.append((i,j))
    for i in range(len(L)): cols.append(L[i]);names.append((i,))
    A=np.array(cols).T
    cx,cy=float(cen[0]),float(cen[1])
    tgt=np.array([float(r2)-cx*cx-cy*cy,2*cx,2*cy,-1,0,-1])
    e0=np.zeros(6);e0[0]=1
    r=linprog(np.r_[np.zeros(A.shape[1]),-1],A_eq=np.hstack([A,e0[:,None]]),b_eq=tgt,bounds=[(0,None)]*A.shape[1]+[(None,None)],method='highs')
    lam=r.x[:-1]
    return r.x[-1],[(names[i],lam[i]) for i in range(len(lam)) if lam[i]>1e-12]
if __name__=='__main__':
    for k in range(16):
        C=[t[2:] for t in cons(k)]
        eps,sup=solve(C,CEN[k]); print(k,round(eps,5),len(sup))
