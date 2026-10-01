import itertools, json
from fractions import Fraction as F
from cells import *
from lp1 import solve, CEN
R2=F(6,25)
def verts(C):
    V=[]
    for A,B in itertools.combinations(C,2):
        a1,b1,c1=A;a2,b2,c2=B
        det=a1*b2-a2*b1
        if det==0: continue
        x=(-c1*b2+c2*b1)/det; y=(-a1*c2+a2*c1)/det
        if all(a*x+b*y+c>=0 for (a,b,c) in C) and (x,y) not in V: V.append((x,y))
    # order by angle about centroid
    import math
    mx=sum(float(v[0]) for v in V)/len(V); my=sum(float(v[1]) for v in V)/len(V)
    V.sort(key=lambda v: math.atan2(float(v[1])-my,float(v[0])-mx))
    return V
def rnd(v,d=1000): return (F(round(v[0]*d),d),F(round(v[1]*d),d))
def build(C,cen,depth=0):
    """returns tree: ('leaf', constraint list used) or ('split', (a,b,c), tree_ge, tree_le)"""
    eps,sup=solve(C,cen,R2)
    if eps>1e-7:
        used=sorted({i for s,_ in sup for i in s})
        return ('leaf',eps,sup,C)
    assert depth<6, 'too deep'
    V=verts(C); m=len(V)
    best=None
    for i in range(m):
        for j in range(i+2,m):
            if i==0 and j==m-1: continue
            p1,p2=rnd(V[i]),rnd(V[j])
            a=p2[1]-p1[1]; b=p1[0]-p2[0]; c=-(a*p1[0]+b*p1[1])
            g=[v for v in V if a*v[0]+b*v[1]+c>0]; l=[v for v in V if a*v[0]+b*v[1]+c<0]
            sc=abs(len(g)-len(l))
            if best is None or sc<best[0]: best=(sc,(a,b,c))
    a,b,c=best[1]
    return ('split',(a,b,c),build(C+[(a,b,c)],cen,depth+1),build(C+[(-a,-b,-c)],cen,depth+1))
def count(t): return 1 if t[0]=='leaf' else count(t[2])+count(t[3])
if __name__=='__main__':
    for k in range(16):
        C=[t[2:] for t in cons(k)]
        t=build(C,CEN[k]); print(k,count(t))
