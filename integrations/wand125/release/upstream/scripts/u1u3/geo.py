from cells import PU, Ux
from fractions import Fraction as F
from itertools import combinations
h=F(1,2)
def cross(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def hull(points):
    points=sorted(set(points))
    if len(points)<3:return points
    lo=[];hi=[]
    for p in points:
        while len(lo)>1 and cross(lo[-2],lo[-1],p)<=0:lo.pop()
        lo.append(p)
    for p in reversed(points):
        while len(hi)>1 and cross(hi[-2],hi[-1],p)<=0:hi.pop()
        hi.append(p)
    return lo[:-1]+hi[:-1]
def cell_cons(k):
    """list of (a,b,c): a x + b y + c >= 0, unit coords, incl. box"""
    xk,yk=PU[k];out=[]
    for j in range(16):
        if j==k: continue
        xj,yj=PU[j]
        out.append((-2*(xj-xk),-2*(yj-yk),xj*xj+yj*yj-xk*xk-yk*yk))
    return out
BOX=[(F(1),F(0),-h),(F(-1),F(0),Ux-h),(F(0),F(1),-h),(F(0),F(-1),Ux-h)]
# views on unit coords: g0 id, g1 (Ux-x,y), g2 (Ux-y,x), g3 (y,x)
def view(g,p):
    x,y=p
    return [(x,y),(Ux-x,y),(Ux-y,x),(y,x)][g]
def pull(g,con):
    """constraint on g(p) -> constraint on p"""
    a,b,c=con
    # g(p)=(X,Y) affine in p; a X + b Y + c
    if g==0: return (a,b,c)
    if g==1: return (-a,b,c+a*Ux)          # X=Ux-x,Y=y
    if g==2: return (b,-a,c+a*Ux)          # X=Ux-y,Y=x : a(Ux-y)+b x
    if g==3: return (b,a,c)                # X=y,Y=x
def vertices(C):
    V=[]
    for (a1,b1,c1),(a2,b2,c2) in combinations(C,2):
        det=a1*b2-a2*b1
        if det==0: continue
        x=(-c1*b2+c2*b1)/det; y=(-a1*c2+a2*c1)/det
        if all(a*x+b*y+c>=0 for a,b,c in C): V.append((x,y))
    return hull(V)
def region_cons(ls):
    C=list(BOX)
    for g,l in enumerate(ls):
        C+= [pull(g,c) for c in cell_cons(l)]
    return C
