import re
from fractions import Fraction as F
import os
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','lean','Sqpack','S11Opt','Cells.lean')).read()
m=re.search(r'def PU : Fin 16 → ℝ × ℝ := !\[(.*?)\]\n',src,re.S)
nums=re.findall(r'\((\d+) / (\d+) : ℝ\)',m.group(1))
vals=[F(int(a),int(b)) for a,b in nums]
PU=[(vals[2*i],vals[2*i+1]) for i in range(16)]
Ux=F(387708359002281417731,10**20)
def cons(k):
    """linear constraints a.x+b.y+c>=0 for cell k in the centre box"""
    out=[]
    xk,yk=PU[k]
    for j in range(16):
        if j==k: continue
        xj,yj=PU[j]
        # |p-Pk|^2<=|p-Pj|^2  <=> (xj^2+yj^2-xk^2-yk^2) - 2x(xj-xk) - 2y(yj-yk) >=0
        out.append(('v',j,-2*(xj-xk),-2*(yj-yk),xj*xj+yj*yj-xk*xk-yk*yk))
    h=F(1,2)
    out+= [('bx0',0,F(1),F(0),-h),('bx1',0,F(-1),F(0),Ux-h),('by0',0,F(0),F(1),-h),('by1',0,F(0),F(-1),Ux-h)]
    return out
