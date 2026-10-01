import sys
from fractions import Fraction as F
from cells import *
from bsp import build, CEN
def q(x):
    x=F(x)
    if x.denominator==1: return f"({x.numerator} : ℝ)"
    return f"({x.numerator} / {x.denominator} : ℝ)"
def linexpr(a,b,c):
    return f"{q(c)} + {q(a)} * p.1 + {q(b)} * p.2"
def gen_cell(k):
    C=cons(k)
    names=[]; L=[]
    xk,yk=PU[k]
    L.append(f"lemma cell_disk_{k} {{p : ℝ × ℝ}} (h : InCellU {k} p) (hb : InB p) :")
    cx,cy=CEN[k]
    L.append(f"    (p.1 - {q(cx)}) ^ 2 + (p.2 - {q(cy)}) ^ 2 ≤ 6 / 25 := by")
    L.append(f"  obtain ⟨hx0, hx1, hy0, hy1⟩ := hb")
    L.append(f"  unfold Ux at hx1 hy1")
    tree=build([t[2:] for t in C],CEN[k])
    used=set()
    def walk(t):
        if t[0]=='leaf':
            for s,_ in t[2]: used.update(i for i in s if i<len(C))
        else: walk(t[2]); walk(t[3])
    walk(tree)
    for t,(kind,j,a,b,c) in enumerate(C):
        nm=f"g{t}"; names.append(nm)
        if t not in used: continue
        if kind=='v':
            xj,yj=PU[j]
            L.append(f"  have {nm} := cell_lin h {j} {q(xk)} {q(yk)} {q(xj)} {q(yj)} rfl rfl")
        else:
            L.append(f"  have {nm} : 0 ≤ {linexpr(a,b,c)} := by linarith")
    ncon=len(C)
    def emit(t,ind,extra):
        pad=' '*ind
        if t[0]=='leaf':
            _,eps,sup,Cl=t
            hints=[]
            for s,_ in sup:
                nm=lambda i: names[i] if i<ncon else extra[i-ncon]
                if len(s)==2: hints.append(f"mul_nonneg {nm(s[0])} {nm(s[1])}")
                else: hints.append(nm(s[0]))
            L.append(f"{pad}linarith [{', '.join(hints)}]")
        else:
            _,(a,b,c),tg,tl=t
            nm=f"s{len(extra)}"
            L.append(f"{pad}rcases le_total 0 ({linexpr(a,b,c)}) with {nm} | {nm}")
            L.append(f"{pad}· " + "")
            L[-1]=L[-1].rstrip()
            emit_inline(tg,ind+2,extra+[nm],pad+"· ")
            L.append(f"{pad}· replace {nm} : 0 ≤ {linexpr(-a,-b,-c)} := by linarith")
            emit(tl,ind+2,extra+[nm])
    def emit_inline(t,ind,extra,prefix):
        # replace last line (bullet) with first line of subtree
        L.pop()
        start=len(L)
        emit(t,ind,extra)
        L[start]=prefix+L[start].lstrip()
    emit(tree,2,[])
    return "\n".join(L)
if __name__=='__main__':
    ks=[int(a) for a in sys.argv[1:]] or range(16)
    print("\n\n".join(gen_cell(k) for k in ks))
