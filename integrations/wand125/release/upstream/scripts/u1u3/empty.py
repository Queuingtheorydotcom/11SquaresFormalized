import numpy as np, pickle, itertools
from scipy.optimize import linprog
from geo import *
def tagged_cons(views_labels):
    """list of (tag, (a,b,c)); tag=('box',i) or ('cell',g,l,j) meaning bisector of cell l vs site j in view g"""
    out=[(('box',i),c) for i,c in enumerate(BOX)]
    for g,l in views_labels:
        js=[j for j in range(16) if j!=l]
        for j,c in zip(js,cell_cons(l)):
            out.append((('cell',g,l,j),pull(g,c)))
    return out
def farkas(TC):
    A=np.array([[float(a),float(b)] for _,(a,b,c) in TC]).T  # 2 x n
    cvec=np.array([float(c) for _,(a,b,c) in TC])
    n=len(TC)
    # y>=0, A y = 0, c.y = -1  ; minimize sum y
    Aeq=np.vstack([A,cvec[None,:]]); beq=np.array([0,0,-1.0])
    r=linprog(np.ones(n),A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*n,method='highs')
    if r.status!=0: return None
    return [TC[i][0] for i in range(n) if r.x[i]>1e-12]
if __name__=='__main__':
    P=pickle.load(open('pairs.pkl','rb'))
    cert={}
    for (g,h,a,b),Vv in P.items():
        if Vv: continue
        s=farkas(tagged_cons([(g,a),(h,b)]))
        assert s is not None and len(s)<=3, ((g,h,a,b),s)
        cert[(g,h,a,b)]=s
    print('pair certs',len(cert))
    labels=pickle.load(open('dist.pkl','rb'))[0]
    ne={k for k,v in P.items() if v}
    T296=[t for t in itertools.product(range(16),repeat=4) if all((g,h,t[g],t[h]) in ne for g,h in itertools.combinations(range(4),2))]
    fake=[t for t in T296 if t not in set(labels)]
    fc={}
    for t in fake:
        s=farkas(tagged_cons(list(enumerate(t))))
        assert s is not None and len(s)<=3
        fc[t]=s
    print('fake',len(fake), 'views used', sorted({len({x[1] for x in s if x[0]=='cell'}) for s in fc.values()}))
    pickle.dump((cert,fc,T296),open('empty.pkl','wb'))
