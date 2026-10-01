from geo import *
import pickle
regs={():None}
stage=[]
for g in range(4):
    new={}
    for ls in regs:
        for l in range(16):
            V=vertices(region_cons(ls+(l,)))
            if V: new[ls+(l,)]=V
    regs=new; stage.append(len(regs))
print(stage)
from collections import Counter
print(Counter(len(v) for v in regs.values()))
pickle.dump(regs,open('regs.pkl','wb'))
