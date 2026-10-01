from fixed import *
six,used=pickle.load(open('fixed_used.pkl','rb'))
def unsat(b):
    C=compat_masks(b)
    for J0 in six:
        for T in itertools.product(six,repeat=3):
            if search(J0,T,C)[0]: return False
    return True
cur=set(used)
for b in sorted(used,key=lambda b:-D[b]):
    t=cur-{b}
    if unsat(t): cur=t
print('greedy',len(cur),flush=True)
C=compat_masks(cur); tot=sum(search(J0,T,C)[1] for J0 in six for T in itertools.product(six,repeat=3))
print('nodes',tot)
pickle.dump(cur,open('greedy.pkl','wb'))
