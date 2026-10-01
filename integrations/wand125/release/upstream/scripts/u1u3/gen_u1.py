from gen import gen_cell, q
from bsp import CEN
HEAD=open('u1_head.lean').read()
TAIL=open('u1_tail.lean').read()
cells="\n\n".join(gen_cell(k) for k in range(16))
cases="\n".join(f"  · exact diam_of_disk (cell_disk_{k} hp hbp) (cell_disk_{k} hq hbq)" for k in range(16))
print(HEAD+cells+"\n\n"+TAIL.replace("@@CASES@@",cases),end="")
