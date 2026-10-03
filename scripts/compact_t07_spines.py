#!/usr/bin/env python3
"""One-time exact CTree spine refactor of the imported dac90e2f checkpoint.

This source transformer is not a Lean acceptance test; the checked-in source
already contains its output. Do not rerun it on this checkpoint.
"""
from pathlib import Path
import re, hashlib, json, sys, time
ROOT=Path(__file__).resolve().parents[1]
GEN=ROOT/'ElevenSquare/Tasks/T07/Ext/Gen'
BEGIN=re.compile(r'\((\.(?:split|empty|keep|forbidHull|forbid|collide|left|right)\b|CTreeChain\.build\b)')
PARENS=re.compile(r'[()]')
WS=re.compile(r'\s+')
class Node:
 def __init__(self, start, kind):self.start=start;self.kind=kind;self.children=[];self.end=None

def parse(text):
 nodes={m.start():Node(m.start(),m.group(1)) for m in BEGIN.finditer(text)}
 stack=[];active=[];roots=[]
 for m in PARENS.finditer(text):
  pos=m.start()
  if m.group()=='(':
   stack.append(pos)
   if pos in nodes:
    n=nodes[pos]
    if active:active[-1].children.append(n)
    else:roots.append(n)
    active.append(n)
  else:
   begin=stack.pop()
   if begin in nodes:
    n=active.pop();assert n.start==begin;n.end=pos+1
 assert not stack and not active
 return roots

def normalized(text):return WS.sub('',text)
def canonical(n,t):
 if n.kind=='.split':
  assert len(n.children)==2
  a,b=n.children; plane=t[n.start+len('(.split'):a.start]
  return '(.split'+normalized(plane)+canonical(a,t)+canonical(b,t)+')'
 if n.kind=='CTreeChain.build':
  assert n.children
  cuts=n.children[:-1]; ans=canonical(n.children[-1],t)
  for c in reversed(cuts):
   assert c.kind in ('.left','.right') and len(c.children)==1
   child=c.children[0]; plane=t[c.start+len('('+c.kind):child.start]
   side=canonical(child,t)
   ans='(.split'+normalized(plane)+(ans+side if c.kind=='.left' else side+ans)+')'
  return ans
 assert n.kind not in ('.left','.right') and not n.children
 return normalized(t[n.start:n.end])

def render(n,t,stats):
 if n.kind!='.split':return t[n.start:n.end]
 assert len(n.children)==2
 current=n; cuts=[]
 while current.kind=='.split':
  a,b=current.children
  if a.kind=='.split' and b.kind=='.split':break
  plane=t[current.start+len('(.split'):a.start].strip()
  if a.kind=='.split':cuts.append(('.left',plane,b));current=a
  else:cuts.append(('.right',plane,a));current=b
 if not cuts:
  a,b=n.children; plane=t[n.start+len('(.split'):a.start].strip()
  return '(.split '+plane+'\n    '+render(a,t,stats)+'\n    '+render(b,t,stats)+')'
 stats['cuts_factored']+=len(cuts);stats['spines']+=1
 rows=[f'({direction} {plane} {render(side,t,stats)})' for direction,plane,side in cuts]
 return '(CTreeChain.build ['+',\n    '.join(rows)+']\n    '+render(current,t,stats)+')'

def replace_roots(text,roots,fn):
 pieces=[];start=0
 for n in roots:pieces.extend([text[start:n.start],fn(n)]);start=n.end
 pieces.append(text[start:]);return ''.join(pieces)

stats={'files_changed':0,'cuts_factored':0,'spines':0,'trees_roundtripped':0,'before_lines':0,'after_lines':0,'before_bytes':0,'after_bytes':0}
files=[];start=time.time()
for p in sorted(GEN.rglob('*.lean')):
 if not re.search(r'C\d+$',p.stem):continue
 old=p.read_text();rs=parse(old)
 if not any(n.kind=='.split' for n in rs):continue
 new=replace_roots(old,rs,lambda n:render(n,old,stats))
 if new==old:continue
 rs2=parse(new); assert len(rs)==len(rs2),(p,'root count')
 h=hashlib.sha256()
 for a,b in zip(rs,rs2):
  ca,cb=canonical(a,old),canonical(b,new);assert ca==cb,(p,a.start,'roundtrip')
  h.update(ca.encode());h.update(b'\n');stats['trees_roundtripped']+=1
 skeleton=lambda t,rr:replace_roots(t,rr,lambda n:'CERTIFICATE_TREE')
 assert skeleton(old,rs)==skeleton(new,rs2),(p,'outside tree')
 assert 'import ElevenSquare.Tasks.T07.Ext.Promote' in new
 new=new.replace('import ElevenSquare.Tasks.T07.Ext.Promote','import ElevenSquare.Tasks.T07.Ext.CTreeChain',1)
 stats['files_changed']+=1;stats['before_lines']+=len(old.splitlines());stats['after_lines']+=len(new.splitlines());stats['before_bytes']+=len(old.encode());stats['after_bytes']+=len(new.encode())
 files.append({'path':str(p.relative_to(ROOT)),'tree_token_sha256':h.hexdigest(),'old_sha256':hashlib.sha256(old.encode()).hexdigest(),'new_sha256':hashlib.sha256(new.encode()).hexdigest()})
 p.write_text(new)
 if stats['files_changed']%100==0:print(json.dumps({'progress':stats['files_changed'],'elapsed':round(time.time()-start,1),'saved_lines':stats['before_lines']-stats['after_lines']}),flush=True)
report={'method':'Exact reconstruction of original CTree constructor trees from oriented cut spines; numeric witnesses, tree order, and all non-tree source bytes unchanged except import','stats':stats,'files':files}
out=ROOT/'.verification/t07-spine-source-roundtrip.json';out.parent.mkdir(exist_ok=True);out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(stats,indent=2));print('source-only elapsed',round(time.time()-start,1))
