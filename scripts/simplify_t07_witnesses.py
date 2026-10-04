#!/usr/bin/env python3
"""Replace exact two-dimensional witness vectors by their supporting facets.

This untrusted source transformer retains the ordinary CTree checker. It checks
that every reconstructed Fraction is exactly the original value before writing
anything. Source, output, context-file and helper hashes make its receipt bound
to concrete files. This is structural preservation, not Lean acceptance.

Start with a small pilot:
  python3 scripts/simplify_t07_witnesses.py --stage P2/S137 --part 0 --write
The default is a read-only proposal. The P2 state reconstruction follows the
actual replaceRows/replaceHull declarations; unsupported states are rejected.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import re
import time
import subprocess
from collections import Counter

ROOT = Path(__file__).resolve().parents[1]
GEN = ROOT / 'ElevenSquare/Tasks/T07/Ext/Gen'
HELPER = ROOT / 'ElevenSquare/Tasks/T07/Ext/CompactWitness.lean'
NUMBER = re.compile(r'-?\d+(?:/\d+)?')
WORD = re.compile(r'[A-Za-z_][A-Za-z_0-9.]*')
SPACE = re.compile(r'\s*')

@dataclass
class Expr:
    kind: str
    args: list
    value: object
    start: int
    end: int
    source: str
    @property
    def raw(self): return self.source[self.start:self.end]

class Parser:
    def __init__(self, source, pos=0): self.s, self.i = source, pos
    def ws(self): self.i = SPACE.match(self.s, self.i).end()
    def at(self, token): self.ws(); return self.s.startswith(token, self.i)
    def eat(self, token):
        self.ws()
        if not self.s.startswith(token, self.i):
            raise ValueError((self.i, token, self.s[self.i:self.i+70]))
        self.i += len(token)
    def val(self):
        self.ws(); start = self.i; c = self.s[self.i]
        args = []; value = None
        if c in '[⟨{':
            self.i += 1; end = {'[':']','⟨':'⟩','{':'}'}[c]
            names = []
            while not self.at(end):
                if c == '{':
                    name = WORD.match(self.s, self.i)
                    if not name: raise ValueError(self.s[self.i:self.i+70])
                    names.append(name[0]); self.i = name.end(); self.eat(':=')
                args.append(self.val())
                if not self.at(end): self.eat(',')
            self.eat(end); kind = {'[':'list','⟨':'struct','{':'record'}[c]
            value = names if c == '{' else None
        elif c == '(':
            self.i += 1; self.ws()
            if self.at('.'):
                self.i += 1; m = WORD.match(self.s, self.i)
                if not m: raise ValueError(self.s[self.i:self.i+70])
                kind = m[0]; self.i = m.end()
                arity = {'split':3,'keep':2,'forbidHull':3,'forbid':2,
                         'collide':2,'empty':1,'left':2,'right':2}[kind]
                args = [self.val() for _ in range(arity)]
            elif self.at('CTreeChain.build'):
                self.eat('CTreeChain.build'); kind = 'chain'
                args = [self.val(), self.val()]
            else:
                a = self.val()
                if self.at(','):
                    kind = 'tuple'; args = [a]
                    while self.at(','):
                        self.eat(','); args.append(self.val())
                else: kind = 'paren'; args = [a]
            self.eat(')')
        elif self.at('true') or self.at('false'):
            value = self.at('true'); self.i += 4 if value else 5; kind = 'bool'
        else:
            m = NUMBER.match(self.s, self.i)
            if not m: raise ValueError((self.i, self.s[self.i:self.i+70]))
            value = Q(m[0]); self.i = m.end(); kind = 'number'
        return Expr(kind, args, value, start, self.i, self.s)

def datum(expr):
    if expr.kind in ('number','bool'): return expr.value
    if expr.kind == 'paren': return datum(expr.args[0])
    if expr.kind in ('list','struct','record','tuple'): return [datum(a) for a in expr.args]
    raise ValueError(expr.kind)

class Sources:
    def __init__(self): self.texts = {}; self.defs = {}
    def text(self, path):
        path = path.resolve()
        if path not in self.texts: self.texts[path] = path.read_text()
        return self.texts[path]
    def definition(self, path, name):
        key = (path.resolve(), name)
        if key not in self.defs:
            s = self.text(path)
            m = re.search(r'^def '+re.escape(name)+r'\s*:[^\n]*?:=', s, re.M)
            if not m: raise ValueError(f'Missing definition {path}:{name}')
            self.defs[key] = Parser(s, m.end()).val()
        return self.defs[key]

def halfplanes(vertices):
    return [(q[1]-p[1], p[0]-q[0],
             (q[1]-p[1])*p[0]+(p[0]-q[0])*p[1])
            for p,q in zip(vertices, vertices[1:]+vertices[:1])]

def source_state(src, family, stage):
    """Evaluate preceding state declarations, never infer state from filenames alone."""
    if family != 'P2': raise ValueError('Only the P2 state chain is supported yet')
    base = GEN / family
    current = src.text(base / f'S{stage}D.lean')
    match = re.search(r'def mid : PoseState := replaceRows prev (\d+) rs', current)
    if not match: raise ValueError('Unsupported current state declaration')
    expected_current = (f'abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.P2.S{stage-1}.next'
                        if stage else 'abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.P2.st0')
    if expected_current not in current: raise ValueError('Unexpected current predecessor')
    owner = int(match[1]); rows = {}; owned = {}
    for n in range(stage-1, -1, -1):
        state = src.text(base / f'S{n}D.lean')
        expected = (f'abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.P2.S{n-1}.next'
                    if n else 'abbrev prev : PoseState := ElevenSquare.Tasks.T07.Ext.P2.st0')
        if expected not in state: raise ValueError(f'Unexpected predecessor at {n}')
        m = re.search(r'def mid : PoseState := replaceRows prev (\d+) rs', state)
        next_match = re.search(r'^def next : PoseState := (.+)$', state, re.M)
        if not next_match: raise ValueError(f'Missing next state at {n}')
        next_expr = next_match[1]
        if next_expr == 'prev':
            if m: raise ValueError(f'Unexpected unused row update at {n}')
            continue
        if not m: raise ValueError(f'Unsupported row replacement at {n}')
        j = int(m[1]); cp = base / f'S{n}C.lean'
        promoted = next_expr == f'replaceHull mid {j} (combs.map Comb.v)'
        if not promoted and next_expr != 'mid':
            raise ValueError(f'Unsupported next state at {n}')
        if j not in rows: rows[j] = datum(src.definition(cp, 'rs'))
        if j not in owned and promoted:
            owned[j] = [entry[0] for entry in datum(src.definition(cp, 'combs'))]
        if len(rows) == 11 and len(owned) == 11: break
    if owner not in rows: raise ValueError('Input owner still uses unsupported initial seed rows')
    return owner, rows[owner], owned

def rebuild(P, g, support):
    kind, *ix = support
    if kind == 'literal': return ix[0]
    out = [Q(0)] * len(P)
    if kind == 'zero': return out
    if kind == 'one':
        k = ix[0]; h = P[k]
        if h[0] != 0: out[k] = g[0]/h[0]
        elif h[1] != 0: out[k] = g[1]/h[1]
        else: return None
    elif kind == 'two':
        k,l = ix; h,z = P[k],P[l]; det = h[0]*z[1]-h[1]*z[0]
        if det == 0: return None
        out[k] = (g[0]*z[1]-g[1]*z[0])/det
        out[l] = (h[0]*g[1]-h[1]*g[0])/det
    return out

def support_for(P, g, weights, raw, counts):
    ix = [k for k,w in enumerate(weights) if w]
    hint = ('zero',) if not ix else ('one',*ix) if len(ix)==1 else ('two',*ix)
    if len(weights) == len(P) and len(ix) <= 2 and rebuild(P,g,hint) == weights:
        counts['vectors_reconstructed'] += 1; counts[f'support_{len(ix)}'] += 1
        return '.'+hint[0] if not ix else '('+'.'+hint[0]+' '+' '.join(map(str,ix))+')'
    counts['vectors_literal'] += 1
    # Literal fallback means exact identity; no inference or loss of source data.
    assert rebuild(P,g,('literal',weights)) == weights
    return f'(.literal {raw})'

def rewrite_tree(tree, P, rs, owned, core, regs, counts):
    """Prove syntactic data preservation by exact reconstruction at each old leaf."""
    kind, aa = tree.kind, tree.args
    replacements = []
    def use(expr, new): replacements.append((expr.start-tree.start,expr.end-tree.start,new))
    if kind == 'chain':
        cuts = aa[0].args; context = P
        for cut in cuts:
            plane = datum(cut.args[0]); negative = [-v for v in plane]
            side_context = [negative]+context if cut.kind == 'left' else [plane]+context
            use(cut.args[1], rewrite_tree(cut.args[1], side_context, rs, owned, core, regs, counts))
            context = [plane]+context if cut.kind == 'left' else [negative]+context
        use(aa[1], rewrite_tree(aa[1],context,rs,owned,core,regs,counts))
        token = tree.raw.index('CTreeChain.build')
        replacements.append((token,token+len('CTreeChain.build'),'CompactWitness.chain'))
    elif kind == 'split':
        plane=datum(aa[0]); use(aa[1],rewrite_tree(aa[1],[plane]+P,rs,owned,core,regs,counts))
        use(aa[2],rewrite_tree(aa[2],[[-v for v in plane]]+P,rs,owned,core,regs,counts))
        replacements.append((1,1+len('.split'),'CompactWitness.split'))
    elif kind in ('keep','forbidHull','collide'):
        index = int(datum(aa[0])); hints = aa[-1]
        if kind == 'keep':
            if not 0 <= index < len(rs): raise ValueError('Invalid kept-row index')
            goals = rs[index][2]
        elif kind == 'forbidHull':
            if index not in owned:
                counts['leaves_literal_missing_seed'] += 1
                return '(CompactWitness.raw '+tree.raw+')'
            A = owned[index]; corners = datum(aa[1]); vs = []
            for a,b in corners:
                a,b=int(a),int(b)
                if not (0<=a<len(A) and 0<=b<len(core)): raise ValueError('Invalid hull vertex index')
                vs.append((A[a][0]-core[b][0], A[a][1]-core[b][1]))
            goals = halfplanes(vs)
        else:
            if not 0 <= index < len(regs): raise ValueError('Invalid collision-region index')
            grid = Q(10**20)
            goals = halfplanes([(v[0]/grid,v[1]/grid) for v in regs[index][1]])
        if len(hints.args) != len(goals): raise ValueError('Witness/goal length mismatch')
        items = [support_for(P,g,datum(mu),mu.raw,counts) for g,mu in zip(goals,hints.args)]
        use(hints,'['+', '.join(items)+']')
        replacements.append((1,1+len('.'+kind),'CompactWitness.'+kind))
        counts['leaves_reconstructed'] += 1
    elif kind in ('forbid','empty'):
        counts['leaves_literal'] += 1
        return '(CompactWitness.raw '+tree.raw+')'
    else: raise ValueError(f'Unsupported tree form {kind}')
    result = tree.raw
    for start,end,new in sorted(replacements,reverse=True): result=result[:start]+new+result[end:]
    return result

def audit_stage_consumers(src, family, stage, input_count):
    """Verify generated certificate names, arities, order and sole consumer."""
    base = GEN / family
    main_path = base / f'S{stage}.lean'
    main = src.text(main_path)
    match = re.search(r'^def certs : List \(List Sub\) := \[([^\]]*)\]', main, re.M)
    if not match: raise ValueError('Unsupported stage certificate list')
    entries = [v.strip() for v in match[1].split(',') if v.strip()]
    definitions = {}
    shards = list(base.glob(f'S{stage}C[0-9]*.lean'))
    for shard in shards:
        for m in re.finditer(r'^def (cert\d+)(.*?) : List Sub :=', src.text(shard), re.M):
            name, args = m[1], m[2]
            if name in definitions: raise ValueError(f'Duplicate definition {name}')
            if args not in ['', ' (prev : PoseState) (rs : List PoseRow)']:
                raise ValueError(f'Unsupported certificate parameters {name}')
            definitions[name] = bool(args)
    expected = [f'cert{k}'+(' prev rs' if definitions.get(f'cert{k}') else '')
                for k in range(input_count)]
    if entries != expected or set(definitions) != {f'cert{k}' for k in range(input_count)}:
        raise ValueError('Certificate definitions/order/instantiation do not match input rows')
    # No generated certificate may have an unhandled qualified external consumer.
    pattern = rf'\bS{stage}\.cert[0-9]+\b|(?:open|namespace)[^\n]*\b{re.escape(family)}\.S{stage}(?:\s|$)'
    result = subprocess.run(['rg','-l',pattern,'--glob','*.lean','ElevenSquare','Sqpack'],
                            cwd=ROOT,text=True,capture_output=True)
    if result.returncode not in (0,1): raise ValueError(result.stderr)
    allowed = {main_path.resolve(), *(p.resolve() for p in base.glob(f'S{stage}*.lean'))}
    unexpected = [p for p in result.stdout.splitlines() if (ROOT/p).resolve() not in allowed]
    if unexpected: raise ValueError(f'External certificate consumers require review: {unexpected}')
    return main_path, main, match, definitions

def digest(text): return hashlib.sha256(text.encode()).hexdigest()

def transform(stage_name, part, write=False, receipt=None, sources=None):
    family, stage_token = stage_name.split('/'); stage = int(stage_token.removeprefix('S'))
    src = sources if sources is not None else Sources()
    base=GEN/family; shard=base/f'S{stage}C{part}.lean'
    text=src.text(shard)
    if 'CompactWitness.sub' in text: raise ValueError(f'Already compact: {shard}')
    owner, input_rows, owned = source_state(src,family,stage)
    check_source = src.text(ROOT / 'ElevenSquare/Tasks/T07/Ext/Check.lean')
    poly_source = src.text(ROOT / 'ElevenSquare/Tasks/T07/Ext/Poly.lean')
    cap_match = re.search(r'^def coverQ : ℚ := (\d+) / (\d+)$', check_source, re.M)
    grid_match = re.search(r'^def gridG : ℕ := (\d+) \^ (\d+)$', poly_source, re.M)
    if not cap_match or not grid_match: raise ValueError('Unrecognized coordinate constants')
    cap = Q(int(cap_match[1]), int(cap_match[2]))
    grid = int(grid_match[1]) ** int(grid_match[2])
    if grid != 10**20: raise ValueError('Collision scale changed; update reconstruction')
    main_source = src.text(base/f'S{stage}.lean')
    statement = f'theorem step_ok : stepB prev {owner} rs pcov certs = true'
    if statement not in main_source: raise ValueError('Stage owner differs from checker contract')
    main_path, main_source, list_match, parameterized = audit_stage_consumers(src,family,stage,len(input_rows))
    rs = datum(src.definition(base/f'S{stage}C.lean','rs'))
    replacements=[]; counts=Counter()
    for name in re.findall(r'^def (cert\d+)\s*:',text,re.M):
        row=int(name[4:]); cert=src.definition(shard,name)
        if not 0 <= row < len(input_rows): raise ValueError('Invalid input row')
        for u in cert.args:
            if u.kind!='struct' or len(u.args)!=8: raise ValueError('Unsupported Sub literal')
            a,b,cuts,wall,core,ccore,regs=map(datum,u.args[:7])
            P=input_rows[row][2]+[[k[0]*(-1 if k[3] else 1),k[1]*(-1 if k[3] else 1),k[5]] for k in cuts]
            P += [[-Q(1),Q(0),-wall],[Q(1),Q(0),cap-wall],[Q(0),-Q(1),-wall],[Q(0),Q(1),cap-wall]]
            tree=rewrite_tree(u.args[7],P,rs,owned,core,regs,counts)
            new=f'CompactWitness.sub prev {owner} rs {row} '+' '.join(v.raw for v in u.args[:7])+'\n  '+tree
            replacements.append((u.start,u.end,new)); counts['subrows']+=1
        counts['rows']+=1
    if not replacements: raise ValueError('No certificate definitions found')
    result=text
    for start,end,new in sorted(replacements,reverse=True): result=result[:start]+new+result[end:]
    result=result.replace('import ElevenSquare.Tasks.T07.Ext.CTreeChain',
        'import ElevenSquare.Tasks.T07.Ext.CompactWitness')
    result=re.sub(r'^def (cert\d+) : List Sub :=',
        r'def \1 (prev : PoseState) (rs : List PoseRow) : List Sub :=',result,flags=re.M)
    converted_names=set(re.findall(r'^def (cert\d+) \(prev : PoseState\)',result,re.M))
    if converted_names != set(re.findall(r'^def (cert\d+) : List Sub :=',text,re.M)):
        raise ValueError('Converted certificate names changed')
    calls=[f'cert{k}'+(' prev rs' if parameterized[f'cert{k}'] or f'cert{k}' in converted_names else '')
           for k in range(len(input_rows))]
    main_result=main_source[:list_match.start(1)]+', '.join(calls)+main_source[list_match.end(1):]
    report={'schema':1,'kind':'exact-rational-witness-reconstruction',
        'kernel_acceptance':False,'file':str(shard.relative_to(ROOT)),
        'before_sha256':digest(text),'after_sha256':digest(result),
        'before_bytes':len(text.encode()),'after_bytes':len(result.encode()),
        'before_lines':len(text.splitlines()),'after_lines':len(result.splitlines()),
        'counts':dict(counts),'helper_sha256':digest(HELPER.read_text()),
        'transformer_sha256':digest(Path(__file__).read_text()),
        'parameterized_certificates':sorted(converted_names,key=lambda n:int(n[4:])),
        'stage_consumer':{'file':str(main_path.relative_to(ROOT)),
            'before_sha256':digest(main_source),'after_sha256':digest(main_result)},
        'context_sources':{str(p.relative_to(ROOT)):digest(s) for p,s in sorted(src.texts.items()) if p!=shard.resolve()}}
    if write:
        shard.write_text(result)
        main_path.write_text(main_result)
        # The next shard in a batch must inspect the new calls and signatures.
        src.texts[main_path.resolve()] = main_result
        src.texts[shard.resolve()] = result
    if receipt:
        receipt.parent.mkdir(parents=True,exist_ok=True)
        receipt.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='context_sources'},sort_keys=True))
    return report

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage',default='P2/S137')
    parser.add_argument('--part',type=int,default=0)
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--all-parts',action='store_true')
    parser.add_argument('--through-stage',type=int)
    parser.add_argument('--max-seconds',type=float,default=300)
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    if not args.all_parts and args.through_stage is None:
        transform(args.stage,args.part,args.write,args.receipt)
        return
    family, token = args.stage.split('/')
    first = int(token.removeprefix('S'))
    last = args.through_stage if args.through_stage is not None else first
    start = time.monotonic(); reports=[]; skipped=[]; bounded=False
    for stage in range(first,last+1):
        src=Sources()
        paths=sorted((GEN/family).glob(f'S{stage}C[0-9]*.lean'),
            key=lambda p:int(re.fullmatch(r'S\d+C(\d+)\.lean',p.name)[1]))
        for path in paths:
            if time.monotonic()-start > args.max_seconds:
                bounded=True;break
            if 'CompactWitness.sub' in path.read_text():
                skipped.append(str(path.relative_to(ROOT)));continue
            part=int(re.fullmatch(r'S\d+C(\d+)\.lean',path.name)[1])
            reports.append(transform(f'{family}/S{stage}',part,args.write,None,src))
            # Keep the stage's parsed state, not completed certificate ASTs.
            for key in list(src.defs):
                if key[0] == path.resolve(): del src.defs[key]
            src.texts.pop(path.resolve(),None)
        if bounded:break
    summary={'schema':1,'kind':'bounded-exact-witness-reconstruction-batch',
        'kernel_acceptance':False,'write':args.write,'seconds':time.monotonic()-start,
        'stopped_at_time_bound':bounded,'files':reports,'skipped_already_compact':skipped,
        'before_bytes':sum(r['before_bytes'] for r in reports),
        'after_bytes':sum(r['after_bytes'] for r in reports),
        'before_lines':sum(r['before_lines'] for r in reports),
        'after_lines':sum(r['after_lines'] for r in reports)}
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print(json.dumps({**{k:v for k,v in summary.items() if k!='files'},
        'file_count':len(reports)},sort_keys=True))
if __name__=='__main__': main()
