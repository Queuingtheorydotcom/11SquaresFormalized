#!/usr/bin/env python3
"""Factor identical proof adapters; refuse source shapes outside the audited pattern."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
TAIL = '''  rcases ho with ⟨S, hS, rfl⟩ | ⟨e, he, rfl⟩
  · exact Or.inl ⟨S, hS, fun a ha g hg' => hg g (List.mem_flatMap.mpr ⟨a, ha, hg'⟩)⟩
  · obtain ⟨p, hp, hm⟩ := hg _ (List.mem_singleton_self _)
    simp only [List.mem_singleton] at hp
    subst hp
    exact Or.inr ⟨e, he, hm⟩'''
COVER = re.compile(
    r'  obtain ⟨o, ho, hg⟩ := (bridge [^\n]+)\n'
    r'  simp only \[opts(\d+), List.mem_append, List.mem_map\] at ho\n' + re.escape(TAIL))
CAP = re.compile(
    r'  have hb := baryAll_spec \(sites := sites(\d+)\) \(subs := subs\1\)\n'
    r'    \(groups := atoms.getD \1 \[\]\) \(barys := barys\1\) \(by decide \+kernel\)\n'
    r'  exact maj_capacity \(Q := G.Q\) \(k := (\d+)\) \(sites := sites\1\) \(subs := subs\1\)\n'
    r'    \(by decide \+kernel\) \(by decide \+kernel\)\n'
    r'    hb.1 hb.2 hAc hAo hBc hBo hAB hA hB')

def transform(text):
    replacements = []
    def cover(m):
        call, index = m.groups()
        out = ('  exact field_option_cases (atoms := atoms) (sets := optSets' + index + ')\n'
               '    (used := used' + index + ') (' + call + ')')
        replacements.append((out, m[0]))
        return out
    def cap(m):
        i, k = m.groups()
        out = (f'  exact checked_maj_capacity (k := {k}) (sites := sites{i}) (subs := subs{i})\n'
               f'    (barys := barys{i}) (by decide +kernel) (by decide +kernel) (by decide +kernel)\n'
               '    hAc hAo hBc hBo hAB hA hB')
        replacements.append((out, m[0]))
        return out
    out, covers = COVER.subn(cover, text)
    out, caps = CAP.subn(cap, out)
    back = out
    # Each replacement is unique within its field namespace.
    for new, old in reversed(replacements):
        assert back.count(new) == 1
        back = back.replace(new, old, 1)
    assert back == text, 'Proof-body substitution altered other source'
    if replacements:
        out = out.replace('import Sqpack.S11Opt.FieldGen\n',
                          'import Sqpack.S11Opt.Simplified.BundledAdapters\n', 1)
    return out, covers, caps

if __name__ == '__main__':
    report = {'status': 'SOURCE_ROUNDTRIP_ONLY', 'files': [], 'covers': 0, 'capacities': 0}
    pending = []
    for p in sorted((ROOT / 'Sqpack/S11Opt/Bundled').glob('F*/Final.lean')):
        old = p.read_text()
        new, covers, caps = transform(old)
        if old == new:
            continue
        report['files'].append({'path': str(p.relative_to(ROOT)), 'covers': covers,
            'capacities': caps, 'old_sha256': hashlib.sha256(old.encode()).hexdigest(),
            'new_sha256': hashlib.sha256(new.encode()).hexdigest(),
            'lines_removed': len(old.splitlines()) - len(new.splitlines())})
        report['covers'] += covers
        report['capacities'] += caps
        pending.append((p, new))
    if pending:
        assert report['covers'] == 187 and report['capacities'] == 147, report
        for p, new in pending:
            p.write_text(new)
        (ROOT / 'simplification/bundled-adapter-source-roundtrip.json').write_text(
            json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: (len(v) if k == 'files' else v) for k, v in report.items()}))
