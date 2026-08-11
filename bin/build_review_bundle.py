#!/usr/bin/env python3
"""
Rebuild the documentation review bundles from the CURRENT docs and RTL.

Each book (and each part of an oversized book) becomes a self-contained review
unit: DOCS.md (the documentation) + RTL.sv (the modules it documents, plus their
dependency closure) + optionally DOCS_WITH_NO_MODULE.md.

PROCESS RULE: clear the staging area, package EVERYTHING, then send only the
packages that are needed. Never package a subset.

This script always `rm -rf`s the output books directory and regenerates all books
from the current working tree. Do not add a book filter or an "only rebuild what
changed" optimisation - selection belongs at the send step, not the build step.

The reason is that a stale or partial bundle produces findings indistinguishable
from real ones: the reviewer reports defects that were already fixed, and you
cannot tell from the output which is which. That has already cost one full review
pass. Rebuilding everything is cheap; re-reviewing stale content is not.

Usage: python3 bin/build_review_bundle.py [out_dir]
"""
import os, re, sys, glob, json, collections

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT  = sys.argv[1] if len(sys.argv) > 1 else '/mnt/data/github/rtl-doc-review'
MD   = 'docs/markdown'
LIMIT = 120_000 * 4          # chars; ~120k tokens per unit

os.chdir(REPO)

# ---- index every .sv so a doc can be matched to the module it documents ----
sv = collections.defaultdict(list)
for root, dirs, files in os.walk('.'):
    dirs[:] = [d for d in dirs if d not in ('.git', 'node_modules', 'venv', 'obj_dir')]
    for f in files:
        if f.endswith('.sv'):
            sv[f[:-3]].append(os.path.join(root, f)[2:])

def canon(paths):
    c = [p for p in paths if '/OLD/' not in p and '/dv/' not in p and '/testcode/' not in p]
    if not c: return None
    r = [p for p in c if p.startswith('rtl/')]
    return sorted(r or c, key=len)[0]

def modules_for(stem):
    if stem in sv:
        p = canon(sv[stem]); return [p] if p else []
    # Width-suffixed family: math_adder_brent_kung -> _008/_016/_032/_064
    fam = [k for k in sv if re.fullmatch(re.escape(stem) + r'_\d+', k)]
    if fam:
        return [p for p in (canon(sv[k]) for k in sorted(fam)) if p]
    # Named-variant family: math_subtractor -> _half/_full/_full_nbit/
    # _ripple_carry/_carry_lookahead. Without this the page arrives with no RTL
    # and every reviewer reports its modules as never written.
    fam = [k for k in sv if re.fullmatch(re.escape(stem) + r'_[a-z][a-z0-9_]*', k)]
    return [p for p in (canon(sv[k]) for k in sorted(fam)) if p]

KW = {'module','if','else','for','case','begin','end','always','assign','logic','wire',
      'generate','endgenerate','endmodule','initial','function','task','posedge','negedge',
      'input','output','inout','parameter','localparam','typedef','enum','struct','endcase',
      'while','return','signed','unsigned','int','bit','reg','integer','genvar','endfunction'}

def deps_of(text, present):
    """One-level-plus closure of modules instantiated by `text`."""
    out, seen = [], set(present)
    queue = [m for m in re.findall(r'^\s{0,8}([a-z_][a-z0-9_]{3,})\s*(?:#\s*\(|[A-Za-z_]\w*\s*\()',
                                   text, re.M) if m in sv and m not in KW]
    while queue:
        m = queue.pop(0)
        if m in seen: continue
        c = canon(sv.get(m, []))
        if not c: continue
        seen.add(m); out.append((m, c))
        sub = open(c, encoding='utf-8', errors='replace').read()
        for m2 in re.findall(r'^\s{0,8}([a-z_][a-z0-9_]{3,})\s*(?:#\s*\(|[A-Za-z_]\w*\s*\()', sub, re.M):
            if m2 not in seen and m2 not in KW and m2 in sv: queue.append(m2)
    return out

def write_unit(d, title, docs, note=''):
    os.makedirs(d, exist_ok=True)
    with open(f'{d}/DOCS.md', 'w', encoding='utf-8') as fh:
        fh.write(f'# {title}\n\n{len(docs)} documentation files.{note}\n'
                 'Each section is one source file; cite findings by the path in its banner.\n\n---\n')
        for p in docs:
            fh.write(f'\n\n<!-- ================================================= -->\n'
                     f'<!-- SOURCE FILE: {p} -->\n'
                     f'<!-- ================================================= -->\n\n')
            fh.write(open(p, encoding='utf-8').read())
    rtl = []
    for p in docs:
        for c in modules_for(os.path.basename(p)[:-3]):
            if c not in rtl: rtl.append(c)
    body = ''.join(open(p, encoding='utf-8', errors='replace').read() for p in rtl)
    present = set(re.findall(r'^module\s+(\w+)', body, re.M))
    extra = deps_of(body, present)
    with open(f'{d}/RTL.sv', 'w', encoding='utf-8') as fh:
        fh.write(f'// {title} -- RTL for the documents in DOCS.md\n'
                 f'// {len(rtl)} documented modules + {len(extra)} dependencies.\n'
                 '// GROUND TRUTH: if a doc disagrees with this, the doc is wrong.\n')
        for p in rtl + [c for _, c in extra]:
            fh.write(f'\n\n// =================================================\n'
                     f'// SOURCE FILE: {p}\n'
                     f'// =================================================\n\n')
            fh.write(open(p, encoding='utf-8', errors='replace').read())
    return os.path.getsize(f'{d}/DOCS.md') + os.path.getsize(f'{d}/RTL.sv')

os.system(f'rm -rf {OUT}/books')
manifest = []
for idx in sorted(glob.glob(f'{MD}/**/_book_*_index.md', recursive=True)):
    key = re.search(r'_book_(.+)_index\.md$', idx).group(1)
    title = next((l[2:].strip() for l in open(idx, encoding='utf-8') if l.startswith('# ')), key)
    base = os.path.dirname(idx)
    docs = []
    for m in re.finditer(r'\]\(([^)]+\.md)\)', open(idx, encoding='utf-8').read()):
        p = os.path.normpath(os.path.join(base, m.group(1)))
        if os.path.exists(p) and p not in docs: docs.append(p)
    if not docs: continue

    total = sum(os.path.getsize(p) for p in docs) * 3   # rough, docs+rtl
    if total <= LIMIT:
        sz = write_unit(f'{OUT}/books/{key}', title, docs)
        manifest.append((key, 1, sz // 4)); print(f'  {key:10s} 1 unit   ~{sz//4000}k tok')
    else:
        parts, cur, cursz = [], [], 0
        for p in docs:
            s = os.path.getsize(p) * 3
            if cur and cursz + s > LIMIT: parts.append(cur); cur, cursz = [], 0
            cur.append(p); cursz += s
        if cur: parts.append(cur)
        tot = 0
        for i, part in enumerate(parts, 1):
            sz = write_unit(f'{OUT}/books/{key}/parts/part_{i:02d}', title, part,
                            note=f' Part {i} of {len(parts)}.')
            tot += sz
        manifest.append((key, len(parts), tot // 4))
        print(f'  {key:10s} {len(parts)} parts  ~{tot//4000}k tok')

# ---- HAS/MAS spec books (projects/components/*/docs/<book>/<book>_index.md).
# Chaptered specs, humanize-first consumers; their chapter names don't match
# .sv stems so RTL.sv comes out effectively empty — that's fine, the humanize
# mode never sends it and a qc round on these should read the generator, not
# guess at RTL.
for idx in sorted(glob.glob('projects/components/*/docs/*/*_index.md')):
    base = os.path.dirname(idx)
    key = os.path.basename(base)                      # e.g. bridge_has
    if not re.search(r'_(has|mas)$', key): continue
    title = next((l[2:].strip() for l in open(idx, encoding='utf-8') if l.startswith('# ')), key)
    docs = []
    for m in re.finditer(r'\]\(([^)]+\.md)\)', open(idx, encoding='utf-8').read()):
        pth = os.path.normpath(os.path.join(base, m.group(1)))
        if os.path.exists(pth) and pth not in docs: docs.append(pth)
    if not docs: continue
    docs.insert(0, idx)                               # index prose is part of the doc
    sz = write_unit(f'{OUT}/books/{key}', title, docs)
    manifest.append((key, 1, sz // 4)); print(f'  {key:14s} 1 unit   ~{sz//4000}k tok')

json.dump([{'book': k, 'parts': n, 'ktok': t // 1000} for k, n, t in manifest],
          open(f'{OUT}/.manifest.json', 'w'), indent=1)
print(f'\n  bundle rebuilt at {OUT} from current working tree')
