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

VENDORED = ('/external/', '/.bender/', '/checkouts/', '/node_modules/',
            '/third_party/', '/vendor/')

def canon(paths):
    c = [p for p in paths
         if '/OLD/' not in p and '/dv/' not in p and '/testcode/' not in p
         and not any(v in p for v in VENDORED)]
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

def modules_from_text(text):
    """Modules a document NAMES, for units whose filenames are not module names.

    The filename->module mapping works for the rtl-area pages, where
    `axi4_master_rd.md` documents `axi4_master_rd`. A component book is
    chaptered instead -- `04_axi4_to_apb4.md`, `01_architecture.md` --
    so nothing matches and the unit is packaged with an EMPTY RTL.sv
    that still announces itself as ground truth. A qc round on that
    asks "is this true?" while supplying nothing to be true against.

    Falls back to what the prose names: every identifier that is also a
    known module. Over-inclusion is the safe direction here -- an extra
    module costs tokens, a missing one costs a false finding.
    """
    # Only look where a module is NAMED as code -- inline `spans` and
    # fenced blocks. Scanning raw prose matches ordinary English: "read"
    # is a word on every page and also a vendored module, so a plain
    # word-scan drags third-party RTL in as this repo's ground truth.
    spans = re.findall(r'`([^`\n]+)`', text)
    spans += re.findall(r'```[a-z]*\n(.*?)```', text, re.S)
    spans += re.findall(r'^\s*\|(.+)\|\s*$', text, re.M)   # table cells
    hay = '\n'.join(spans)
    out = []
    for tok in sorted(set(re.findall(r'\b[a-z][a-z0-9_]{3,}\b', hay))):
        if tok in KW or tok not in sv:
            continue
        c = canon(sv[tok])
        if c and c not in out:
            out.append(c)
    return out


def write_unit(d, title, docs, note=''):
    os.makedirs(d, exist_ok=True)
    docs_text = []
    with open(f'{d}/DOCS.md', 'w', encoding='utf-8') as fh:
        fh.write(f'# {title}\n\n{len(docs)} documentation files.{note}\n'
                 'Each section is one source file; cite findings by the path in its banner.\n\n---\n')
        for p in docs:
            fh.write(f'\n\n<!-- ================================================= -->\n'
                     f'<!-- SOURCE FILE: {p} -->\n'
                     f'<!-- ================================================= -->\n\n')
            body_md = open(p, encoding='utf-8').read()
            docs_text.append(body_md)
            fh.write(body_md)
    rtl = []
    for p in docs:
        for c in modules_for(os.path.basename(p)[:-3]):
            if c not in rtl: rtl.append(c)
    if not rtl:
        # Chaptered book: recover the modules from what the prose names.
        rtl = modules_from_text('\n'.join(docs_text))
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
# Chaptered specs. Their chapter names don't match .sv stems, so the
# filename->module mapping finds nothing; write_unit falls back to the modules
# the prose NAMES (modules_from_text) rather than shipping an empty RTL.sv.
#
# This used to be left empty deliberately, on the grounds that these books are
# humanize-first and humanize never sends RTL. That stopped being true when the
# books were queued for correctness first (DOCREV-017): a qc round asks "is this
# doc true against the RTL?", and an empty RTL.sv still announcing itself as
# GROUND TRUTH is the mis-packaging rule 5 exists for -- every documented module
# reads as never written.
#
# Caveat for the generated fabrics: bridge and apbx_xbar RTL is emitted by a
# generator, so their real ground truth is the generator plus its output. The
# generated modules are bundled here; the generator source is not. Read it
# alongside when triaging those two books.
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
    # Same LIMIT as every other unit: a book that now carries real RTL can
    # exceed it, and an over-budget unit comes back truncated rather than loud.
    #
    # MEASURE, don't estimate. The docs*3 heuristic the other books use assumes
    # RTL is about twice the prose; a book whose RTL outweighs it (converters:
    # 145KB docs, 433KB RTL) passes the estimate and lands over budget anyway.
    # So write the single unit, look at what it actually came to, and fall back
    # to parts if it is too big -- deleting the oversized unit, or the bundle
    # would hold both and a batch would send the stale one.
    sz = write_unit(f'{OUT}/books/{key}', title, docs)
    if sz <= LIMIT:
        manifest.append((key, 1, sz // 4))
        print(f'  {key:14s} 1 unit   ~{sz//4000}k tok')
    else:
        for f in ('DOCS.md', 'RTL.sv'):
            fp = f'{OUT}/books/{key}/{f}'
            if os.path.exists(fp): os.remove(fp)
        # Bucket by this book's OWN measured expansion (unit bytes per doc
        # byte), not the shared *3 guess -- that guess is what let an
        # over-budget unit through a moment ago, and reusing it here just
        # reproduces the same single oversized part.
        doc_bytes = sum(os.path.getsize(d) for d in docs) or 1
        ratio = sz / doc_bytes
        parts, cur, cursz = [], [], 0
        for d in docs:
            s = os.path.getsize(d) * ratio
            if cur and cursz + s > LIMIT: parts.append(cur); cur, cursz = [], 0
            cur.append(d); cursz += s
        if cur: parts.append(cur)
        tot = 0
        for i, part in enumerate(parts, 1):
            tot += write_unit(f'{OUT}/books/{key}/parts/part_{i:02d}', title, part,
                              note=f' Part {i} of {len(parts)}.')
        manifest.append((key, len(parts), tot // 4))
        print(f'  {key:14s} {len(parts)} parts  ~{tot//4000}k tok')

json.dump([{'book': k, 'parts': n, 'ktok': t // 1000} for k, n, t in manifest],
          open(f'{OUT}/.manifest.json', 'w'), indent=1)
print(f'\n  bundle rebuilt at {OUT} from current working tree')
