#!/usr/bin/env python3
"""Build a `<area>_meta` review unit: the meta-docs a book bundle never sees.

`build_review_bundle.py` builds a unit per `docs/markdown/**/_book_*_index.md`
and includes only `overview.md` plus the pages that index links -- so
`index.md`, `quickstart.md`, the book index itself and the area's beside-code
`CLAUDE.md` are outside the bundle. Those are exactly the pages that carry
module counts and category lists, and exactly the ones that rot when modules
move (rtl/common claimed 86 modules after the split left 49).

The unit's `RTL.sv` is an INVENTORY, not source: ground truth for
count/category/existence claims. Where an area's modules have moved, the
inventory of the new location is listed too, so "the doc says X lives here"
stays separable from "X does not exist".

The bundler `rm -rf`s `books/`, so this must be re-run after EVERY rebuild.
Never edit a previous copy -- a hand-maintained inventory is what goes stale.

    python3 bin/review/make_meta_unit.py common ~/rtl-doc-review/books
    python3 bin/review/make_meta_unit.py common ~/rtl-doc-review/books \
        --book rtl-common --also-list cdc math
"""
import argparse
import glob
import re
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


EXCLUDE = ('/testcode/', '/includes/', '/OLD/', '/dv/')


def inventory(area):
    """(subdir, module) under rtl/<area>/, sorted. Empty if the area is gone.

    Recursive, because an area is not always a flat directory: rtl/amba holds
    its 133 modules in per-protocol subdirectories and a flat glob finds none
    of them -- which reads as "the area is gone" and aborts. `subdir` is ''
    for a flat area (common, cdc, math), so their inventories are unchanged.
    Include files and testcode are not modules and stay out, the same
    exclusions the bundler applies."""
    root = f'{REPO}/rtl/{area}'
    out = []
    for p in sorted(glob.glob(f'{root}/**/*.sv', recursive=True)):
        if any(x in p for x in EXCLUDE):
            continue
        out.append((os.path.dirname(os.path.relpath(p, root)), os.path.basename(p)))
    return sorted(out)


def render_inventory(area, mods):
    """Inventory lines, grouped by subdirectory when the area has any."""
    if not any(sub for sub, _ in mods):
        return [f'//   {m}' for _, m in mods]
    lines, cur = [], None
    for sub, m in mods:
        if sub != cur:
            cur = sub
            lines += ['//', f'//   rtl/{area}/{sub or "."}/']
        lines.append(f'//     {m}')
    return lines


def meta_pages(book, area):
    """The meta-docs, in reading order. Only the ones that exist.

    Everything beside the area's code counts, not just CLAUDE.md/README.md --
    a standalone guide parked in the RTL tree (rtl/amba once carried a
    VERIFICATION_ARCHITECTURE.md, retired 2026-08-09) is the page most likely
    to describe a structure that has since changed, and nothing else in the
    pipeline reads it."""
    d = f'{REPO}/docs/markdown/{book}'
    cands = [f'{d}/index.md', f'{d}/overview.md', f'{d}/quickstart.md']
    cands += sorted(glob.glob(f'{d}/_book_*_index.md'))
    cands += sorted(glob.glob(f'{REPO}/rtl/{area}/*.md'))
    return [p for p in cands if os.path.isfile(p)]


def port_block(sv_path):
    """The `module ... );` header: parameters and ports, no body."""
    src = open(sv_path, encoding='utf-8', errors='replace').read()
    m = re.search(r'^module\s+\w+.*?^\s*\);', src, re.S | re.M)
    return m.group(0) if m else None


def instantiated_modules(doc_text, area):
    """Modules the meta-docs show being INSTANTIATED, not merely mentioned.

    A `_meta` unit's RTL.sv is an inventory, which settles existence and count
    claims but says nothing about interfaces -- so a code example connecting
    ports that do not exist reads as unverifiable and survives review. common
    round_1 (2026-07-30) shipped four such patterns: counter_bin documented
    with .i_clk/.o_count/.o_overflow against real clk/counter_bin_curr and no
    overflow port at all, counter_freq_invariant as a timeout timer it is not,
    plus wrong parameter names on arbiter_round_robin and dataint_crc. None
    were findable from an inventory.

    Matching `name #(` and `name u_inst (` keeps this to modules the docs tell
    a reader to wire up, which is where interface claims are actionable.
    """
    names = set(re.findall(r'^\s*([a-z][a-z0-9_]{3,})\s*#?\s*\(', doc_text, re.M))
    names |= set(re.findall(r'\b([a-z][a-z0-9_]{3,})\s+u_\w+\s*\(', doc_text))
    out = {}
    for n in sorted(names):
        for cand in glob.glob(f'{REPO}/rtl/**/{n}.sv', recursive=True):
            blk = port_block(cand)
            if blk:
                out[n] = (os.path.relpath(cand, REPO), blk)
            break
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('area', help='RTL area under rtl/, e.g. common')
    ap.add_argument('books', help='the bundle books dir, e.g. ~/rtl-doc-review/books')
    ap.add_argument('--book', help='docs/markdown book dir (default: rtl-<area>)')
    ap.add_argument('--also-list', nargs='*', default=[],
                    help='other areas whose inventory to include, for modules '
                         'that MOVED out of this one (e.g. cdc math)')
    args = ap.parse_args()

    book = args.book or f'rtl-{args.area}'
    out = os.path.join(os.path.expanduser(args.books), f'{args.area}_meta')

    mods = inventory(args.area)
    if not mods:
        sys.exit(f'error: no modules under rtl/{args.area}/ -- wrong area name?')
    pages = meta_pages(book, args.area)
    if not pages:
        sys.exit(f'error: no meta-docs found for book docs/markdown/{book}/')

    os.makedirs(out, exist_ok=True)

    rtl = [f'// {args.area} meta-docs -- ground truth is the module INVENTORY, not full source.',
           '//',
           '// These pages make count, category and existence claims about the area.',
           f'// Verify them against this list: rtl/{args.area}/ holds {len(mods)} modules.',
           '//']
    rtl += render_inventory(args.area, mods)
    for other in args.also_list:
        omods = inventory(other)
        rtl += ['//',
                f'// Modules that live in rtl/{other}/ ({len(omods)}), NOT rtl/{args.area}/.',
                f'// Listed so "the doc says this lives in {args.area}" is separable from',
                '// "this module does not exist".',
                '//']
        rtl += render_inventory(other, omods)

    doc_text = '\n'.join(open(p, encoding='utf-8').read() for p in pages)
    insts = instantiated_modules(doc_text, args.area)
    if insts:
        rtl += ['',
                '// ' + '=' * 74,
                '// INTERFACES OF THE MODULES THESE PAGES INSTANTIATE',
                '//',
                '// Parameter and port declarations only, no bodies. The inventory above',
                '// settles existence; this settles whether a code example would compile.',
                '// A doc that connects a port not declared here, or overrides a parameter',
                '// by a name not declared here, is wrong.',
                '// ' + '=' * 74,
                '']
        for name, (src, blk) in insts.items():
            rtl += [f'// SOURCE FILE: {src}', blk, '']
    with open(f'{out}/RTL.sv', 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(rtl) + '\n')

    doc = [f'# {book} meta-docs',
           '',
           f'{len(pages)} documentation files. These are the pages OUTSIDE the '
           f'`{args.area}` book bundle: the catalogue, the orientation, the '
           'quickstart and the beside-code guidance. RTL.sv carries a module '
           'inventory for count and existence claims, plus the parameter and '
           'port declarations of every module these pages show being '
           'instantiated -- so code examples can be checked against real '
           'interfaces.',
           '']
    for p in pages:
        rel = os.path.relpath(p, REPO)
        doc += [f'<!-- SOURCE FILE: {rel} -->', '',
                open(p, encoding='utf-8').read(), '']
    with open(f'{out}/DOCS.md', 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(doc))

    print(f'{args.area}_meta -> {out}')
    print(f'  {len(pages)} pages, {len(mods)} modules in inventory'
          + (f' (+{sum(len(inventory(o)) for o in args.also_list)} from '
             f'{", ".join(args.also_list)})' if args.also_list else ''))
    print(f'  {len(insts)} instantiated-module interfaces: '
          + ', '.join(insts) if insts else '  no instantiations found in the docs')
    for p in pages:
        print(f'    {os.path.relpath(p, REPO)}')


if __name__ == '__main__':
    main()
