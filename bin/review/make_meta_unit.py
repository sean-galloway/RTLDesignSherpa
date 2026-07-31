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
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def inventory(area):
    """Module basenames under rtl/<area>/, sorted. Empty if the area is gone."""
    return sorted(os.path.basename(p) for p in glob.glob(f'{REPO}/rtl/{area}/*.sv'))


def meta_pages(book, area):
    """The meta-docs, in reading order. Only the ones that exist."""
    d = f'{REPO}/docs/markdown/{book}'
    cands = [f'{d}/index.md', f'{d}/overview.md', f'{d}/quickstart.md']
    cands += sorted(glob.glob(f'{d}/_book_*_index.md'))
    cands += [f'{REPO}/rtl/{area}/CLAUDE.md', f'{REPO}/rtl/{area}/README.md']
    return [p for p in cands if os.path.isfile(p)]


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
    rtl += [f'//   {m}' for m in mods]
    for other in args.also_list:
        omods = inventory(other)
        rtl += ['//',
                f'// Modules that live in rtl/{other}/ ({len(omods)}), NOT rtl/{args.area}/.',
                f'// Listed so "the doc says this lives in {args.area}" is separable from',
                '// "this module does not exist".',
                '//']
        rtl += [f'//   {m}' for m in omods]
    with open(f'{out}/RTL.sv', 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(rtl) + '\n')

    doc = [f'# {book} meta-docs',
           '',
           f'{len(pages)} documentation files. These are the pages OUTSIDE the '
           f'`{args.area}` book bundle: the catalogue, the orientation, the '
           'quickstart and the beside-code guidance. RTL.sv is a module '
           'inventory, not source -- it is here to settle count and existence '
           'claims.',
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
    for p in pages:
        print(f'    {os.path.relpath(p, REPO)}')


if __name__ == '__main__':
    main()
