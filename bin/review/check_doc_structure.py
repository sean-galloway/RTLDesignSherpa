#!/usr/bin/env python3
"""Report how far a doc area's `##` headings drift from the canonical set.

The humanize pass is told to unify structure, and it does -- but "unify" without
a named target set lets each round settle on its own self-consistent scheme, so
areas humanized in different rounds ended up internally tidy and mutually
inconsistent. This measures that, per area, so the question "does this area need
re-humanizing?" has a number behind it instead of an impression.

    python3 bin/review/check_doc_structure.py docs/markdown/rtl-common
    python3 bin/review/check_doc_structure.py docs/markdown/rtl-*  docs/markdown/rtl-amba/gaxi

Reports, per area:
  - pages fully conformant (every `##` is canonical, no required section missing)
  - which canonical sections are missing, and from how many pages
  - which non-canonical headings appear, and how often -- the rename candidates

Exit status is 0 always: this is a report, not a gate. The gate for a humanize
round is check_tag_survival.py; this tells you whether a round is worth running.
"""
import os
import re
import sys
import glob
import collections

# The canonical spine. Derived from vault/handbook/authoring/module-doc-template.md
# and from what the most recently humanized area actually converged on, which is
# not the same thing -- where they disagreed, observed usage won, because a
# standard nothing follows is a wish.
CANONICAL = [
    'Overview',
    'Module Interface',      # optional: the SystemVerilog declaration block
    'Parameters',
    'Ports',
    'Functional Description',
    'Timing Characteristics',
    'Waveforms',             # optional: wavedrom timing diagrams
    'Timing Diagrams',       # optional: alias-adjacent, same purpose
    'Usage Examples',
    'Design Notes',
    'Related Modules',
    'Testing',
    'References',            # optional
    'Navigation',
]
# Allowed but not required. Every name here MUST also appear in CANONICAL:
# conformance requires each heading to be in CANONICAL, and REQUIRED is
# derived as CANONICAL - OPTIONAL. 'Waveforms' and 'Timing Diagrams' were
# listed here but NOT in CANONICAL, which made them dead configuration --
# they could not be required, and a page carrying one was marked
# non-conformant for having it. Four axil4 pages failed on exactly that.
OPTIONAL = {'Module Interface', 'References', 'Waveforms', 'Timing Diagrams'}
REQUIRED = [h for h in CANONICAL if h not in OPTIONAL]

# Headings that mean a canonical section under a different name. Rename, do not
# invent a new section for them.
ALIASES = {
    'Module Parameters': 'Parameters',
    'Port Groups': 'Ports',
    'Interface Signals': 'Ports',
    'Behavior': 'Functional Description',
    'Functionality': 'Functional Description',
    'Theory of operation': 'Functional Description',
    'Implementation': 'Functional Description',
    'Implementation Details': 'Functional Description',
    # Verified by reading the content behind each, 2026-09-02: 'Module
    # Declaration' holds the SystemVerilog declaration block, 'Module
    # Architecture' holds the block diagram, 'Related Documentation' holds the
    # see-also list. Same section, different name -- which is what this map is
    # for; the alternative is inventing a parallel spine per book.
    'Module Declaration': 'Module Interface',
    'Module Architecture': 'Functional Description',
    'Architecture and Implementation': 'Functional Description',
    'Architecture': 'Functional Description',
    'Implementation': 'Functional Description',
    'Related Documentation': 'Related Modules',
    'Related': 'Related Modules',
    'Performance Characteristics': 'Timing Characteristics',
    'Synthesis Considerations': 'Design Notes',
    'Known Limitations': 'Design Notes',
    'Common Applications': 'Usage Examples',
    'Timing': 'Timing Characteristics',
    'Timing Diagrams': 'Timing Characteristics',
    'Usage Example': 'Usage Examples',
    'Design examples': 'Usage Examples',
    'Design Considerations': 'Design Notes',
    'Design considerations': 'Design Notes',
    'Notes': 'Design Notes',
    'Test Coverage': 'Testing',
    'Verification': 'Testing',
    'Comparison with Related Modules': 'Related Modules',
}

# Non-module pages. The spine below describes a page that documents ONE
# module; an index, an overview or a cross-cutting guide has no module to
# have Parameters or Ports for. `*_guide.md` pages (three of them, all
# clock-gating techniques spanning a family) were being counted against
# their book for lacking sections they cannot have.
SKIP = {'index.md', 'README.md', 'overview.md', 'quickstart.md'}
SKIP_SUFFIX = ('_guide.md',)
SKIP_PREFIX = ('_book_',)          # generated book indexes, built by gen_index


def is_module_page(path):
    """True when the page documents ONE module that exists in the tree.

    The spine below describes a per-module page. A family page
    (`math_fp16_modules.md`, `math_adder_basic.md` -- each covering half a
    dozen modules), an area overview (`cdc.md`, `math_library.md`) or a status
    page has no single module to have Parameters and Ports for, and holding it
    to the module template produces a failure nobody can act on. Twenty-six
    pages were in that state.

    Judged by whether `<stem>.sv` exists anywhere under rtl/ or projects/,
    which is a fact about the tree rather than a naming convention.
    """
    import os
    stem = os.path.splitext(os.path.basename(path))[0]
    for root in ('rtl', 'projects'):
        for _dir, _sub, files in os.walk(root):
            if f'{stem}.sv' in files:
                return True
    return False


def headings(path):
    out = []
    for line in open(path, errors='ignore').read().splitlines():
        if re.match(r'^##\s', line):
            out.append(re.sub(r'^##\s+', '', line).strip())
    return out


def report(area):
    files = [f for f in sorted(glob.glob(os.path.join(area, '*.md')))
             if os.path.basename(f) not in SKIP
             and not os.path.basename(f).endswith(SKIP_SUFFIX)
             and not os.path.basename(f).startswith(SKIP_PREFIX)]
    skipped_nonmodule = [f for f in files if not is_module_page(f)]
    files = [f for f in files if is_module_page(f)]
    if not files:
        return
    conform = 0
    missing = collections.Counter()
    unknown = collections.Counter()
    aliased = collections.Counter()
    for f in files:
        hs = headings(f)
        norm = {ALIASES.get(h, h) for h in hs}
        for h in hs:
            if h in ALIASES:
                aliased[f'{h} -> {ALIASES[h]}'] += 1
            elif h not in CANONICAL:
                unknown[h] += 1
        gaps = [h for h in REQUIRED if h not in norm]
        for h in gaps:
            missing[h] += 1
        if not gaps and not any(h not in CANONICAL for h in hs):
            conform += 1
    n = len(files)
    pct = 100.0 * conform / n
    print(f'\n{area}  --  {conform}/{n} pages conformant ({pct:.0f}%)')
    if skipped_nonmodule:
        names = ', '.join(os.path.basename(f) for f in skipped_nonmodule)
        print(f'  not module pages, spine not applied: {names}')
    if missing:
        print('  missing required sections:')
        for h, c in missing.most_common():
            print(f'     {h:<26} absent from {c}/{n}')
    if aliased:
        print('  renameable (same section, different name):')
        for h, c in aliased.most_common(8):
            print(f'     {h:<50} x{c}')
    if unknown:
        print('  unrecognised headings (decide: alias, or leave page-specific):')
        for h, c in unknown.most_common(8):
            print(f'     {h:<40} x{c}')


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        return 0
    for a in args:
        if os.path.isdir(a):
            report(a)
    return 0


if __name__ == '__main__':
    sys.exit(main())
