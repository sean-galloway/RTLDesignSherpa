#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DocExampleCheck
# Purpose: An instantiation example must name ports the module actually has
#
# Documentation: vault/handbook/authoring/module-doc-template.md
# Subsystem: authoring
"""Fail when a doc page's instantiation example names a port the RTL lacks.

Twenty-eight pages carried examples with invented ports -- `apb4_slave` shown
with `clk`/`resetn` when it has neither, `axi4_master_rd` with `NUM_MASTERS`
and `NUM_SLAVES`. A reader copying one gets code that does not compile.

These survived every qc and humanize round because no reviewer cross-checks an
example against the port list, and at least two were INTRODUCED by a humanize
round: a voice pass rewrote `bin_to_bcd`'s example into ports the module never
had. A voice pass is free to reword prose; it is not qualified to invent an
interface, and nothing was checking.

Checked by name presence in the module source, which is deliberately weak: it
will not catch a wrong width or a swapped connection, only a name that does not
exist at all. That is the class that actually appeared.
"""
import os
import re
import subprocess
import sys

RE_CONN = re.compile(r'^\s*\.(\w+)\s*\(', re.M)


def module_src(root, stem):
    for base in ('rtl', 'projects'):
        for d, _s, files in os.walk(base):
            if f'{stem}.sv' in files:
                p = os.path.join(d, f'{stem}.sv')
                return re.sub(r'//[^\n]*', '', open(p, errors='ignore').read())
    return None


def main() -> int:
    root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).decode().strip()
    os.chdir(root)
    bad = 0
    pages = 0
    doc_pages = 0
    # Index every module once, so a page can be checked against whatever module
    # its example actually instantiates rather than one guessed from the page
    # name. This is what lets the check reach projects/components, whose docs
    # are chaptered HAS/MAS books rather than per-module pages -- 109 of those
    # files carry SystemVerilog blocks and none was reachable before.
    index = {}
    for base in ('rtl', 'projects'):
        for d, _s, files in os.walk(base):
            for fn in files:
                if fn.endswith('.sv'):
                    index.setdefault(fn[:-3], os.path.join(d, fn))

    # An instantiation starts either `mod #(` or `mod u_name (`. Matching
    # only the first form meant a parameterless instantiation was not seen
    # as a new one, and its connections were blamed on the module above it
    # -- which is how `sync_pulse`'s ports were reported against
    # `cdc_synchronizer`.
    RE_INST = re.compile(
        r'^\s*([a-z][a-z0-9_]{3,})\s*(?:#\s*\(|u_\w+\s*\()', re.M)
    roots = ['docs'] + [os.path.join(r, 'docs')
                        for r, ds, _f in os.walk('projects') if 'docs' in ds]
    seen = set()
    # Beside-code CLAUDE.md is in NO docs/ tree, so neither walk reached it --
    # and it is the file an agent reads first. Ten fabricated examples sat in
    # rtl/amba/CLAUDE.md under this very gate until 2026-09-25 (amba BUG-001).
    page_list = []
    for root in roots:
        for d, _s, files in os.walk(root):
            page_list += [os.path.join(d, fn) for fn in sorted(files)
                          if fn.endswith('.md')]
    page_list += [q for q in subprocess.check_output(
        ['git', 'ls-files', '*CLAUDE.md'], text=True).split() if os.path.isfile(q)]
    for path in page_list:
        if True:
            if not path.endswith('.md'):
                continue
            if path in seen:
                continue
            seen.add(path)
            doc_pages += 1
            text = open(path, errors='ignore').read()
            for blk in re.findall(r'```systemverilog(.*?)```', text, re.S):
                # Split the block at each instantiation so a connection is
                # attributed to the module it actually belongs to. A block with
                # two instantiations otherwise blames each module for the
                # other's ports -- which flagged correct pages and nearly had me
                # "fix" documentation that was right.
                starts = [(m.start(), m.group(1)) for m in RE_INST.finditer(blk)]
                for k, (pos, mod) in enumerate(starts):
                    if mod not in index:
                        continue
                    end = starts[k + 1][0] if k + 1 < len(starts) else len(blk)
                    seg = blk[pos:end]
                    src = re.sub(r'//[^\n]*', '',
                                 open(index[mod], errors='ignore').read())
                    miss = [c for c in RE_CONN.findall(seg)
                            if not re.search(rf'\b{re.escape(c)}\b', src)]
                    if miss:
                        bad += 1
                        print(f'  {path}: {mod} example names '
                              f'{", ".join(sorted(set(miss))[:5])}')

    for d, _s, files in os.walk('docs/markdown'):
        for fn in sorted(files):
            if not fn.endswith('.md'):
                continue
            path = os.path.join(d, fn)
            src = module_src(root, fn[:-3])
            if src is None:
                continue
            pages += 1
            text = open(path, errors='ignore').read()
            m = re.search(r'## Usage Examples(.*?)(?=\n## |\Z)', text, re.S)
            if not m:
                continue
            missing = [c for c in RE_CONN.findall(m.group(1))
                       if not re.search(rf'\b{re.escape(c)}\b', src)]
            if missing:
                bad += 1
                names = ', '.join(sorted(set(missing))[:6])
                print(f'  {path}: example names ports the module lacks -- {names}')
    # BOTH walks, because the old line counted only the per-module pages: it
    # read 241 while the first walk was silently covering 939 more. A gate that
    # stopped scanning the component books would have printed the same 241.
    print(f'\n{doc_pages} doc pages + {pages} module pages checked, '
          f'{bad} with a fabricated example')
    # One known finding in projects/components is tracked as TASK-077 and is
    # being fixed by hand -- a whole-block regeneration drops the other
    # instantiations in the same block. Was 9; the stream clocks-and-reset page
    # (three findings) was fixed 2026-09-15, and the rest had already been
    # fixed by their owners. The one left is rapids_core_beats, whose page
    # documents three interfaces the module does not have at all, so it needs
    # the rapids owner rather than a rename. Ratchet: this must not GROW.
    # Measured against a clean HEAD checkout, NOT the working tree. A dirty
    # tree carries other sessions' uncommitted fixes, so a baseline taken
    # there is lower than what CI sees -- I set 4 that way and CI failed with
    # 9. `git worktree add --detach /tmp/chk HEAD` and run it there.
    # 2026-09-25: scope widened to beside-code CLAUDE.md, which surfaced three
    # MORE findings, all the same gaxi_fifo_sync shape that amba BUG-001 fixed
    # (the module takes axi_aclk/axi_aresetn/wr_*/rd_*; the docs connect
    # i_clk/i_rst_n/i_valid/i_data/i_ready). All three are FIXED (d2062a097):
    #   projects/components/dmas/rapids/CLAUDE.md  x2  -- fixed by rapids owner
    #   projects/components/dmas/stream/CLAUDE.md  x1  -- fixed by stream owner
    # so the ratchet drops 4 -> 1. Measured in a detached worktree at that HEAD,
    # not the working tree, per the warning above.
    #
    # The one left is the rapids_core_beats MAS page (TASK-077), and it is
    # bigger than the printed message suggests. The message truncates to five
    # names (sorted(set(miss))[:5]); the page actually carries 25 fabricated
    # connections out of 43 in its Integration Example, plus ~40 more in its
    # port TABLES, which this gate never inspects because RE_CONN only matches
    # .port(net) connection syntax. Real names: sink write is m_axi_wr_*,
    # source read m_axi_rd_*, fill s_axis_t*, drain m_axis_t*, MonBus
    # mon_valid/mon_ready/mon_packet, status src_/snk_system_idle -- there is
    # no error_flags port at all.
    #
    # Known blind spot, found while fixing the above: the check greps the whole
    # MODULE SOURCE, not just its port list, so an internal wire name can mask a
    # fabricated port name. all_channels_idle and scheduler_idle pass on the
    # rapids_core_beats page for exactly that reason, despite neither being a
    # port. Tightening it to the port list would raise the count.
    BASELINE = 1
    if bad > BASELINE:
        print(f'  FAIL: {bad} exceeds the baseline of {BASELINE} (TASK-077)')
        return 1
    if bad < BASELINE:
        print(f'  baseline can be lowered to {bad} -- edit BASELINE')
    return 0


if __name__ == '__main__':
    sys.exit(main())
