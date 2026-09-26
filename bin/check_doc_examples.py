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

# A port/signal reference TABLE, outside any fence. The header decides: a table
# whose first column is Port/Signal/Signal Name lists interface names.
RE_TBL_HDR = re.compile(r'^\|\s*(Port|Signal Name|Signal)\s*\|', re.I)
RE_TBL_ROW = re.compile(r'^\|\s*`?([A-Za-z_]\w*)`?\s*\|')
def name_in_src(name, src_low):
    """Is `name` an interface name of this module?

    Deliberately permissive about prefix and case, because a correct page may
    cite the PROTOCOL name: an AXI-Stream table says TDATA where the port is
    m_axis_tdata, an APB table says PRESETn where the port is presetn. Treating
    those as defects would mean editing correct documentation to satisfy a
    defect in this script. The suffix arm needs >= 3 characters -- at 4 it
    called axis4_master's TID fabricated while absolving TDATA, which is a fact
    about the threshold and not about the page.
    """
    n = name.lower()
    if re.search(rf'\b{re.escape(n)}\b', src_low):
        return True
    return len(n) >= 3 and bool(re.search(rf'\b\w*{re.escape(n)}\b', src_low))


def table_names(text):
    """[(lineno, name)] from port tables, skipping fenced blocks.

    Fences matter: an ASCII block diagram draws rows like `|   pclk   |-----+`
    that match the row pattern exactly.
    """
    out, fence, intbl = [], False, False
    for i, line in enumerate(text.split('\n'), 1):
        if line.lstrip().startswith('```'):
            fence, intbl = not fence, False
            continue
        if fence:
            continue
        if RE_TBL_HDR.match(line):
            intbl = True
            continue
        if intbl:
            if not line.startswith('|'):
                intbl = False
                continue
            if set(line.replace('|', '').strip()) <= set('-: '):
                continue          # the |---|---| separator row
            m = RE_TBL_ROW.match(line)
            if m:
                out.append((i, m.group(1)))
    return out


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
    tbl_rows_seen = [0]
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
            # ...and the PORT TABLES on the same page, which used to be invisible.
            src_low = src.lower()
            tbl_rows_seen[0] += len(tbl := table_names(text))
            tmiss = sorted({n for _ln, n in tbl if not name_in_src(n, src_low)})
            if tmiss:
                bad += 1
                print(f'  {path}: port TABLE names ports the module lacks -- '
                      f'{", ".join(tmiss[:6])}')
    # BOTH walks, because the old line counted only the per-module pages: it
    # read 241 while the first walk was silently covering 939 more. A gate that
    # stopped scanning the component books would have printed the same 241.
    print(f'\n{doc_pages} doc pages + {pages} module pages checked '
          f'({tbl_rows_seen[0]} port-table rows), '
          f'{bad} with a fabricated example')
    if tbl_rows_seen[0] == 0:
        print('  FAILED: read no port-table rows at all -- the table scan is '
              'broken, not the tree', file=sys.stderr)
        return 1
    # One known finding in projects/components is tracked as amba TASK-077 and is
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
    # amba TASK-077 is FIXED (ff57ee35f), so the ratchet reaches 0. That page
    # had far more wrong with it than the printed message suggested: the message
    # truncates to five names (sorted(set(miss))[:5]), while the page carried 25
    # fabricated connections out of 43 in its Integration Example AND 42 of 55
    # fabricated signals in its port tables. It was rewritten against the module:
    # sink write is m_axi_wr_*, source read m_axi_rd_*, ingress s_axis_t*,
    # egress m_axis_t*, MonBus mon_valid/mon_ready/mon_packet, descriptor AXI is
    # TWO masters (src_/snk_m_axi_desc_*), status is per half
    # (src_/snk_system_idle) -- and there is no error_flags port at all.
    #
    # AT ZERO NOW. Any new finding fails the gate immediately, which is the
    # point: there is no longer a backlog to hide in.
    #
    # Port TABLES are read now (2026-09-25), on per-module pages ONLY -- the page
    # filename names the module, so attribution is certain. 5515 rows across 241
    # pages, zero findings: the port tables on module pages were already clean,
    # which is worth stating because the comment this replaces implied otherwise.
    # The tbl_rows_seen guard above exists so "zero findings" can never mean
    # "read no tables".
    #
    # THREE attribution arms were tried and REJECTED. All three are recorded
    # because each looked reasonable and each produced confident false findings:
    #
    # 1. "The one module the page mentions", when the filename does not resolve.
    #    It blames every table on whatever module appears in some instantiation
    #    example: rapids/CLAUDE.md's scheduler config table and stream's
    #    02_port_list.md were both blamed on gaxi_fifo_sync. 153 findings,
    #    almost entirely misattribution.
    # 2. Any startswith() sibling as a module "family". It blamed
    #    math_multiplier_basic.md against math_multiplier_basic_cell (a sub-cell,
    #    ports i_i/i_j/i_c/i_p) and called i_multiplier/i_multiplicand/ow_product
    #    fabricated; they exist in 32+ files.
    # 3. A RESTRICTED family arm -- siblings only if every suffix is wr/rd/NNN.
    #    This looked safe and was not. Its single finding across five pages was
    #    axi4_dwidth_converter.md, which is a PLANNED-DESIGN page: it states
    #    "Location: Not implemented", "Status: Planned - no RTL in this
    #    repository", and names AW_/W_/B_/AR_/R_FIFO_DEPTH while explicitly
    #    saying none of them exist in RTL yet. Its _wr and _rd siblings are two
    #    different shipping modules with SKID_DEPTH_* parameters, not variants of
    #    a bidirectional parent. Acting on that finding meant rewriting a
    #    deliberate design document to satisfy this script -- the exact failure
    #    the module docstring warns about. axi4_cdc.md has the same shape.
    #
    # The lesson is narrow and worth keeping: a page documenting a module that
    # does not exist is not a page with fabricated ports. Only compare a table
    # against RTL when the page and the module are the SAME subject, and the
    # filename is currently the only evidence of that strong enough to gate on.
    #
    # So the CHAPTERED BOOKS (projects/**/docs/**) still have their tables
    # unchecked: 119 of 367 table-bearing pages have no attributable module, and
    # that is where the known damage is -- amba TASK-077's page carried 42 of 55
    # table signals fabricated. Closing that needs an explicit per-page module
    # declaration (a `Module:` field), not a cleverer guess from this side.
    BASELINE = 0
    if bad > BASELINE:
        print(f'  FAIL: {bad} exceeds the baseline of {BASELINE} -- a doc example\n          names a port its module does not have. The backlog this ratchet\n          tracked (amba TASK-077) is CLOSED and the floor is 0, so any\n          finding here is NEW.')
        return 1
    if bad < BASELINE:
        print(f'  baseline can be lowered to {bad} -- edit BASELINE')
    return 0


if __name__ == '__main__':
    sys.exit(main())
