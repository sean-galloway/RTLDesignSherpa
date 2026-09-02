#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: TestDutFamily
# Purpose: Catch a test that elaborates another protocol family's RTL
#
# Documentation: vault/handbook/dv/test-structure.md
# Subsystem: dv
#
# Author: sean galloway
# Created: 2026-09-01
"""Fail when `test_<family>_*.py` elaborates a DUT from a different family.

`test_axil5_master_rd.py` drove `axil4_master_rd` for five days and the suite
reported green the whole time, because a passing test says nothing about WHICH
module passed. It began when there was no AXI5-Lite RTL to drive, and survived
the RTL landing because the port that recreated the family only created the
tests that were missing -- the one already there was never re-examined.

The check is deliberately narrow. A test may legitimately drive a `_stub`, a
`tb_*` pair wrapper, or a shared module it is only probing an aspect of
(`test_axi_monitor_addr_filter` drives `axi_monitor_base`), so name-vs-DUT is
too noisy to gate on. Crossing a PROTOCOL FAMILY is not that: an axil5 test
elaborating axil4 RTL is either a bug or a deliberate equivalence run.

A file that names both families is the declared exemption
(`test_axil5_axil4_equivalence.py`) -- the intent is then in the filename,
where the next reader sees it.
"""
import pathlib
import re
import subprocess
import sys

FAMILIES = ('axil4', 'axil5', 'axis4', 'axis5', 'axi4', 'axi5',
            'apb4', 'apb5', 'gaxi')
RE_DUT = re.compile(r'dut_name\s*=\s*["\']([\w]+)["\']')


def family(name: str):
    """Longest matching family prefix, so axil5 wins over axi5.

    `axis_*` maps to axis4. The AXI5-Stream modules are named `axis5_master.sv`
    and friends, but the AXI4-Stream ones are bare `axis_master.sv` with no `4`
    -- an inconsistency in rtl/amba/axis4/. Without this mapping `family()`
    returns None for every axis4 module, those tests are SKIPPED, and this
    checker reports a clean run over a family it cannot see. It did exactly
    that until 2026-09-02.

    This is a workaround for the naming, not an endorsement of it. Renaming the
    four axis4 modules to `axis4_*` touches ~104 files; when that happens, this
    special case should go.
    """
    for f in sorted(FAMILIES, key=len, reverse=True):
        if name.startswith(f + '_') or name == f:
            return f
    if name.startswith('axis_'):
        return 'axis4'
    return None


def main() -> int:
    root = pathlib.Path(subprocess.check_output(
        ['git', 'rev-parse', '--show-toplevel']).decode().strip())
    bad = []
    checked = 0
    for path in sorted(root.rglob('test_*.py')):
        parts = set(path.parts)
        if parts & {'.git', 'venv', '.claude', 'sim_build',
                    'local_sim_build', 'node_modules'}:
            continue
        stem = path.stem[len('test_'):]
        tf = family(stem)
        if tf is None:
            continue
        m = RE_DUT.search(path.read_text(errors='replace'))
        if not m:
            continue
        checked += 1
        df = family(m.group(1))
        if df is None or df == tf:
            continue
        # Declared exemption: the filename names the other family too.
        # Split on '_' rather than using \b -- \b does NOT break at an
        # underscore, so r'\baxil4\b' never matches inside
        # 'axil5_axil4_equivalence'. That exact trap cost a debugging
        # round earlier when r'\baxil4_master_rd\b' silently skipped
        # every '..._master_rd_mon' instantiation.
        if df in stem.split('_'):
            continue
        bad.append((path.relative_to(root), tf, m.group(1), df))

    for rel, tf, dut, df in bad:
        print(f"  {rel}: a {tf} test elaborates {dut} ({df} RTL) -- point it at "
              f"its own module, or name the file for both families if the "
              f"cross-family run is deliberate")
    print(f"\n{checked} family-named tests checked, {len(bad)} crossing a family")
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
