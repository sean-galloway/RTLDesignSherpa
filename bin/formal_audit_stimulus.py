#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Find formal harnesses whose DUT INPUTS are declared but never driven.

A harness that writes `logic foo;` and wires it to a DUT input has not
driven anything. `opt -full` folds the undriven net to a constant before
`setundef -expose` can free it, so that input is pinned for the whole proof.

Two ways that hurts, one loud and one silent:

  * LOUD -- a cover that needs the input goes unreachable, and the cover task
    fails whatever the RTL does. arbiter_rr_pwm_monbus could not reach
    cp_monbus because cfg_mon_enable was never driven (fixed 2026-09-11).
  * SILENT -- the proof passes with that input held at a constant, so every
    property is only proved for one value of it. apb4_master proves and
    covers today with cmd_paddr and cmd_pwrite pinned: nothing
    payload-dependent is being checked, and the run looks green.

The fix is `(* anyseq *)` on the declaration (or `(* anyconst *)` where the
value must hold across the trace), not a wider BMC depth.

    python3 bin/formal_audit_stimulus.py
"""
import re, pathlib
ROOT = pathlib.Path("/mnt/data/github/RTLDesignSherpa")

rtl = {}
for f in (ROOT/"rtl").rglob("*.sv"):
    if "/OLD/" in str(f):
        continue
    t = f.read_text(errors="replace")
    for m in re.finditer(r'^\s*module\s+(\w+)\b(.*?)^\);', t, re.M|re.S):
        rtl.setdefault(m.group(1), m.group(2))

def dirs_of(mod):
    body = rtl.get(mod)
    if body is None:
        return {}
    return {m.group(2): m.group(1) for m in
            re.finditer(r'^\s*(input|output|inout)\b[^,;]*?(\w+)\s*(?:,|$)', body, re.M)}

hits = []
for area in ("amba","cdc","common","integ_common"):
    for h in sorted((ROOT/"formal"/area).glob("*/formal_*.sv")):
        s = h.read_text(errors="replace")
        s_nc = re.sub(r'//.*', '', s)
        # DUT module: the instantiated module that we know from rtl/
        insts = {m.group(1) for m in
                 re.finditer(r'^\s*([a-z_]\w*)\s*(?:#\s*\([\s\S]*?\))?\s*\w+\s*\(', s_nc, re.M)
                 if m.group(1) in rtl}
        if not insts:
            continue
        dirs = {}
        for i in insts:
            dirs.update(dirs_of(i))
        feeds = {m.group(2): m.group(1) for m in
                 re.finditer(r'\.(\w+)\s*\(\s*([A-Za-z_]\w*)\s*\)', s_nc)
                 if dirs.get(m.group(1)) == "input"}
        bad = []
        for sig, port in feeds.items():
            decl = re.search(rf'^\s*(\(\*[^)]*\*\)\s*)?(?:logic|reg|wire)\s+(?:\[[^\]]*\]\s*)?{sig}\s*;',
                             s_nc, re.M)
            if not decl:
                continue                      # declared with an initialiser, or a port
            if decl.group(1):
                continue                      # already anyseq/anyconst
            # driven anywhere?
            if re.search(rf'(^|[^.\w]){sig}\s*(<=|=[^=])', s_nc, re.M):
                continue
            if re.search(rf'assign\s+{sig}\b', s_nc):
                continue
            bad.append(sig)
        if bad:
            hits.append((f"{area}/{h.parent.name}", len(bad), sorted(bad)[:6]))

print(f"harnesses with UNDRIVEN DUT inputs: {len(hits)}")
for name, n, sample in sorted(hits, key=lambda x: -x[1]):
    print(f"  {name:44s} {n:3d}  e.g. {', '.join(sample)}")
