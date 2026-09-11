#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Find formal harnesses whose DUT INPUTS are declared but never driven.

A harness that writes `logic foo;` and wires it to a DUT input has not
driven anything. Whether that PINS the input depends on the task's script:

  * plain `prep` (sby's default) runs `setundef -undriven -anyseq`, so the
    net is FREE -- no problem;
  * a custom script that runs an `opt` pass BEFORE any `setundef` folds the
    undriven net to a constant first, and the input is pinned for the whole
    proof.

So this audit only reports harnesses whose script folds. (An earlier version
reported every undriven net, which flagged free inputs as pinned -- corrected
2026-09-11 after measuring it.)

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

def script_folds(task_dir: pathlib.Path) -> bool:
    """True when the task's sby script runs an opt pass before any setundef.

    That ORDER is what pins an undriven net. sby's own plain `prep` runs
    `setundef -undriven -anyseq`, so in a task that uses plain prep an
    undriven or unconnected input is FREE, not pinned -- measured 2026-09-11:
    the axi_master_wr_splitter harness reaches both fub_awaddr 0x40 and 0x80
    with those nets undriven. Flagging such a task is a false positive.
    """
    for sby in task_dir.glob("*.sby"):
        m = re.search(r'^\[script\]\s*$(.*?)(?=^\[|\Z)', sby.read_text(errors="replace"), re.M | re.S)
        if not m:
            continue
        ls = [l.strip() for l in m.group(1).splitlines()
              if l.strip() and not l.strip().startswith("#")]
        oi = next((i for i, l in enumerate(ls) if re.match(r'opt(\s|$|_expr|_clean)', l)), None)
        si = next((i for i, l in enumerate(ls) if l.startswith("setundef")), None)
        if oi is not None and (si is None or oi < si):
            return True
    return False


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
        # Each INSTANCE separately. Port directions must come from that
        # instance's own module: bin2gray has an INPUT named `binary` and
        # gray2bin an OUTPUT of the same name, and merging directions across
        # module types flagged gray2bin's output as a pinned input.
        feeds, inst_driven, dirs = {}, set(), {}
        for m in re.finditer(r'^\s*([a-z_]\w*)\s*(?:#\s*\([\s\S]*?\))?\s*\w+\s*\(([\s\S]*?)\);',
                             s_nc, re.M):
            mod, conns = m.group(1), m.group(2)
            if mod not in rtl:
                continue
            d = dirs_of(mod)
            for pm in re.finditer(r'\.(\w+)\s*\(\s*([A-Za-z_]\w*)\s*\)', conns):
                port, sig = pm.group(1), pm.group(2)
                dirs.setdefault(port, d.get(port))
                if d.get(port) == "input":
                    feeds[sig] = port
                elif d.get(port) == "output":
                    # A net one instance drives is not undriven just because
                    # another instance reads it (roundtrip harnesses do this).
                    inst_driven.add(sig)
        if not feeds and not dirs:
            continue
        # Inputs the instantiation never connects AT ALL. Same effect as an
        # undriven net and easier to miss, because nothing in the harness
        # mentions the signal. The four axi4 *_mon harnesses connected 16 of
        # 35 cfg_ inputs; the three left out were the packet-class enables, so
        # no class could be turned on and cp_monbus_valid was unreachable.
        connected = {m.group(1) for m in re.finditer(r'\.(\w+)\s*\(', s_nc)}
        unconnected = sorted(p for p, d in dirs.items()
                             if d == "input" and p not in connected)
        # dirs only holds ports that appear in SOME connection; recompute the
        # full input set from each instantiated module to catch ports never
        # mentioned at all (the axi4 *_mon case).
        for m in re.finditer(r'^\s*([a-z_]\w*)\s*(?:#\s*\([\s\S]*?\))?\s*\w+\s*\(([\s\S]*?)\);',
                             s_nc, re.M):
            if m.group(1) not in rtl:
                continue
            named = set(re.findall(r'\.(\w+)\s*\(', m.group(2)))
            for port, d in dirs_of(m.group(1)).items():
                if d == "input" and port not in named and port not in unconnected:
                    unconnected.append(port)
        unconnected = sorted(set(unconnected))
        bad = []
        for sig, port in feeds.items():
            decl = re.search(rf'^\s*(\(\*[^)]*\*\)\s*)?(?:logic|reg|wire)\s+(?:\[[^\]]*\]\s*)?{sig}\s*;',
                             s_nc, re.M)
            if not decl:
                continue                      # declared with an initialiser, or a port
            if decl.group(1):
                continue                      # already anyseq/anyconst
            if sig in inst_driven:
                continue                      # driven by an instance output
            # driven anywhere?
            if re.search(rf'(^|[^.\w]){sig}\s*(<=|=[^=])', s_nc, re.M):
                continue
            if re.search(rf'assign\s+{sig}\b', s_nc):
                continue
            bad.append(sig)
        if (bad or unconnected) and not script_folds(h.parent):
            continue          # plain prep frees these nets -- not pinned
        if bad or unconnected:
            hits.append((f"{area}/{h.parent.name}", len(bad), sorted(bad)[:5],
                         len(unconnected), unconnected[:5]))

print(f"harnesses with pinned DUT inputs: {len(hits)}")
print(f"{'harness':44s} {'undriven':>8s} {'unconn':>7s}  examples")
for name, n, sample, nu, usample in sorted(hits, key=lambda x: -(x[1] + x[3])):
    ex = ", ".join(sample or usample)
    print(f"  {name:44s} {n:6d} {nu:7d}  {ex}")
print()
print("undriven = declared in the harness, wired to a DUT input, never assigned")
print("unconn   = a DUT input the instantiation does not connect at all")
print("Reported only where the task's script runs opt before setundef --")
print("sby's plain prep frees undriven nets, so those tasks are not pinned.")
