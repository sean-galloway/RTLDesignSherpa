#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate a validated GTKWave save file from a simulation dump.

Usage:
  gen_gtkw.py --dump <dump.fst|dump.vcd> --top <dut_top_module> \
      --out <view.gtkw> --title "<title>" --rebuild "<how to rebuild>" \
      [--curated <python file with CURATED dict>] [--auto-ports]

Pipeline: fst2vcd (if .fst) -> parse the $var header into the exact set of
dut-relative signal paths -> emit the .gtkw (house format, matching the
existing mem-ctrl-ip fub views) -> validate every emitted path against the
dump and fail nonzero on any missing path (the stream/rapids '0 missing
paths' rule).

Curated groups: <file> defines CURATED = { "<top_module>": [ (group, [(sig,
fmt), ...]), ...] } where sig is dut-relative (no top prefix) and fmt is 28
(digital) or 22 (hex/buses). Signals absent from the dump are skipped with a
warning, not emitted -- the file is a triage view, missing paths are defects
only when a curated signal the DUT must have is absent.
"""

import argparse
import os
import subprocess
import sys
import tempfile

FST2VCD = "/mnt/data/tools/oss-cad-suite/bin/fst2vcd"


def dump_to_vcd(dump):
    if dump.endswith(".vcd"):
        return dump, False
    tmp = tempfile.NamedTemporaryFile(suffix=".vcd", delete=False)
    tmp.close()
    with open(tmp.name, "w") as out:
        subprocess.run([FST2VCD, dump], stdout=out, stderr=subprocess.DEVNULL,
                       check=True)
    return tmp.name, True


def vcd_signals(vcd, top):
    """Return the set of dut-relative signal paths (top stripped)."""
    sigs = set()
    scope = []
    in_defs = False
    with open(vcd, "r", errors="replace") as f:
        for line in f:
            if line.startswith("$var"):
                p = line.split()
                name = p[4].split("[")[0]
                path = ".".join(scope + [name])
                if path.startswith(top + "."):
                    sigs.add(path[len(top) + 1:])
            elif line.startswith("$scope"):
                scope.append(line.split()[2])
            elif line.startswith("$upscope"):
                if scope:
                    scope.pop()
            elif line.startswith("$enddefinitions"):
                break
    return sigs


def auto_groups(sigs):
    """Fallback grouping for uncovered signals: handshake pairs, then buses,
    then the rest — by name heuristic."""
    def is_bus(s):
        return any(k in s for k in ("_i", "_o")) and any(
            c.isdigit() for c in s) is False and len(s) > 4

    hand, buses, rest = [], [], []
    for s in sorted(sigs):
        if s.endswith("_valid") or s.endswith("_ready"):
            hand.append(s)
        elif any(s.endswith(x) for x in ("_data", "_addr", "_id", "_bank",
                                         "_row", "_col", "_len", "_cnt",
                                         "_count", "_state", "_q", "_slot")):
            buses.append(s)
        else:
            rest.append(s)
    groups = []
    if hand:
        groups.append(("HANDSHAKES", [(s, 28) for s in hand]))
    if buses:
        groups.append(("BUSES/STATE", [(s, 22) for s in buses]))
    if rest:
        groups.append(("OTHER", [(s, 28) for s in rest]))
    return groups


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dump", required=True)
    ap.add_argument("--top", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--title", required=True)
    ap.add_argument("--rebuild", required=True,
                    help="command comment for rebuilding the dump")
    ap.add_argument("--curated", help="python file with CURATED dict")
    ap.add_argument("--view", help="view name when CURATED[top] is a dict")
    ap.add_argument("--auto-ports", action="store_true",
                    help="auto-group signals not covered by the curated list")
    args = ap.parse_args()

    curated = {}
    if args.curated:
        ns = {}
        with open(args.curated) as f:
            exec(compile(f.read(), args.curated, "exec"), ns)
        curated = ns.get("CURATED", {})

    vcd, tmp = dump_to_vcd(args.dump)
    try:
        sigs = vcd_signals(vcd, args.top)
    finally:
        if tmp:
            os.unlink(vcd)

    if not sigs:
        print(f"ERROR: no signals under top '{args.top}' in {args.dump}",
              file=sys.stderr)
        return 2

    top_groups = curated.get(args.top, [])
    if isinstance(top_groups, dict):
        if not args.view:
            print(f"ERROR: CURATED['{args.top}'] is a dict; pass --view",
                  file=sys.stderr)
            return 2
        if args.view not in top_groups:
            print(f"ERROR: view '{args.view}' not in CURATED['{args.top}']",
                  file=sys.stderr)
            return 2
        top_groups = top_groups[args.view]

    groups = []
    covered = set()
    for gname, members in top_groups:
        present = [(s, fmt) for s, fmt in members if s in sigs]
        for s, _ in members:
            if s not in sigs:
                print(f"warn: curated signal absent from dump: {s}",
                      file=sys.stderr)
        if present:
            groups.append((gname, present))
            covered.update(s for s, _ in present)

    if args.auto_ports:
        leftovers = [s for s in sorted(sigs - covered)
                     if not s.startswith("unused")]
        auto = auto_groups(set(leftovers))
        groups.extend(auto)

    missing = 0
    lines = []
    lines.append("[*]")
    lines.append(f"[*] GTKWave save file for {args.title}")
    lines.append("[*] Edit [dumpfile] to point at the scenario you want to view.")
    lines.append(f"[*] Default points at the dump built with: {args.rebuild}")
    dump_rel = os.path.relpath(args.dump, os.path.dirname(args.out))
    lines.append(f'[dumpfile] "{dump_rel}"')
    lines.append(f'[savefile] "{os.path.basename(args.out)}"')
    lines.append("[timestart] 0")
    lines.append("[size] 3456 1863")
    lines.append("[pos] -1 -1")
    lines.append("*-17.000000 " + "-1 " * 30)
    lines.append(f"[treeopen] {args.top}.")
    lines.append("[sst_width] 503")
    lines.append("[signals_width] 568")
    lines.append("[sst_expanded] 1")
    lines.append("[sst_vpaned_height] 983")
    for gname, members in groups:
        lines.append("")
        lines.append("@200")
        lines.append(f"-{gname}")
        for s, fmt in members:
            full = f"{args.top}.{s}"
            if s not in sigs:
                missing += 1
                print(f"ERROR missing path: {full}", file=sys.stderr)
                continue
            lines.append(f"@{fmt}")
            lines.append(full)

    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w") as f:
        f.write("\n".join(lines) + "\n")

    n = sum(len(m) for _, m in groups)
    print(f"{args.out}: {n} signals, {len(groups)} groups, "
          f"{len(sigs)} in dump, missing={missing}")
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
