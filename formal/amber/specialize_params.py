#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Specialize an sv2v-flat for yosys bind-based formal proofs.

Yosys's bind statement only fires when the bind target is a truly
PARAMETERLESS module: a target with parameters (even instantiated without
overrides, which normally avoids a $paramod derivation) never receives the
bound instance -- silently, with the properties dropped from the proof. That
vacuous-pass hole is documented in the Task 13 report.

This transform closes it at flat-generation time: in each --module section,
every `parameter` declaration line is deleted and the parameter name is
substituted with a concrete value (--param NAME=VAL; repeat for each
parameter of the module). A name preceded by '.' (a named override on a
submodule instance, e.g. .ADDR_WIDTH(...)) is left alone: modules not listed
stay parameterized and keep receiving their overrides. Derived localparams
(e.g. SET_INDEX_WIDTH = $clog2(SETS)) are left in place -- they now fold to
constants. Sections of unlisted modules pass through byte-identical.

A parameter still referenced (bare) after substitution is a hard error: the
flat would silently differ from the RTL.

Usage:
  specialize_params.py IN OUT --param SETS=16 --param WAYS=2 \
      --module amber_control
"""
from __future__ import annotations

import re
import sys

MODULE_RE = re.compile(r"^module\s+(\w+)\s*\(", re.M)
PARAM_RE = re.compile(
    r"^\s*parameter\s+(?:signed|unsigned)?\s*(?:\[[^\]]*\]\s*)?(\w+)\s*=\s*([^;]+);\s*$")


def main() -> int:
    args = sys.argv[1:]
    if len(args) < 2:
        print(__doc__)
        return 2
    in_path, out_path, args = args[0], args[1], args[2:]

    params: dict[str, str] = {}
    modules: list[str] = []
    i = 0
    while i < len(args):
        if args[i] == "--param":
            name, val = args[i + 1].split("=", 1)
            params[name] = val
            i += 2
        elif args[i] == "--module":
            modules.append(args[i + 1])
            i += 2
        else:
            print(f"unknown argument {args[i]!r}", file=sys.stderr)
            return 2
    if not modules:
        print("at least one --module is required", file=sys.stderr)
        return 2

    text = open(in_path).read() if in_path != "-" else sys.stdin.read()

    # split into (preamble, [(module_name, section_text), ...]): sections
    # include the `module ...` line through `endmodule`.
    marks = [(m.start(), m.group(1)) for m in MODULE_RE.finditer(text)]
    if not marks:
        print("error: no modules found", file=sys.stderr)
        return 1
    chunks: list[tuple[str | None, str]] = [(None, text[:marks[0][0]])]
    for idx, (pos, name) in enumerate(marks):
        end = marks[idx + 1][0] if idx + 1 < len(marks) else len(text)
        chunks.append((name, text[pos:end]))

    out: list[str] = []
    for name, chunk in chunks:
        if name is None or name not in modules:
            out.append(chunk)
            continue

        # collect + drop parameter declaration lines
        kept: list[str] = []
        decls: list[str] = []
        for line in chunk.splitlines(keepends=True):
            pm = PARAM_RE.match(line)
            if pm:
                pname = pm.group(1)
                if pname not in params:
                    print(f"error: parameter {pname!r} of module {name} has "
                          f"no --param value (default {pm.group(2)!r})",
                          file=sys.stderr)
                    return 1
                decls.append(pname)
            else:
                kept.append(line)
        chunk = "".join(kept)

        # substitute within this section only; '.'-prefixed names (named
        # overrides for still-parameterized submodules) are preserved.
        # A parameter may be legitimately unreferenced in the body (e.g.
        # LINE_BYTES in amber_snoop_resp); the check below still guards
        # genuinely unresolved bare uses.
        for pname in decls:
            chunk = re.sub(rf"(?<![\w.]){re.escape(pname)}\b", params[pname],
                           chunk)

        for pname in decls:
            if re.search(rf"(?<![\w.]){re.escape(pname)}\b", chunk):
                print(f"error: unresolved parameter {pname!r} remains in "
                      f"module {name}", file=sys.stderr)
                return 1
        out.append(chunk)

    open(out_path, "w").write("".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main())
