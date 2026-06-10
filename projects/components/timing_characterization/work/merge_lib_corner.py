#!/usr/bin/env python3
"""Merge ASAP7 group Liberty files for one PVT corner.

Usage: merge_lib_corner.py {TT|FF|SS}

Mirrors merge_lib.py but parameterized by corner.  Output file:
  ~/eda/asap7_merged/asap7sc7p5t_RVT_{corner}_nldm.lib
"""
from __future__ import annotations
import re
import sys
from pathlib import Path

ROOT = Path.home() / "eda" / "asap7_merged"
GROUPS = ["SIMPLE", "INVBUF", "AO", "OA", "SEQ"]
FIRST_CELL_RE = re.compile(r"^\s*cell\s*\(", re.MULTILINE)


def find_group_lib(group: str, corner: str) -> Path:
    cands = sorted(ROOT.glob(f"asap7sc7p5t_{group}_RVT_{corner}_nldm_*.lib"))
    if not cands:
        raise SystemExit(f"missing: {group}/{corner}")
    return cands[0]


def split_lib(path: Path) -> tuple[str, str]:
    text = path.read_text()
    m = FIRST_CELL_RE.search(text)
    if not m:
        raise RuntimeError(f"{path.name}: no `cell (` found")
    preamble = text[: m.start()]
    rest = re.sub(r"\n\s*\}\s*\Z", "\n", text[m.start():])
    return preamble, rest


def main() -> None:
    if len(sys.argv) != 2 or sys.argv[1] not in ("TT", "FF", "SS"):
        raise SystemExit("usage: merge_lib_corner.py {TT|FF|SS}")
    corner = sys.argv[1]
    out = ROOT / f"asap7sc7p5t_RVT_{corner}_nldm.lib"
    pieces: list[str] = []
    counts: dict[str, int] = {}
    for i, g in enumerate(GROUPS):
        p = find_group_lib(g, corner)
        pre, cells = split_lib(p)
        counts[p.name] = len(re.findall(r"^\s*cell\s*\(", cells, re.MULTILINE))
        if i == 0:
            pieces.append(pre)
        pieces.append(cells)
    pieces.append("}\n")
    out.write_text("".join(pieces))
    total = sum(counts.values())
    print(f"wrote {out}  ({total} cells)")
    for n, c in counts.items():
        print(f"  {c:5d}  {n}")


if __name__ == "__main__":
    main()
