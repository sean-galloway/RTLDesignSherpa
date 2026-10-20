#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Fail if any formal Makefile builds a *_flat.v without make/formal_flat.mk.

    check_formal_flat_sources.py [--root DIR]

Owner rule (2026-10-19): every formal flat's source list comes from the
DUT's own filelist via bin/flatten_filelist.py, never a hand-listed
SRCS/DEPS (vault/handbook/dv/formal.md). On that date 140 of 141 flat
Makefiles hand-listed, and one reset_sync added inside three blocks broke
twelve proofs. This is the gate that keeps the rule from rotting: a
Makefile that names a *_flat.v must include make/formal_flat.mk.
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

INCLUDE = re.compile(r"^\s*-?include\s+\S*make/formal_flat\.mk\s*$", re.M)
BUILDS_FLAT = re.compile(r"\b\w+_flat\.v\b")


def offenders(root: pathlib.Path) -> list[pathlib.Path]:
    """Formal Makefiles that build a flat but do not use the shared include."""
    bad = []
    for mk in sorted((root / "formal").rglob("Makefile")):
        text = mk.read_text(errors="replace")
        code = "\n".join(l for l in text.splitlines() if not l.lstrip().startswith("#"))
        if BUILDS_FLAT.search(code) and not INCLUDE.search(code):
            bad.append(mk.relative_to(root))
    return bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", type=pathlib.Path,
                    default=pathlib.Path(__file__).resolve().parents[1])
    args = ap.parse_args()
    bad = offenders(args.root)
    for mk in bad:
        print(f"HANDLISTED {mk}: builds a *_flat.v without make/formal_flat.mk")
    print(f"formal flat sources: {len(bad)} hand-listed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
