#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Fail if a formal Makefile builds a *_flat.v without make/formal_flat.mk,
or puts that flat anywhere but its own unit directory.

    check_formal_flat_sources.py [--root DIR]

Owner rule (2026-10-19): every formal flat's source list comes from the
DUT's own filelist via bin/flatten_filelist.py, never a hand-listed
SRCS/DEPS (vault/handbook/dv/formal.md). On that date 140 of 141 flat
Makefiles hand-listed, and one reset_sync added inside three blocks broke
twelve proofs. This is the gate that keeps the rule from rotting: a
Makefile that names a *_flat.v must include make/formal_flat.mk.

FLAT must also name a file in the unit directory (`foo_flat.v` or
`$(CURDIR)/foo_flat.v`), never one in a subdirectory. Proof tooling owns
subdirectories: riscv-formal's genchecks.py rmtree's checks/, and sby
recreates its workdir. kestrel's flat lived in checks/rtl_v/, was converted,
then deleted before sby ran, and all 42 checks failed "kestrel_flat.v not
found" (2026-10-20) while the include rule above passed.
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

INCLUDE = re.compile(r"^\s*-?include\s+\S*make/formal_flat\.mk\s*$", re.M)
BUILDS_FLAT = re.compile(r"\b\w+_flat\.v\b")
FLAT_VAR = re.compile(r"^\s*FLAT\s*:?=\s*(\S+)", re.M)
UNIT_DIR_PREFIXES = ("$(CURDIR)/", "${CURDIR}/")


def _flat_outside_unit_dir(value: str) -> bool:
    """True when a FLAT value has a directory part other than $(CURDIR)."""
    for prefix in UNIT_DIR_PREFIXES:
        if value.startswith(prefix):
            value = value[len(prefix):]
            break
    return "/" in value


def offenders(root: pathlib.Path) -> list[tuple[str, pathlib.Path, str]]:
    """(kind, Makefile, FLAT) for every formal Makefile breaking a flat rule."""
    bad = []
    for mk in sorted((root / "formal").rglob("Makefile")):
        text = mk.read_text(errors="replace")
        code = "\n".join(l for l in text.splitlines() if not l.lstrip().startswith("#"))
        rel = mk.relative_to(root)
        if BUILDS_FLAT.search(code) and not INCLUDE.search(code):
            bad.append(("HANDLISTED", rel, ""))
        for value in FLAT_VAR.findall(code):
            if _flat_outside_unit_dir(value):
                bad.append(("FLAT_SUBDIR", rel, value))
    return bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", type=pathlib.Path,
                    default=pathlib.Path(__file__).resolve().parents[1])
    args = ap.parse_args()
    bad = offenders(args.root)
    for kind, mk, value in bad:
        if kind == "HANDLISTED":
            print(f"HANDLISTED {mk}: builds a *_flat.v without make/formal_flat.mk")
        else:
            print(f"FLAT_SUBDIR {mk}: FLAT := {value} -- build the flat in the "
                  f"unit directory; a tool that owns a subdirectory can delete "
                  f"it before the proof reads it")
    handlisted = sum(1 for kind, _, _ in bad if kind == "HANDLISTED")
    subdir = len(bad) - handlisted
    print(f"formal flat sources: {handlisted} hand-listed, {subdir} outside "
          f"their unit directory")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
