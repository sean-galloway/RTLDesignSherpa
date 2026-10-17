# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Flatten a generated bridge's filelist into one deduplicated list.
#
# The -f graph overlaps by design (two wrappers each declare the helpers they
# need), so a raw `-f` handed to a simulator declares those modules twice
# (MODDUP). Inside the repo, bin/flatten_filelist.py and the make flows do
# this; an installed user has neither, so the package carries its own.

"""Resolve a .f tree to unique, absolute, order-preserving entries."""

from __future__ import annotations

import os
import re
from pathlib import Path
from typing import List

from bridge_pkg._paths import ip_root
from bridge_pkg.ip_closure import ROOT_VARS

_VAR = re.compile(r'\$\{?(\w+)\}?')


def flatten(filelist: Path) -> List[str]:
    """`+incdir+<abs>` lines first, then sources, each once, first wins."""
    root = ip_root()
    env = {k: str(root / v) if v else str(root) for k, v in ROOT_VARS.items()}
    incdirs: List[str] = []
    sources: List[str] = []
    seen_fl = set()

    def expand(token: str, base: Path) -> Path:
        def sub(m: re.Match) -> str:
            name = m.group(1)
            if name in env:
                return env[name]
            if name in os.environ:
                return os.environ[name]
            raise ValueError(f"{token}: ${name} is not a known root variable")
        p = Path(_VAR.sub(sub, token))
        return (p if p.is_absolute() else base / p).resolve()

    def walk(fl: Path) -> None:
        fl = fl.resolve()
        if fl in seen_fl:
            return
        seen_fl.add(fl)
        for raw in fl.read_text().splitlines():
            line = raw.split('//')[0].strip()
            if not line or line.startswith('#'):
                continue
            if line.startswith('-f '):
                walk(expand(line[3:].strip(), fl.parent))
            elif line.startswith('+incdir+'):
                d = str(expand(line[len('+incdir+'):], fl.parent))
                if d not in incdirs:
                    incdirs.append(d)
            elif line[0] in '+-':
                continue
            else:
                s = str(expand(line, fl.parent))
                if not Path(s).is_file():
                    raise FileNotFoundError(f"{fl}: {line} -> {s}")
                if s not in sources:
                    sources.append(s)

    walk(Path(filelist))
    return [f'+incdir+{d}' for d in incdirs] + sources
