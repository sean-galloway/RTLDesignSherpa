# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: bin/kmaps/citations.py
# Purpose: Build-time citation gate -- fail if the RTL moved under a quote
"""Citation registry check.

A workbook whose quotes have drifted from the RTL is worse than no workbook: it
reads as evidence while describing code that no longer exists. Every generator
runs this before writing, so a rerun after an RTL edit fails loudly instead of
publishing a stale map.

Parameterised on promotion (TOOLING-KMAP step 5): the per-component CITES list
and repo root are arguments, because those are the parts that are NOT shared.
"""

import os
import sys


def verify_citations(cites, repo):
    """cites: iterable of (repo-relative path, 1-based line, snippet).

    The snippet must appear ON that line -- a substring test, so a wrapped
    expression must be cited in halves rather than as one joined string.
    Exits non-zero on any drift; never returns a failure quietly.
    """
    bad = []
    for path, line, snippet in cites:
        full = os.path.join(repo, path)
        try:
            with open(full, "r") as f:
                lines = f.readlines()
        except OSError:
            bad.append(f"{path}: unreadable")
            continue
        if line > len(lines) or snippet not in lines[line - 1]:
            bad.append(f"{path}:{line}: expected {snippet!r}")
    if bad:
        print("CITATION DRIFT -- the RTL moved under the cited lines.",
              file=sys.stderr)
        for b in bad:
            print("  " + b, file=sys.stderr)
        sys.exit(1)
