#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Fail when a computed K-map's mirror has drifted from the RTL it claims.

The grids in pumice_signal_contracts.xlsx get their authority from criterion 1
of vault/handbook/design/signal-contracts-and-kmaps.md: cells are COMPUTED from
a python mirror of the RTL expression, never drawn. That guarantee is worth
exactly nothing if the mirror is a mirror of last month's RTL -- a cell computed
from the wrong equation looks identical to one computed from the right equation,
so the map is then worse than no map at all. On 2026-09-10 `rd_col_m`'s mirror
modelled 7 terms against the RTL's 13, and nothing noticed for three weeks.

The check: for every `km.kmap(...)` in the generator, take the documented
expression, find the same signal's assignment in the cited .sv, and require that
every RTL identifier on the right-hand side is NAMED somewhere in the documented
expression. Folding several RTL guards into one axis is fine and expected -- the
fold equation is written in the expression's [square brackets], so the names are
still there. Dropping a term is not fine, and that is what this catches.

    python3 docs/check_kmap_rtl_sync.py        # exit 1 on drift
"""
from __future__ import annotations
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
GEN = os.path.join(HERE, "gen_pumice_signal_contracts.py")
RTL_DIRS = [os.path.join(ROOT, "rtl", d) for d in ("fub", "macro", "top")]

# Identifiers that appear in an RHS but are not signals the map must model:
# SV literals/keywords, elaboration-time constants, helper functions, and the
# loop-local aliases the arbiter uses for "this entry's bank".
NOT_A_SIGNAL = {
    "RK0", "NUM_BANKS", "NUM_ENTRIES", "BANK_ACTIVATING", "BANK_ACTIVE",
    "BANK_PRECHARGING", "BANK_IDLE", "f_ap", "f_bank", "f_row", "f_col",
    "rb", "wb", "e", "i", "b", "ei", "begin", "end", "if", "else",
}
IDENT = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")


def _strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    return re.sub(r"//[^\n]*", "", text)


def _strip_literals(expr: str) -> str:
    """Sized SV literals are not identifiers. Without this, 4'd0 contributes a
    phantom term `d0` and the check cries drift on a correct mirror."""
    expr = re.sub(r"\b\d+\s*'\s*[sS]?[bodhBODH][0-9a-fA-FxXzZ_]+", " ", expr)
    return re.sub(r"'[01]\b", " ", expr)


def _rtl_sources() -> dict[str, str]:
    out = {}
    for d in RTL_DIRS:
        if not os.path.isdir(d):
            continue
        for fn in os.listdir(d):
            if fn.endswith(".sv"):
                out[fn] = _strip_comments(open(os.path.join(d, fn)).read())
    return out


def _rtl_rhs(body: str, lhs: str) -> str | None:
    """The most substantial assignment to `lhs` -- skipping the reset/default
    `= '0` forms that precede a loop body."""
    base = lhs.split("[")[0]
    best = None
    for m in re.finditer(rf"\b{re.escape(base)}\s*(?:\[[^\]]*\])?\s*(?:<?=)\s*(.*?);",
                         body, re.S):
        rhs = " ".join(m.group(1).split())
        if rhs in ("'0", "0", "1'b0", "1'b1", "'1"):
            continue
        if best is None or len(rhs) > len(best):
            best = rhs
    return best


def _kmap_calls(src: str):
    for m in re.finditer(r"km\.kmap\(\s*", src):
        i, depth, j = m.end(), 1, m.end()
        while depth:
            if src[j] == "(":
                depth += 1
            elif src[j] == ")":
                depth -= 1
            j += 1
        yield src[i:j - 1]


def main() -> int:
    gen = open(GEN).read()
    rtl = _rtl_sources()
    checked = skipped = bad = 0
    problems = []
    unresolved = []

    for call in _kmap_calls(gen):
        strings = re.findall(r'"((?:[^"\\]|\\.)*)"', call)
        if len(strings) < 3:
            continue
        name, source = strings[0], strings[1]
        # the documented expression is the first string containing '='
        expr = next((t for t in strings[2:] if "=" in t), None)
        if expr is None:
            skipped += 1
            continue
        # the mirror text is every string in the call (the expression is split
        # across adjacent literals, and the fold equations live there too)
        mirror_text = " ".join(strings)
        fm = re.search(r"([a-z0-9_]+\.sv)", source)
        lhs = expr.split("=")[0].strip()
        if not fm or fm.group(1) not in rtl or not lhs:
            skipped += 1
            continue
        # Resolution ladder: the documented LHS is written for a reader, so it
        # may drop a port's _o, or name the rd/wr pair generically (act_m for
        # rd_act_m and wr_act_m). Try the obvious spellings before giving up --
        # an unresolved name is a map this tool silently stops guarding.
        cands = [lhs, lhs + "_o", "rd_" + lhs, "w_" + lhs, "r_" + lhs]
        head = re.match(r"[A-Za-z_][A-Za-z0-9_]*", name)
        if head:
            cands += [head.group(0), head.group(0) + "_o"]
        rhs = None
        for cand in cands:
            rhs = _rtl_rhs(rtl[fm.group(1)], cand)
            if rhs is not None:
                lhs = cand
                break
        if rhs is None:
            skipped += 1
            unresolved.append((name, fm.group(1), lhs))
            continue
        checked += 1
        rtl_ids = {t for t in IDENT.findall(_strip_literals(rhs))
                   if t not in NOT_A_SIGNAL}
        named = set(IDENT.findall(mirror_text))
        missing = sorted(rtl_ids - named)
        if missing:
            bad += 1
            problems.append((name, fm.group(1), lhs, missing, rhs))

    for name, f, lhs, missing, rhs in problems:
        print(f"DRIFT  {name}")
        print(f"       {f} :: {lhs}")
        print(f"       RTL terms the mirror never names: {', '.join(missing)}")
        print(f"       RTL: {rhs[:200]}")
        print()
    for name, f, lhs in unresolved:
        print(f"UNCHECKED  {name[:56]}\n           ({f}: no assignment found "
              f"for {lhs!r}) -- this map is NOT guarded against drift")
    if unresolved:
        print()
    print(f"kmap mirrors checked: {checked}   drifted: {bad}   "
          f"not machine-checkable: {skipped}")
    if bad:
        print("\nA mirror that omits an RTL term computes its cells from the "
              "WRONG equation. Update the expression in "
              "gen_pumice_signal_contracts.py (fold extra guards into an axis "
              "and write the fold in [brackets] so the names are still there), "
              "then regenerate.")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
